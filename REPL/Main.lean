/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.JSON
import REPL.Frontend
import REPL.InfoTree
import REPL.Util.Path
import REPL.Util.TermUnsafe
import REPL.Lean.ContextInfo
import REPL.InfoTree

/-!
# A REPL for Lean.

Communicates via JSON on stdin and stdout. Commands should be separated by blank lines.

Commands may be of the form
```
{ "cmd" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```
or
```
{ "cmd" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form
```
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "\n⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
 ```
 showing any messages generated, or sorries with their goal states.
 Information is generated for tactic mode sorries, but not for term mode sorries.
-/

open Lean Elab

namespace REPL

-- #print Tactic.State -- goals: List MVarId
-- #print Tactic.Context
-- #print Term.State -- pendingMVars, syntheticMVars
-- #print Term.Context
-- #print Meta.State -- MetavarContext
-- #print Meta.Context -- LocalContext, ...
-- #print Core.State -- Environment, MessageLog, Elab.InfoState, ...
-- #print Core.Context

structure ProofState where
  tacticSavedState : Tactic.SavedState
  tacticContext : Tactic.Context
  termContext : Term.Context
  metaContext : Meta.Context
  coreContext : Core.Context

namespace ProofState

open Lean Elab Tactic

def tacticState (p : ProofState) : Tactic.State := p.tacticSavedState.tactic
def termState (p : ProofState) : Term.State := p.tacticSavedState.term.elab
def metaState (p : ProofState) : Meta.State := p.tacticSavedState.term.meta.meta
def coreState (p : ProofState) : Core.State := p.tacticSavedState.term.meta.core

def withCoreState (p : ProofState) (core : Core.State) : ProofState :=
  { p with
    tacticSavedState :=
    { p.tacticSavedState with
      term :=
      { p.tacticSavedState.term with
        meta :=
        { p.tacticSavedState.term.meta with
          core }}}}

def withMetaState (p : ProofState) (meta : Meta.State) : ProofState :=
  { p with
    tacticSavedState :=
    { p.tacticSavedState with
      term :=
      { p.tacticSavedState.term with
        meta :=
        { p.tacticSavedState.term.meta with
          meta }}}}

def withTermState (p : ProofState) («elab» : Term.State) : ProofState :=
  { p with
    tacticSavedState :=
    { p.tacticSavedState with
      term :=
      { p.tacticSavedState.term with
        «elab» }}}

def withTacticState (p : ProofState) (tactic : Tactic.State) : ProofState :=
  { p with
    tacticSavedState :=
    { p.tacticSavedState with
      tactic }}

def runCoreM (p : ProofState) (t : CoreM α) : IO (α × ProofState) := do
  -- let ctx : Core.Context := { fileName := "", options := {}, fileMap := default }
  -- let state : Core.State := { env := p.env }
  let (a, state') ← (Lean.Core.CoreM.toIO · p.coreContext p.coreState) do t
  return (a, p.withCoreState state')

def runMetaM (p : ProofState) (t : MetaM α) : IO (α × ProofState) := do
  -- let ctx : Meta.Context := { lctx := p.lctx }
  -- let state : Meta.State := { mctx := p.mctx }
  let ((a, state'), p') ← p.runCoreM (Lean.Meta.MetaM.run (ctx := p.metaContext) (s := p.metaState) do t)
  return (a, p'.withMetaState state')

def runTermElabM (p : ProofState) (t : TermElabM α) : IO (α × ProofState) := do
  let ((a, state'), p') ← p.runMetaM (Lean.Elab.Term.TermElabM.run (s := p.termState) do t)
  return (a, p'.withTermState state')

def runTacticM (p : ProofState) (t : TacticM α) : IO (α × ProofState) := do
  -- let ctx : Tactic.Context := { elaborator := .anonymous }
  -- let state : Tactic.State := { goals := p.goals }
  let ((a, state'), p') ← p.runTermElabM (t p.tacticContext |>.run p.tacticState)
  return (a, p'.withTacticState state')

def runTacticM' (p : ProofState) (t : TacticM α) : IO ProofState :=
  Prod.snd <$> p.runTacticM t

def runSyntax (p : ProofState) (t : Syntax) : IO ProofState :=
  Prod.snd <$> p.runTacticM (evalTactic t)

def runString (p : ProofState) (t : String) : IO ProofState :=
  match Parser.runParserCategory p.coreState.env `tactic t with
  | .error e => throw (IO.userError e)
  | .ok stx => p.runSyntax stx

def ppGoals (p : ProofState) : IO (List Format) :=
  Prod.fst <$> p.runTacticM do (← getGoals).mapM (Meta.ppGoal ·)

end ProofState

/-- The monadic state for the Lean REPL. -/
structure State where
  environments : Array Environment := #[]
  proofStates : Array ProofState := #[]
  lines : Array Nat := #[]

/-- The Lean REPL monad. -/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

def recordEnvironment (env : Environment) : M m Nat := do
  let id := (← get).environments.size
  modify fun s => { s with environments := s.environments.push env }
  return id

def recordLines (lines : Nat) : M m Unit :=
  modify fun s => { s with lines := s.lines.push lines }

def recordProofState (proofState : ProofState) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

def createProofState (ctx : ContextInfo) (lctx? : Option LocalContext)
    (goals : List MVarId) (types : List Expr := []) : IO ProofState := do
  ctx.runMetaM (lctx?.getD {}) do
    let goals := goals ++ (← types.mapM fun t => Expr.mvarId! <$> Meta.mkFreshExprMVar (some t))
    pure <|
    { coreContext := ← readThe Core.Context
      metaContext := ← readThe Meta.Context
      termContext := {}
      tacticContext := { elaborator := .anonymous }
      tacticSavedState :=
      { tactic := { goals }
        term :=
        { «elab» := {},
          meta :=
          { meta := ← getThe Meta.State
            core := ← getThe Core.State } } } }

/-- Run a command, returning the id of the new environment, and any messages and sorries. -/
def runCommand (s : Command) : M m CommandResponse := do
  let env? := s.env.bind ((← get).environments[·]?)
  let (env, messages, trees) ← IO.processInput s.cmd env? {} ""
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← trees.bind InfoTree.sorries |>.mapM
    fun ⟨ctx, g, pos, endPos⟩ => do
      let (goal, proofState) ← match g with
      | .tactic g => do
         pure (s!"{(← ctx.ppGoals [g])}".trim, some (← createProofState ctx none [g]))
      | .term lctx (some t) => do
         pure (s!"⊢ {← ctx.ppExpr lctx t}", some (← createProofState ctx lctx [] [t]))
      | .term _ none => unreachable!
      let proofStateId ← proofState.mapM recordProofState
      return Sorry.of goal pos endPos proofStateId
  recordLines <| s.cmd.splitOn "\n" |>.length
  let id ← recordEnvironment env
  pure ⟨id, messages, sorries⟩

def runProofStep (s : ProofStep) : M m (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[s.proofState]? with
  | none => return Sum.inr ⟨"Unknown proof state."⟩
  | some proofState =>
    let proofState' ← proofState.runString s.tactic
    let id ← recordProofState proofState'
    return Sum.inl { proofState := id, goals := (← proofState'.ppGoals).map fun s => s!"{s}" }

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
partial def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

instance [ToJson α] [ToJson β] : ToJson (α ⊕ β) where
  toJson x := match x with
  | .inl a => toJson a
  | .inr b => toJson b

/-- Read-eval-print loop for Lean. -/
partial def repl : IO Unit :=
  StateT.run' loop {}
where loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return ()
  let json := Json.parse query
  match json with
  | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  | .ok j => match fromJson? j with
    | .ok (r : REPL.ProofStep) => IO.println <| toString <| toJson (← runProofStep r)
    | .error _ => match fromJson? j with
      | .ok (r : REPL.Command) => IO.println <| toString <| toJson (← runCommand r)
      | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  loop

/-- Main executable function, run as `lake exe repl`. -/
def main (_ : List String) : IO Unit := do
  searchPathRef.set compile_time_search_path%
  repl
