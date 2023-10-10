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

/--
Bundled structure for the `State` and `Context` objects
for the `CoreM`, `MetaM`, `TermElabM`, and `TacticM` monads.
-/
structure ProofState where
  coreState     : Core.State
  coreContext   : Core.Context
  metaState     : Meta.State
  metaContext   : Meta.Context
  termState     : Term.State
  termContext   : Term.Context
  tacticState   : Tactic.State
  tacticContext : Tactic.Context
namespace ProofState

open Lean Elab Tactic

/-- Run a `CoreM` monadic function in the current `ProofState`, updating the `Core.State`. -/
def runCoreM (p : ProofState) (t : CoreM α) : IO (α × ProofState) := do
  let (a, coreState) ← (Lean.Core.CoreM.toIO · p.coreContext p.coreState) do t
  return (a, { p with coreState })

/-- Run a `MetaM` monadic function in the current `ProofState`, updating the `Meta.State`. -/
def runMetaM (p : ProofState) (t : MetaM α) : IO (α × ProofState) := do
  let ((a, metaState), p') ← p.runCoreM (Lean.Meta.MetaM.run (ctx := p.metaContext) (s := p.metaState) do t)
  return (a, { p' with metaState })

/-- Run a `TermElabM` monadic function in the current `ProofState`, updating the `Term.State`. -/
def runTermElabM (p : ProofState) (t : TermElabM α) : IO (α × ProofState) := do
  let ((a, termState), p') ← p.runMetaM (Lean.Elab.Term.TermElabM.run (s := p.termState) do t)
  return (a, { p' with termState })

/-- Run a `TacticM` monadic function in the current `ProofState`, updating the `Tactic.State`. -/
def runTacticM (p : ProofState) (t : TacticM α) : IO (α × ProofState) := do
  let ((a, tacticState), p') ← p.runTermElabM (t p.tacticContext |>.run p.tacticState)
  return (a, { p' with tacticState })

/--
Run a `TacticM` monadic function in the current `ProofState`, updating the `Tactic.State`,
and discarding the return value.
-/
def runTacticM' (p : ProofState) (t : TacticM α) : IO ProofState :=
  Prod.snd <$> p.runTacticM t

/--
Evaluate a `Syntax` into a `TacticM` tactic, and run it in the current `ProofState`.
-/
def runSyntax (p : ProofState) (t : Syntax) : IO ProofState :=
  Prod.snd <$> p.runTacticM (evalTactic t)

/--
Parse a string into a `Syntax`, evaluate it as a `TacticM` tactic,
and run it in the current `ProofState`.
-/
def runString (p : ProofState) (t : String) : IO ProofState :=
  match Parser.runParserCategory p.coreState.env `tactic t with
  | .error e => throw (IO.userError e)
  | .ok stx => p.runSyntax stx

/-- Pretty print the current goals in the `ProofState`. -/
def ppGoals (p : ProofState) : IO (List Format) :=
  Prod.fst <$> p.runTacticM do (← getGoals).mapM (Meta.ppGoal ·)

end ProofState

/-- The monadic state for the Lean REPL. -/
structure State where
  /--
  Environment snapshots after complete declarations.
  The user can run a declaration in a given environment using `{"cmd": "def f := 37", "env": 17}`.
  -/
  environments : Array Environment := #[]
  /--
  Proof states after individual tactics.
  The user can run a tactic in a given proof state using `{"tactic": "exact 42", "proofState": 5}`.
  Declarations with containing `sorry` record a proof state at each sorry,
  and report the numerical index for the recorded state at each sorry.
  -/
  proofStates : Array ProofState := #[]

/--
The Lean REPL monad.

We only use this with `m := IO`, but it is set up as a monad transformer for flexibility.
-/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

/-- Record an `Environment` into the REPL state, returning its index for future use. -/
def recordEnvironment (env : Environment) : M m Nat := do
  let id := (← get).environments.size
  modify fun s => { s with environments := s.environments.push env }
  return id

/-- Record a `ProofState` into the REPL state, returning its index for future use. -/
def recordProofState (proofState : ProofState) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

/--
Construct a `ProofState` from a `ContextInfo` and optional `LocalContext`, and a list of goals.

For convenience, we also allow a list of `Expr`s, and these are appended to the goals
as fresh metavariables with the given types.
-/
def createProofState (ctx : ContextInfo) (lctx? : Option LocalContext)
    (goals : List MVarId) (types : List Expr := []) : IO ProofState := do
  ctx.runMetaM (lctx?.getD {}) do
    let goals := goals ++ (← types.mapM fun t => Expr.mvarId! <$> Meta.mkFreshExprMVar (some t))
    pure <|
    { coreState := ← getThe Core.State
      coreContext := ← readThe Core.Context
      metaState := ← getThe Meta.State
      metaContext := ← readThe Meta.Context
      termState := {}
      termContext := {}
      tacticState := { goals }
      tacticContext := { elaborator := .anonymous } }

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M m (CommandResponse ⊕ Error) := do
  let (env?, notFound) ← do match s.env with
  | none => pure (none, false)
  | some i => do match (← get).environments[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
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
  let id ← recordEnvironment env
  return .inl ⟨id, messages, sorries⟩

/--
Run a single tactic, returning the id of the new proof statement, and the new goals.
-/
-- TODO return messages?
-- TODO detect sorries?
def runProofStep (s : ProofStep) : M m (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[s.proofState]? with
  | none => return .inr ⟨"Unknown proof state."⟩
  | some proofState =>
    let proofState' ← proofState.runString s.tactic
    let id ← recordProofState proofState'
    return .inl { proofState := id, goals := (← proofState'.ppGoals).map fun s => s!"{s}" }

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
