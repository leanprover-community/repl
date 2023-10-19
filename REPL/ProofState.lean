/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Replay
import REPL.Util.Pickle

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

/-- New messages in a `ProofState`, relative to an optional previous `ProofState`. -/
def newMessages (new : ProofState) (old? : Option ProofState := none) : List Lean.Message :=
  match old? with
  | none => new.coreState.messages.msgs.toList
  | some old => new.coreState.messages.msgs.toList.drop (old.coreState.messages.msgs.size)

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

/--
Construct a `ProofState` from a `ContextInfo` and optional `LocalContext`, and a list of goals.

For convenience, we also allow a list of `Expr`s, and these are appended to the goals
as fresh metavariables with the given types.
-/
def create (ctx : ContextInfo) (lctx? : Option LocalContext)
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

open Lean.Meta in
/-- A copy of `Meta.Context` with closures omitted. -/
structure CompactableMetaContext where
  config            : Config               := {}
  lctx              : LocalContext         := {}
  localInstances    : LocalInstances       := #[]
  defEqCtx?         : Option DefEqContext  := none
  synthPendingDepth : Nat                  := 0
  -- canUnfold?        : Option (Config → ConstantInfo → CoreM Bool) := none

/-- A copy of `Term.Context` with closures and a cache omitted. -/
structure CompactableTermContext where
  declName? : Option Name := none
  auxDeclToFullName : FVarIdMap Name  := {}
  macroStack        : MacroStack      := []
  mayPostpone : Bool := true
  errToSorry : Bool := true
  autoBoundImplicit  : Bool            := false
  autoBoundImplicits : PArray Expr := {}
  -- autoBoundImplicitForbidden : Name → Bool := fun _ => false
  sectionVars        : NameMap Name    := {}
  sectionFVars       : NameMap Expr    := {}
  implicitLambda     : Bool            := true
  isNoncomputableSection : Bool        := false
  ignoreTCFailures : Bool := false
  inPattern        : Bool := false
  -- tacticCache?     : Option (IO.Ref Tactic.Cache) := none
  saveRecAppSyntax : Bool := true
  holesAsSyntheticOpaque : Bool := false

open Lean.Core in
/-- A copy of `Core.State` with the `Environment`, caches, and logging omitted. -/
structure CompactableCoreState where
  -- env             : Environment
  nextMacroScope  : MacroScope     := firstFrontendMacroScope + 1
  ngen            : NameGenerator  := {}
  -- traceState      : TraceState     := {}
  -- cache           : Core.Cache     := {}
  -- messages        : MessageLog     := {}
  -- infoState       : Elab.InfoState := {}

open System (FilePath)

/--
Pickle a `ProofState`, discarding closures and non-essential caches.

When pickling the `Environment`, we do so relative to its imports.
-/
def pickle (p : ProofState) (path : FilePath) : IO Unit := do
  let env := p.coreState.env
  let p' := { p with coreState := { p.coreState with env := ← mkEmptyEnvironment }}
  _root_.pickle path
    (env.header.imports,
     env.constants.map₂,
     ({ p'.coreState with } : CompactableCoreState),
     p'.coreContext,
     p'.metaState,
     ({ p'.metaContext with } : CompactableMetaContext),
     p'.termState,
     ({ p'.termContext with } : CompactableTermContext),
     p'.tacticState,
     p'.tacticContext)

/--
Unpickle a `ProofState`.
-/
def unpickle (path : FilePath) : IO (ProofState × CompactedRegion) := unsafe do
  let ((imports, map₂, coreState, coreContext, metaState, metaContext, termState, termContext,
    tacticState, tacticContext), region) ←
    _root_.unpickle (Array Import × PHashMap Name ConstantInfo × CompactableCoreState ×
      Core.Context × Meta.State × CompactableMetaContext × Term.State × CompactableTermContext ×
      Tactic.State × Tactic.Context) path
  let env ← (← importModules imports {} 0).replay (HashMap.ofList map₂.toList)
  let p' :=
  { coreState := { coreState with env }
    coreContext
    metaState
    metaContext := { metaContext with }
    termState
    termContext := { termContext with }
    tacticState
    tacticContext }
  return (p', region)

end ProofState
