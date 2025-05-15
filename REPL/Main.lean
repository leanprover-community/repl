/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.JSON
import REPL.Frontend
import REPL.Util.Path
import REPL.Lean.ContextInfo
import REPL.Lean.Environment
import REPL.Lean.InfoTree
import REPL.Lean.InfoTree.ToJson
import REPL.Snapshots
import REPL.PaperProof.BetterParser

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

/-- The monadic state for the Lean REPL. -/
structure State where
  /--
  Environment snapshots after complete declarations.
  The user can run a declaration in a given environment using `{"cmd": "def f := 37", "env": 17}`.
  -/
  cmdStates : Array CommandSnapshot := #[]
  /--
  Proof states after individual tactics.
  The user can run a tactic in a given proof state using `{"tactic": "exact 42", "proofState": 5}`.
  Declarations with containing `sorry` record a proof state at each sorry,
  and report the numerical index for the recorded state at each sorry.
  -/
  proofStates : Array ProofSnapshot := #[]

/--
The Lean REPL monad.

We only use this with `m := IO`, but it is set up as a monad transformer for flexibility.
-/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

/-- Record an `CommandSnapshot` into the REPL state, returning its index for future use. -/
def recordCommandSnapshot (state : CommandSnapshot) : M m Nat := do
  let id := (← get).cmdStates.size
  modify fun s => { s with cmdStates := s.cmdStates.push state }
  return id

/-- Record a `ProofSnapshot` into the REPL state, returning its index for future use. -/
def recordProofSnapshot (proofState : ProofSnapshot) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

/-- Delete all command snapshots with index >= id. -/
def deleteCommandSnapshotsAfter (id : Nat) : M m Unit := do
  modify fun s => { s with cmdStates := s.cmdStates.shrink id }

/-- Delete all proof snapshots with index >= id. -/
def deleteProofSnapshotsAfter (id : Nat) : M m Unit := do
  modify fun s => { s with proofStates := s.proofStates.shrink id }

def sorries (trees : List InfoTree) (env? : Option Environment) (rootGoals? : Option (List MVarId))
: M m (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, proofState) ← match g with
        | .tactic g => do
          let lctx ← ctx.runMetaM {} do
              match ctx.mctx.findDecl? g with
              | some decl => return decl.lctx
              | none => throwError "unknown metavariable '{g}'"
          let s ← ProofSnapshot.create ctx lctx env? [g] rootGoals?
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
          let s ← ProofSnapshot.create ctx lctx env? [] rootGoals? [t]
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        let proofStateId ← proofState.mapM recordProofSnapshot
        let goalInfo : Option GoalInfo ← match proofState with
        | some proofState => do
           match proofState.tacticState.goals[0]? with
           | some goalId => do
             -- TODO: this does not work when it's just `sorry` instead of `by sorry` - allow printGoalInfo to return none
             let info ← printGoalInfo ctx goalId
             pure (some info)
           | none => pure none
        | none => pure none
        return Sorry.of goal goalInfo pos endPos proofStateId

def ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def tactics (trees : List InfoTree) (env? : Option Environment) : M m (List Tactic) :=
  trees.flatMap InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, rootGoals, goals, pos, endPos, ns⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none env? goals rootGoals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Tactic.of goals tactic pos endPos proofStateId ns

def proofTrees (infoTrees : List InfoTree) : M m (List (List ProofStepInfo)) := do
  infoTrees.mapM fun infoTree => do
    let proofTree ← PaperProof.BetterParser infoTree
    match proofTree with
    | .some proofTree => return proofTree.steps
    | .none => return []

def collectRootGoalsAsSorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) := do
  trees.flatMap InfoTree.rootGoals |>.mapM
    fun ⟨ctx, goals, pos⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none env? goals goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Sorry.of goals none pos pos proofStateId


private def collectFVarsAux : Expr → NameSet
  | .fvar fvarId => NameSet.empty.insert fvarId.name
  | .app fm arg => (collectFVarsAux fm).union $ collectFVarsAux arg
  | .lam _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .forallE _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .letE _ type value body _ => ((collectFVarsAux type).union $ collectFVarsAux value).union $ collectFVarsAux body
  | .mdata _ expr => collectFVarsAux expr
  | .proj _ _ struct => collectFVarsAux struct
  | _ => NameSet.empty

/-- Collect all fvars in the expression, and return their names. -/
private def collectFVars (e : Expr) : MetaM (Array Expr) := do
  let names := collectFVarsAux e
  let mut fvars := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    if names.contains ldecl.fvarId.name then
      fvars := fvars.push $ .fvar ldecl.fvarId
  return fvars


private def abstractAllLambdaFVars (e : Expr) : MetaM Expr := do
  let mut e' := e
  while e'.hasFVar do
    let fvars ← collectFVars e'
    if fvars.isEmpty then
      break
    e' ← Meta.mkLambdaFVars fvars e'
  return e'

/--
Evaluates the current status of a proof, returning a string description.
Main states include:
- "Completed": Proof is complete and type checks successfully
- "Incomplete": When goals remain, or proof contains sorry/metavariables
- "Error": When kernel type checking errors occur

Inspired by LeanDojo REPL's status tracking.
-/
def getProofStatus (proofState : ProofSnapshot) : M m String := do
  match proofState.tacticState.goals with
    | [] =>
      let res := proofState.runMetaM do
        match proofState.rootGoals with
        | [goalId] =>
          match proofState.metaState.mctx.getExprAssignmentCore? goalId with
          | none => return "Error: Goal not assigned"
          | some pf => do
            let pf ← instantiateMVars pf

            -- First check that the proof has the expected type
            let pft ← Meta.inferType pf >>= instantiateMVars
            let expectedType ← Meta.inferType (mkMVar goalId) >>= instantiateMVars
            unless (← Meta.isDefEq pft expectedType) do
              return s!"Error: proof has type {pft} but root goal has type {expectedType}"

            let pf ← goalId.withContext $ abstractAllLambdaFVars pf
            let pft ← Meta.inferType pf >>= instantiateMVars

            if pf.hasExprMVar then
              return "Incomplete: contains metavariable(s)"

            -- Find all level parameters
            let usedLevels := collectLevelParams {} pft
            let usedLevels := collectLevelParams usedLevels pf

            let decl := Declaration.defnDecl {
              name := Name.anonymous,
              type := pft,
              value := pf,
              levelParams := usedLevels.params.toList,
              hints := ReducibilityHints.opaque,
              safety := DefinitionSafety.safe
            }

            try
              let _ ← addDecl decl
            catch ex =>
              return s!"Error: kernel type check failed: {← ex.toMessageData.toString}"

            if pf.hasSorry then
              return "Incomplete: contains sorry"
            return "Completed"

        | _ => return "Not verified: more than one initial goal"
      return (← res).fst

    | _ => return "Incomplete: open goals remain"

def replaceWithPrint (f? : Expr → MetaM (Option Expr)) (e : Expr) : MetaM Expr := do
  IO.println s!"Processing expression: {e}"
  match ← f? e with
  | some eNew => do
    IO.println s!"Replaced with: {eNew}"
    return eNew
  | none      => match e with
    | .forallE _ d b _ => let d ← replaceWithPrint f? d; let b ← replaceWithPrint f? b; return e.updateForallE! d b
    | .lam _ d b _     => let d ← replaceWithPrint f? d; let b ← replaceWithPrint f? b; return e.updateLambdaE! d b
    | .mdata _ b       => let b ← replaceWithPrint f? b; return e.updateMData! b
    | .letE _ t v b _  => let t ← replaceWithPrint f? t; let v ← replaceWithPrint f? v; let b ← replaceWithPrint f? b; return e.updateLet! t v b
    | .app f a         => let f ← replaceWithPrint f? f; let a ← replaceWithPrint f? a; return e.updateApp! f a
    | .proj _ _ b      => let b ← replaceWithPrint f? b; return e.updateProj! b
    | e                => return e

def replaceMVarsWithSorry (e : Expr) : MetaM Expr := do
  match e with
  | .mvar _ => do
    let mvarType ← Meta.inferType e
    let sorryTerm ← Meta.mkSorry mvarType false
    return sorryTerm
  | .forallE _ d b _ => let d ← replaceMVarsWithSorry d; let b ← replaceMVarsWithSorry b; return e.updateForallE! d b
  | .lam _ d b _     => let d ← replaceMVarsWithSorry d; let b ← replaceMVarsWithSorry b; return e.updateLambdaE! d b
  | .mdata _ b       => let b ← replaceMVarsWithSorry b; return e.updateMData! b
  | .letE _ t v b _  => let t ← replaceMVarsWithSorry t; let v ← replaceMVarsWithSorry v; let b ← replaceMVarsWithSorry b; return e.updateLet! t v b
  | .app f a         => let f ← replaceMVarsWithSorry f; let a ← replaceMVarsWithSorry a; return e.updateApp! f a
  | .proj _ _ b      => let b ← replaceMVarsWithSorry b; return e.updateProj! b
  | e                => return e

def replaceMVarsWithSorryPrint (e : Expr) : MetaM Expr := do
  let mkSorryForMVar (e : Expr) : MetaM (Option Expr) := do
    if e.isMVar then
      let mvarType ← Meta.inferType e
      let sorryTerm ← Meta.mkSorry mvarType false
      return some sorryTerm
    else
      return none
  replaceWithPrint mkSorryForMVar e


/--
  Given a metavar‐context `mctx` and a metavariable `mvarId`,
  first lookup its "core" assignment or delayed assignment,
  then recursively replace any immediate `?m` occurrences in that Expr
  by their own core/delayed assignments.
  Returns `none` if no assignment of either kind is found.
-/
partial def getFullAssignment (mctx : MetavarContext) (mvarId : MVarId) : Option Expr :=
  goMVar mvarId
  where
    -- goExpr: traverse an Expr, inlining any mvars via goMVar
    goExpr (e : Expr) : Expr :=
      match e with
      | .mvar mid =>
        match goMVar mid with
        | some e' => e'
        | none    => e
      | .forallE nm ty bd bi  => .forallE nm (goExpr ty) (goExpr bd) bi
      | .lam      nm ty bd bi => .lam      nm (goExpr ty) (goExpr bd) bi
      | .app      f a         => .app      (goExpr f) (goExpr a)
      | .letE     nm ty v bd bi => .letE nm (goExpr ty) (goExpr v) (goExpr bd) bi
      | .mdata    md b        => .mdata    md (goExpr b)
      | .proj     s i b       => .proj     s i (goExpr b)
      | other                => other
    goMVar (mid : MVarId) : Option Expr :=
      match mctx.getExprAssignmentCore? mid with
      | some e => some (goExpr e)
      | none   =>
        match mctx.getDelayedMVarAssignmentCore? mid with
        | some da => goMVar da.mvarIdPending
        | none    => none

/--
  Given a metavar‐context `mctx` and a metavariable `mvarId`,
  follow its core or delayed assignments recursively,
  and collect the names of all metavariables reachable.
  Returns a `NameSet` of metavariable names.
-/
partial def getFullMvars (mctx : MetavarContext) (mvarId : MVarId) : NameSet :=
  goMVar mvarId NameSet.empty
where
  /-- Handle a metavariable: inline its assignment if any, otherwise record it. -/
  goMVar (mid : MVarId) (acc : NameSet) : NameSet :=
    match mctx.getExprAssignmentCore? mid with
    | some e  => goExpr e acc
    | none    =>
      match mctx.getDelayedMVarAssignmentCore? mid with
      | some da => goMVar da.mvarIdPending acc
      | none    => acc.insert mid.name

  /-- Traverse an `Expr`, collecting any metavars it contains. -/
  goExpr : Expr → NameSet → NameSet
  | Expr.mvar mid,          acc => goMVar mid acc
  | Expr.app f a,           acc => goExpr a (goExpr f acc)
  | Expr.lam _ ty body _,   acc => goExpr body (goExpr ty acc)
  | Expr.forallE _ ty bd _, acc => goExpr bd (goExpr ty acc)
  | Expr.letE _ ty val bd _,acc => goExpr bd (goExpr val (goExpr ty acc))
  | Expr.mdata _ b,         acc => goExpr b acc
  | Expr.proj _ _ b,        acc => goExpr b acc
  | _,                      acc => acc


partial def getFullAssignmentIO (mctx : MetavarContext) (mvarId : MVarId) : IO (Option Expr) :=
  goMVar mvarId
where
  /-- Traverse an Expr, inlining any mvars via goMVar, but first print it. -/
  goExpr (e : Expr) : IO Expr := do
    IO.println s!"[goExpr] ▶ {e}"
    match e with
    | .mvar mid =>
      -- try to inline that mvar
      match (← goMVar mid) with
      | some e' => pure e'
      | none    => pure e
    | .forallE nm ty bd bi  =>
      pure $ .forallE nm (← goExpr ty) (← goExpr bd) bi
    | .lam      nm ty bd bi =>
      pure $ .lam      nm (← goExpr ty) (← goExpr bd) bi
    | .app      f a         =>
      pure $ .app      (← goExpr f) (← goExpr a)
    | .letE     nm ty v bd bi =>
      pure $ .letE nm (← goExpr ty) (← goExpr v) (← goExpr bd) bi
    | .mdata    md b        =>
      pure $ .mdata    md (← goExpr b)
    | .proj     s i b       =>
      pure $ .proj     s i (← goExpr b)
    | other                =>
      pure other

  /-- Lookup the “core” or delayed assignment of a mvar, printing the mvar first. -/
  goMVar (mid : MVarId) : IO (Option Expr) := do
    IO.println s!"[goMVar] ▶ {mid.name}"
    match mctx.getExprAssignmentCore? mid with
    | some e =>
      -- directly assigned: inline and return
      some <$> goExpr e
    | none   =>
      match mctx.getDelayedMVarAssignmentCore? mid with
      | some da =>
        -- there’s a pending delayed assignment
        goMVar da.mvarIdPending
      | none    =>
        -- not assigned at all
        pure none

partial def getFullAssignmentLambda (mctx : MetavarContext) (mvarId : MVarId) : MetaM (Option Expr) :=
  goMVar mvarId
  where
    goExpr (e : Expr) : MetaM Expr := do
      match e with
      | .mvar mid =>
        match (← goMVar mid) with
        | some e' => pure e'
        | none    => pure e
      | .forallE nm ty bd bi  =>
        pure $ .forallE nm (← goExpr ty) (← goExpr bd) bi
      | .lam      nm ty bd bi =>
        pure $ .lam      nm (← goExpr ty) (← goExpr bd) bi
      | .app      f a         =>
        pure $ .app      (← goExpr f) (← goExpr a)
      | .letE     nm ty v bd bi =>
        pure $ .letE nm (← goExpr ty) (← goExpr v) (← goExpr bd) bi
      | .mdata    md b        =>
        pure $ .mdata    md (← goExpr b)
      | .proj     s i b       =>
        pure $ .proj     s i (← goExpr b)
      | other                =>
        pure other
    goMVar (mid : MVarId) : MetaM (Option Expr) := do
      match mctx.getExprAssignmentCore? mid with
      | some e => pure $ some (← goExpr e)
      | none   =>
        match mctx.getDelayedMVarAssignmentCore? mid with
        | some da => do
          let e' ← goMVar da.mvarIdPending
          match e' with
          | some e' =>
            let e'' ← Meta.mkLambdaFVars da.fvars e'
            return some e''
          | none => return none
        | none    => pure none

/-- Does the expression `e` contain the metavariable `t`? -/
private def findInExpr (t : MVarId) : Expr → Bool
  | Expr.mvar mid          => mid == t
  | Expr.app f a           => findInExpr t f || findInExpr t a
  | Expr.lam _ ty bd _     => findInExpr t ty || findInExpr t bd
  | Expr.forallE _ ty bd _ => findInExpr t ty || findInExpr t bd
  | Expr.letE _ ty val bd _=> findInExpr t ty || findInExpr t val || findInExpr t bd
  | Expr.proj _ _ e        => findInExpr t e
  | Expr.mdata _ e         => findInExpr t e
  | _                      => false

def checkAssignment (proofState : ProofSnapshot) (oldGoal : MVarId) (pf : Expr) : MetaM String := do
  let occursCheck ← Lean.occursCheck oldGoal pf
  if !occursCheck then
    return s!"Error: Goal {oldGoal.name} assignment is circular"

  -- Check that all MVars in the proof are goals in new state
  let mvars ← Meta.getMVars pf

  -- Loop through all unassigned metavariables recursively (note that delayed assigned ones are included).
  for mvar in mvars do
    let delayedAssigned ← mvar.isDelayedAssigned
    -- We only care about the leaf metavariables, so we skip delayed assigned ones.
    if delayedAssigned then
      continue

    -- If the metavariable in the assignment is a new goal, it's fine.
    if proofState.tacticState.goals.contains mvar then
      continue

    return s!"Error: Goal {oldGoal.name} assignment contains unassigned metavariables"

  return "OK"

/--
Verifies that all goals from the old state are properly handled in the new state.
Returns either "OK" or an error message describing the first failing goal.
-/
def verifyGoalAssignment (proofState : ProofSnapshot) (oldProofState? : Option ProofSnapshot := none) :
    M m String := do
  match oldProofState? with
  | none       => return "OK"  -- Nothing to verify
  | some oldSt => do
    let mut errorMsg := ""
    for oldGoal in oldSt.tacticState.goals do
      -- skip goals that are still open
      if proofState.tacticState.goals.contains oldGoal then
        continue

      -- run checks and build closed declaration inside the goal's local context
      let (res, _) ← proofState.runMetaM do
        -- switch to the local context of the goal
        oldGoal.withContext do
        match ← getExprMVarAssignment? oldGoal with
        | none       => return s!"Error: Goal {oldGoal.name} was not solved"
        | some pfRaw => do
          let pf ← instantiateMVars pfRaw
          -- First check that the proof has the expected type
          let pft ← Meta.inferType pf >>= instantiateMVars
          let expectedType ← Meta.inferType (mkMVar oldGoal) >>= instantiateMVars
          unless (← Meta.isDefEq pft expectedType) do
            return s!"Error: step assignment has type {pft} but goal has type {expectedType}"

          let chk ← checkAssignment proofState oldGoal pf
          if chk != "OK" then return chk

          let pf ← instantiateMVars pfRaw
          let pf ← replaceMVarsWithSorry pf
          try
            _ ← Lean.Meta.check pf
            return "OK"
          catch ex =>
            return s!"Error: kernel type check failed: {← ex.toMessageData.toString}"

          -- let pf ← instantiateMVars pfRaw
          -- let pf ← abstractAllLambdaFVars pf
          -- let pf ← instantiateMVars pf
          -- -- let pf ← abstractAllLambdaFVars pf
          -- let pf ← replaceMVarsWithSorry pf
          -- -- let pf ← abstractAllLambdaFVars pf

          -- -- infer its type (it already includes the same Pi over locals)
          -- let pftRaw ← Meta.inferType pf
          -- let pftClosed ← instantiateMVars pftRaw

          -- -- collect universe levels
          -- let usedLvls :=
          --   let l1 := collectLevelParams {} pftClosed
          --   collectLevelParams l1 pf

          -- IO.println s!"pf: {pf}"
          -- IO.println s!"pftClosed: {pftClosed}"
          -- -- IO.println s!"usedLvls: {usedLvls.params.toList}"

          -- -- -- build the declaration
          -- let freshName ← mkFreshId
          -- let decl := Declaration.defnDecl {
          --   name        := freshName,
          --   type        := pftClosed,
          --   value       := pf,
          --   levelParams := usedLvls.params.toList,
          --   hints       := ReducibilityHints.opaque,
          --   safety      := DefinitionSafety.safe
          -- }

          -- -- add and check
          -- try
          --   -- TODO: isn't this memory leak
          --   let _ ← addDecl decl
          --   return "OK"
          -- catch ex =>
          --   return s!"Error: kernel type check failed: {← ex.toMessageData.toString}"

      if res != "OK" then
        errorMsg := res
        break

    return if errorMsg == "" then "OK" else errorMsg

/-- Record a `ProofSnapshot` and generate a JSON response for it. -/
def createProofStepReponse (proofState : ProofSnapshot) (old? : Option ProofSnapshot := none) :
    M m ProofStepResponse := do
  let messages := proofState.newMessages old?
  let messages ← messages.mapM fun m => Message.of m
  let traces ← proofState.newTraces old?
  let trees := proofState.newInfoTrees old?
  let trees ← match old? with
  | some old => do
    let (ctx, _) ← old.runMetaM do return { ← CommandContextInfo.save with }
    let ctx := PartialContextInfo.commandCtx ctx
    pure <| trees.map fun t => InfoTree.context ctx t
  | none => pure trees
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees none (some proofState.rootGoals)
  let proofStateId ← recordProofSnapshot proofState
  let (ctx, _) ← proofState.runMetaM do return { ← CommandContextInfo.save with }
  let goalInfos ← proofState.tacticState.goals.mapM (fun mvarId => do
    let goalInfo ← printGoalInfo ctx mvarId
    return goalInfo)
  let mctxAfterJson ← MetavarContext.toJson proofState.metaState.mctx ctx
  return {
    proofState := proofStateId
    goals := (← proofState.ppGoals).map fun s => s!"{s}"
    messages
    sorries
    traces
    goalInfos
    mctxAfter := mctxAfterJson
    -- proofStatus := (← getProofStatus proofState)
    proofStatus := "N/A"
    stepVerification := (← verifyGoalAssignment proofState old?)
    -- stepVerification := "N/A"
  }

/-- Pickle a `CommandSnapshot`, generating a JSON response. -/
def pickleCommandSnapshot (n : PickleEnvironment) : M m (CommandResponse ⊕ Error) := do
  match (← get).cmdStates[n.env]? with
  | none => return .inr ⟨"Unknown environment."⟩
  | some env =>
    discard <| env.pickle n.pickleTo
    return .inl { env := n.env }

/-- Unpickle a `CommandSnapshot`, generating a JSON response. -/
def unpickleCommandSnapshot (n : UnpickleEnvironment) : M IO CommandResponse := do
  let (env, _) ← CommandSnapshot.unpickle n.unpickleEnvFrom
  let env ← recordCommandSnapshot env
  return { env }

/-- Pickle a `ProofSnapshot`, generating a JSON response. -/
-- This generates a new identifier, which perhaps is not what we want?
def pickleProofSnapshot (n : PickleProofState) : M m (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[n.proofState]? with
  | none => return .inr ⟨"Unknown proof State."⟩
  | some proofState =>
    discard <| proofState.pickle n.pickleTo
    return .inl (← createProofStepReponse proofState)

/-- Unpickle a `ProofSnapshot`, generating a JSON response. -/
def unpickleProofSnapshot (n : UnpickleProofState) : M IO (ProofStepResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match n.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let (proofState, _) ← ProofSnapshot.unpickle n.unpickleProofStateFrom cmdSnapshot?
  Sum.inl <$> createProofStepReponse proofState

def pruneSnapshots (n : PruneSnapshots) : M m String := do
  match n.cmdFromId with
  | some id => deleteCommandSnapshotsAfter id
  | none => pure ()
  match n.proofFromId with
  | some id => deleteProofSnapshotsAfter id
  | none => pure ()
  return "OK"

partial def removeChildren (t : InfoTree) : InfoTree :=
  match t with
  | InfoTree.context ctx t' => InfoTree.context ctx (removeChildren t')
  | InfoTree.node i _ => InfoTree.node i PersistentArray.empty
  | InfoTree.hole _ => t

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M IO (CommandResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match s.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let initialCmdState? := cmdSnapshot?.map fun c => c.cmdState
  let (initialCmdState, cmdState, messages, trees) ← try
    IO.processInput s.cmd initialCmdState?
  catch ex =>
    return .inr ⟨ex.toString⟩
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees initialCmdState.env none
  let sorries ← match s.rootGoals with
  | some true => pure (sorries ++ (← collectRootGoalsAsSorries trees initialCmdState.env))
  | _ => pure sorries
  let tactics ← match s.allTactics with
  | some true => tactics trees initialCmdState.env
  | _ => pure []
  let proofTreeEdges ← match s.proofTrees with
  | some true => some <$> proofTrees trees
  | _ => pure none
  let cmdSnapshot :=
  { cmdState
    cmdContext := (cmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "",
        fileMap := default,
        snap? := none,
        cancelTk? := none } }
  let env ← recordCommandSnapshot cmdSnapshot
  let jsonTrees := match s.infotree with
  | some "full" => trees
  | some "tactics" => trees.flatMap InfoTree.retainTacticInfo
  | some "original" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainOriginal
  | some "substantive" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainSubstantive
  | some "no_children" => trees.map removeChildren
  | _ => []
  let infotree ← if jsonTrees.isEmpty then
    pure none
  else
    pure <| some <| Json.arr (← jsonTrees.toArray.mapM fun t => t.toJson none)
  return .inl
    { env,
      messages,
      sorries,
      tactics,
      infotree,
      proofTreeEdges }

def processFile (s : File) : M IO (CommandResponse ⊕ Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := none, cmd }
  catch e =>
    pure <| .inr ⟨e.toString⟩

/--
Run a single tactic, returning the id of the new proof statement, and the new goals.
-/
-- TODO detect sorries?
def runProofStep (s : ProofStep) : M IO (ProofStepResponse ⊕ Error) := do
  match (← get).proofStates[s.proofState]? with
  | none => return .inr ⟨"Unknown proof state."⟩
  | some proofState =>
    try
      let proofState' ← proofState.runString s.tactic
      return .inl (← createProofStepReponse proofState' proofState)
    catch ex =>
      return .inr ⟨"Lean error:\n" ++ ex.toString⟩

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
partial def getLines : IO String := do
  let line ← (← IO.getStdin).getLine
  if line.trim.isEmpty then
    return line
  else
    return line ++ (← getLines)

instance [ToJson α] [ToJson β] : ToJson (α ⊕ β) where
  toJson x := match x with
  | .inl a => toJson a
  | .inr b => toJson b

/-- Commands accepted by the REPL. -/
inductive Input
| command : REPL.Command → Input
| file : REPL.File → Input
| proofStep : REPL.ProofStep → Input
| pickleEnvironment : REPL.PickleEnvironment → Input
| unpickleEnvironment : REPL.UnpickleEnvironment → Input
| pickleProofSnapshot : REPL.PickleProofState → Input
| unpickleProofSnapshot : REPL.UnpickleProofState → Input
| pruneSnapshots : REPL.PruneSnapshots → Input

/-- Parse a user input string to an input command. -/
def parse (query : String) : IO Input := do
  let json := Json.parse query
  match json with
  | .error e => throw <| IO.userError <| toString <| toJson <|
      (⟨"Could not parse JSON:\n" ++ e⟩ : Error)
  | .ok j => match fromJson? j with
    | .ok (r : REPL.ProofStep) => return .proofStep r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.PickleEnvironment) => return .pickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.UnpickleEnvironment) => return .unpickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.PickleProofState) => return .pickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.UnpickleProofState) => return .unpickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.Command) => return .command r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.File) => return .file r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.PruneSnapshots) => return .pruneSnapshots r
    | .error e => throw <| IO.userError <| toString <| toJson <|
        (⟨"Could not parse as a valid JSON command:\n" ++ e⟩ : Error)

/-- Avoid buffering the output. -/
def printFlush [ToString α] (s : α) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (toString s)
  out.flush -- Flush the output

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit :=
  StateT.run' loop {}
where loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return ()
  if query.startsWith "#" || query.startsWith "--" then loop else
  IO.println <| toString <| ← match ← parse query with
  | .command r => return toJson (← runCommand r)
  | .file r => return toJson (← processFile r)
  | .proofStep r => return toJson (← runProofStep r)
  | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
  | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
  | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
  | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
  | .pruneSnapshots r => return toJson (← pruneSnapshots r)
  printFlush "\n" -- easier to parse the output if there are blank lines
  loop

/-- Main executable function, run as `lake exe repl`. -/
unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl
