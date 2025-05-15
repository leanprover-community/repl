/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
import Lean.Message
import Lean.Elab.InfoTree.Main
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
import REPL.Lean.InfoTree.ToJson

open Lean Elab InfoTree

namespace REPL

structure CommandOptions where
  allTactics : Option Bool := none
  rootGoals : Option Bool := none
  /--
  Should be "full", "tactics", "original", or "substantive".
  Anything else is ignored.
  -/
  infotree : Option String
  proofTrees : Option Bool := none

/-- Run Lean commands.
If `env = none`, starts a new session (in which you can use `import`).
If `env = some n`, builds on the existing environment `n`.
-/
structure Command extends CommandOptions where
  env : Option Nat
  cmd : String
deriving ToJson, FromJson

/-- Process a Lean file in a fresh environment. -/
structure File extends CommandOptions where
  path : System.FilePath
deriving FromJson

structure PruneSnapshots where
  cmdFromId : Option Nat
  proofFromId : Option Nat
deriving ToJson, FromJson

/--
Run a tactic in a proof state.
-/
structure ProofStep where
  proofState : Nat
  tactic : String
deriving ToJson, FromJson

/-- Line and column information for error messages and sorries. -/
structure Pos where
  line : Nat
  column : Nat
deriving ToJson, FromJson

/-- Severity of a message. -/
inductive Severity
  | trace | info | warning | error
deriving ToJson, FromJson

/-- A Lean message. -/
structure Message where
  pos : Pos
  endPos : Option Pos
  severity : Severity
  data : String
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean message. -/
def Message.of (m : Lean.Message) : IO Message := do pure <|
  { pos := ⟨m.pos.line, m.pos.column⟩,
    endPos := m.endPos.map fun p => ⟨p.line, p.column⟩,
    severity := match m.severity with
    | .information => .info
    | .warning => .warning
    | .error => .error,
    data := (← m.data.toString).trim }

structure HypothesisInfo where
  username : String
  type : String
  value : Option String
  -- unique identifier for the hypothesis, fvarId
  id : String
  isProof : String
  deriving Inhabited, ToJson, FromJson

structure GoalInfo where
  username : String
  type : String
  hyps : List HypothesisInfo
  -- unique identifier for the goal, mvarId
  id : MVarId
  deriving Inhabited, ToJson, FromJson

/-- A Lean `sorry`. -/
structure Sorry where
  pos : Pos
  endPos : Pos
  goal : String
  goalInfo: Option GoalInfo
  /--
  The index of the proof state at the sorry.
  You can use the `ProofStep` instruction to run a tactic at this state.
  -/
  proofState : Option Nat
deriving FromJson

instance : ToJson Sorry where
  toJson r := Json.mkObj <| .flatten [
    [("goal", r.goal)],
    match r.goalInfo with
    | some goalInfo => [("goalInfo", toJson goalInfo)]
    | none => [],
    [("proofState", toJson r.proofState)],
    if r.pos.line ≠ 0 then [("pos", toJson r.pos)] else [],
    if r.endPos.line ≠ 0 then [("endPos", toJson r.endPos)] else [],
  ]

/-- Construct the JSON representation of a Lean sorry. -/
def Sorry.of (goal : String) (goalInfo : Option GoalInfo) (pos endPos : Lean.Position) (proofState : Option Nat) : Sorry :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goal,
    goalInfo,
    proofState }

structure Tactic where
  pos : Pos
  endPos : Pos
  goals : String
  tactic : String
  proofState : Option Nat
  usedConstants : Array Name
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean tactic. -/
def Tactic.of (goals tactic : String) (pos endPos : Lean.Position) (proofState : Option Nat) (usedConstants : Array Name) : Tactic :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goals,
    tactic,
    proofState,
    usedConstants }

private def mayBeProof (expr : Expr) : MetaM String := do
  let type : Expr ← Lean.Meta.inferType expr
  if ← Meta.isProof expr then
    return "proof"
  if type.isSort then
    return "universe"
  else
    return "data"

def printGoalInfo (printCtx : ContextInfo) (id : MVarId) : IO GoalInfo := do
  let some decl := printCtx.mctx.findDecl? id
    | panic! "printGoalInfo: goal not found in the mctx"
  -- to get tombstones in name ✝ for unreachable hypothesis
  let lctx := decl.lctx |>.sanitizeNames.run' {options := {}}
  let ppContext := printCtx.toPPContext lctx

  let hyps ← lctx.foldrM (init := []) (fun hypDecl acc => do
    if hypDecl.isAuxDecl || hypDecl.isImplementationDetail then
      return acc

    let type ← liftM (ppExprWithInfos ppContext hypDecl.type)
    let value ← liftM (hypDecl.value?.mapM (ppExprWithInfos ppContext))
    let isProof : String ← printCtx.runMetaM decl.lctx (mayBeProof hypDecl.toExpr)
    return ({
      username := hypDecl.userName.toString,
      type := type.fmt.pretty,
      value := value.map (·.fmt.pretty),
      id := hypDecl.fvarId.name.toString,
      isProof := isProof,
    } : HypothesisInfo) :: acc)
  return ⟨ decl.userName.toString, (← ppExprWithInfos ppContext decl.type).fmt.pretty, hyps, id⟩


instance : BEq GoalInfo where
  beq g1 g2 := g1.id == g2.id

instance : Hashable GoalInfo where
  hash g := hash g.id
structure MetavarDecl.Json where
  mvarId : String
  userName : String
  type : String
  mvarsInType : List MVarId
  value : Option String
deriving ToJson, FromJson

structure MetavarContext.Json where
  decls : Array MetavarDecl.Json
deriving ToJson, FromJson

def MetavarContext.toJson (mctx : MetavarContext) (ctx : ContextInfo) : IO MetavarContext.Json := do
  let mut decls := #[]
  for (mvarId, decl) in mctx.decls do
    let (_, typeMVars) ← ctx.runMetaM decl.lctx ((Meta.collectMVars decl.type).run {})
    decls := decls.push {
      mvarId := toString mvarId.name
      userName := toString decl.userName
      type := (← ctx.ppExpr {} decl.type).pretty
      mvarsInType := typeMVars.result.toList
      -- value := (mctx.getExprAssignmentCore? mvarId).map toString
      value := "N/A"
    }
  return { decls }

structure ProofStepInfo where
  tacticString : String
  infoTree : Option Json
  goalBefore : GoalInfo
  goalsAfter : List GoalInfo
  mctxBefore : Option MetavarContext.Json
  mctxAfter : Option MetavarContext.Json
  tacticDependsOn : List String
  spawnedGoals : List GoalInfo
  start : Option Lean.Position
  finish : Option Lean.Position
  deriving Inhabited, ToJson, FromJson

/--
A response to a Lean command.
`env` can be used in later calls, to build on the stored environment.
-/
structure CommandResponse where
  env : Nat
  messages : List Message := []
  sorries : List Sorry := []
  tactics : List Tactic := []
  infotree : Option Json := none
  proofTreeEdges : Option (List (List ProofStepInfo)) := none
deriving FromJson

def Json.nonemptyList [ToJson α] (k : String) : List α → List (String × Json)
  | [] => []
  | l  => [⟨k, toJson l⟩]

instance : ToJson CommandResponse where
  toJson r := Json.mkObj <| .flatten [
    [("env", r.env)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "tactics" r.tactics,
    match r.infotree with | some j => [("infotree", j)] | none => [],
    match r.proofTreeEdges with
    | some edges => Json.nonemptyList "proofTreeEdges" edges
    | none => [],
  ]

/--
A response to a Lean tactic.
`proofState` can be used in later calls, to run further tactics.
-/
structure ProofStepResponse where
  proofState : Nat
  goals : List String
  messages : List Message := []
  sorries : List Sorry := []
  traces : List String
  goalInfos: List GoalInfo := []
  mctxAfter : Option MetavarContext.Json
  proofStatus : String
  stepVerification : String
deriving ToJson, FromJson

instance : ToJson ProofStepResponse where
  toJson r := Json.mkObj <| .flatten [
    [("proofState", r.proofState)],
    [("goals", toJson r.goals)],
    [("goalInfos", toJson r.goalInfos)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "traces" r.traces,
    match r.mctxAfter with | some mctxAfter => [("mctxAfter", toJson mctxAfter)] | none => [],
    [("proofStatus", r.proofStatus)],
    [("stepVerification", r.stepVerification)]
  ]

/-- Json wrapper for an error. -/
structure Error where
  message : String
deriving ToJson, FromJson

structure PickleEnvironment where
  env : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleEnvironment where
  unpickleEnvFrom : System.FilePath
deriving ToJson, FromJson

structure PickleProofState where
  proofState : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleProofState where
  unpickleProofStateFrom : System.FilePath
  env : Option Nat
deriving ToJson, FromJson

end REPL
