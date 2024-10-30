/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
import Lean.Message
import Lean.Elab.InfoTree.Main

open Lean Elab InfoTree

namespace REPL

structure CommandOptions where
  allTactics : Option Bool := none
  /--
  Should be "full", "tactics", "original", or "substantive".
  Anything else is ignored.
  -/
  infotree : Option String

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

/-- A Lean `sorry`. -/
structure Sorry where
  pos : Pos
  endPos : Pos
  goal : String
  /--
  The index of the proof state at the sorry.
  You can use the `ProofStep` instruction to run a tactic at this state.
  -/
  proofState : Option Nat
deriving FromJson

instance : ToJson Sorry where
  toJson r := Json.mkObj <| .join [
    [("goal", r.goal)],
    [("proofState", toJson r.proofState)],
    if r.pos.line ≠ 0 then [("pos", toJson r.pos)] else [],
    if r.endPos.line ≠ 0 then [("endPos", toJson r.endPos)] else [],
  ]

/-- Construct the JSON representation of a Lean sorry. -/
def Sorry.of (goal : String) (pos endPos : Lean.Position) (proofState : Option Nat) : Sorry :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goal,
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
deriving FromJson

def Json.nonemptyList [ToJson α] (k : String) : List α → List (String × Json)
  | [] => []
  | l  => [⟨k, toJson l⟩]

instance : ToJson CommandResponse where
  toJson r := Json.mkObj <| .join [
    [("env", r.env)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "tactics" r.tactics,
    match r.infotree with | some j => [("infotree", j)] | none => []
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
deriving ToJson, FromJson

instance : ToJson ProofStepResponse where
  toJson r := Json.mkObj <| .join [
    [("proofState", r.proofState)],
    [("goals", toJson r.goals)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "traces" r.traces
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
