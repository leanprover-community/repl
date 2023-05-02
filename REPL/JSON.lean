/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Data.Json
import Lean.Message
import Lean.Elab.InfoTree.Main

open Lean Elab

namespace REPL

/-- Run Lean commands.
If `env = none`, starts a new session (in which you can use `import`).
If `env = some n`, builds on the existing environment `n`.
-/
structure Run where
  env : Option Nat
  cmd : String
deriving ToJson, FromJson

/-- Line and column information for error messages and sorries. -/
structure Pos where
  line : Nat
  column : Nat
deriving ToJson, FromJson

/-- Severity of a message. -/
inductive Severity
  | info | warning | error
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
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean sorry. -/
def Sorry.of (ctx : ContextInfo) (g : MVarId) (pos endPos : Lean.Position) :
    IO Sorry := do pure <|
{ pos := ⟨pos.line, pos.column⟩,
  endPos := ⟨endPos.line, endPos.column⟩,
  goal := s!"{(← ctx.ppGoals [g])}".trim }

/--
A response to a Lean command.
`env` can be used in later calls, to build on the stored environment.
-/
structure Response where
  env : Nat
  messages : List Message
  sorries : List Sorry
  allTacticSteps : List String
deriving ToJson, FromJson

/-- Json wrapper for an error. -/
structure Error where
  message : String
deriving ToJson, FromJson

end REPL