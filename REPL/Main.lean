/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.JSON
import REPL.Frontend
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

/-- The monadic state for the Lean REPL. -/
structure State where
  environments : Array Environment
  lines : Array Nat

/-- The Lean REPL monad. -/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

/-- Get the next available id for a new environment. -/
def nextId : M m Nat := do pure (← get).environments.size

/-- Run a command, returning the id of the new environment, and any messages and sorries. -/
unsafe def run (s : Run) : M m Response := do
  let env? := s.env.bind ((← get).environments[·]?)
  let (env, messages, trees) ← IO.processInput s.cmd env? {} ""
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← trees.bind InfoTree.sorries |>.mapM
    fun ⟨ctx, g, pos, endPos⟩ => Sorry.of ctx g pos endPos
  let lines := s.cmd.splitOn "\n" |>.length
  let id ← nextId
  modify fun s => { environments := s.environments.push env, lines := s.lines.push lines }
  pure ⟨id, messages, sorries⟩

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit :=
  StateT.run' loop ⟨#[], #[]⟩
where loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return
  let json := Json.parse query
  match json with
  | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  | .ok j => match fromJson? j with
    | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
    | .ok (r : Run) => IO.println <| toString <| toJson (← run r)
  loop

instance : ToJson Substring where
  toJson s := toJson s.toString

instance : ToJson String.Pos where
  toJson n := toJson n.1

deriving instance ToJson for SourceInfo
deriving instance ToJson for Syntax.Preresolved
deriving instance ToJson for Syntax

/-- Main executable function, run as `lake env lean --run Mathlib/Util/REPL.lean`. -/
unsafe def main (args : List String) : IO Unit := do
  let mod :: rest := args | repl
  let mainModuleName := mod.toName
  initSearchPath (← findSysroot)
  let srcSearchPath ← initSrcSearchPath (← findSysroot)
  let opts := Options.empty.setBool `trace.Elab.info true
  let some file ← srcSearchPath.findModuleWithExt "lean" mainModuleName
    | throw (.userError s!"module {mainModuleName} not found")
  let input ← IO.FS.readFile file
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext input file.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw <| IO.userError "Errors during import; aborting"
  let env := env.setMainModule mainModuleName
  let commandState := { Command.mkState env messages opts with infoState.enabled := true }
  match rest with
  | [] =>
    let s ← IO.processCommands inputCtx parserState commandState
    let ilean :=
      let trees := s.commandState.infoState.trees.toArray
      let references := Lean.Server.findModuleRefs inputCtx.fileMap trees (localVars := false)
      { module := mainModuleName, references : Lean.Server.Ilean }
    let commands := s.commands.pop -- remove EOI command
    IO.println $ Json.mkObj [
      ("header", toJson header),
      ("commands", toJson commands),
      ("ilean", toJson ilean)
    ]
  | arg :: _ =>
    let some n := arg.toNat? | throw (.userError "usage: ast_export <MOD> [cmd id]")
    let process : Frontend.FrontendM Unit :=
      for _ in [0:n] do
        let done ← Frontend.processCommand
        if done then throw (.userError "command index out of range")
    let (_, s) ← (process.run { inputCtx }).run
      { commandState, parserState, cmdPos := parserState.pos }
    IO.println "{\"env\": 0}"
    StateT.run' repl.loop ⟨#[s.commandState.env], #[]⟩
