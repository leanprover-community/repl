/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab

namespace Lean.Elab.IO

open Language Lean

partial def processCommandsIncrementally' (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (commandState : Command.State)
    (old? : Option IncrementalState := none) :
    BaseIO (List IncrementalState) := do
  let task ← Language.Lean.processCommands inputCtx parserState commandState
    (old?.map fun old => (old.inputCtx, old.initialSnap))
  return go task.get task #[]
where
  go initialSnap task commands : List IncrementalState :=
    let snap := task.get
    let commands := commands.push snap.data.stx
    let tree : SnapshotTree := ⟨snap.data.toSnapshot,
      #[snap.data.headersSnap.map (sync := true) toSnapshotTree,
        snap.data.finishedSnap.map (sync := true) toSnapshotTree]⟩
    let messages := tree
      |>.getAll.map (·.diagnostics.msgLog)
      |>.foldl (· ++ ·) {}
    let trees := tree
      |>.getAll.map (·.infoTree?) |>.filterMap id |>.toPArray'
    let result :=
    { commandState := { snap.data.finishedSnap.get.cmdState with messages, infoState.trees := trees }
      parserState := snap.data.parserState
      cmdPos := snap.data.parserState.pos
      inputCtx, initialSnap, commands }
    if let some next := snap.next? then
      result :: go initialSnap next commands
    else
      [result]

/--
Wrapper for `IO.processCommands` that enables info states, and returns
* the new command state
* messages
* info trees
-/
def processCommandsWithInfoTrees
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) (incrementalState? : Option IncrementalState := none) :
    IO (Command.State × IncrementalState × List Message × List InfoTree) := do
  let commandState := { commandState with infoState.enabled := true }
  let r ← IO.processCommandsIncrementally' inputCtx parserState commandState incrementalState?
  let r ← if h : 0 < r.length then
    pure r[0]
  else
    throw <| IO.userError ""
  let s := r.commandState
  pure (s, r, s.messages.msgs.toList, s.infoState.trees.toList)

/--
Process some text input, with or without an existing command state.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.

Returns the resulting command state, along with a list of messages and info trees.
-/
def processInput (input : String) (cmdState? : Option Command.State)
     (incrementalState? : Option IncrementalState := none)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Command.State × IncrementalState × List Message × List InfoTree) := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, commandState) ← match cmdState? with
  | none => do
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    pure (parserState, (Command.mkState env messages opts))
  | some cmdState => do
    pure ({ : Parser.ModuleParserState }, cmdState)
  processCommandsWithInfoTrees inputCtx parserState commandState incrementalState?
