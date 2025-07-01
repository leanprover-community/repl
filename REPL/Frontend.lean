/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend
import Std.Data.HashMap

open Lean Elab Language

namespace Lean.Elab.IO

partial def IO.processCommandsIncrementally' (inputCtx : Parser.InputContext)
    (parserState : Parser.ModuleParserState) (commandState : Command.State)
    (old? : Option IncrementalState) :
    BaseIO (List (IncrementalState × Option InfoTree)) := do
  let task ← Language.Lean.processCommands inputCtx parserState commandState
    (old?.map fun old => (old.inputCtx, old.initialSnap))
  return go task.get task #[]
where
  go initialSnap t commands :=
    let snap := t.get
    let commands := commands.push snap
    -- Opting into reuse also enables incremental reporting, so make sure to collect messages from
    -- all snapshots
    let messages := toSnapshotTree initialSnap
      |>.getAll.map (·.diagnostics.msgLog)
      |>.foldl (· ++ ·) {}
    -- In contrast to messages, we should collect info trees only from the top-level command
    -- snapshots as they subsume any info trees reported incrementally by their children.
    let trees := commands.map (·.infoTreeSnap.get.infoTree?) |>.filterMap id |>.toPArray'
    let result : (IncrementalState × Option InfoTree) :=
      ({ commandState := { snap.resultSnap.get.cmdState with messages, infoState.trees := trees }
         , parserState := snap.parserState
         , cmdPos := snap.parserState.pos
         , commands := commands.map (·.stx)
         , inputCtx := inputCtx
         , initialSnap := initialSnap
       }, snap.infoTreeSnap.get.infoTree?)
    if let some next := snap.nextCmdSnap? then
      result :: go initialSnap next.task commands
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
    (commandState : Command.State) (incrementalState? : Option IncrementalState := none)
    : IO (List (IncrementalState × Option InfoTree) × List Message) := do
  let commandState := { commandState with infoState.enabled := true }
  let incStates ← IO.processCommandsIncrementally' inputCtx parserState commandState incrementalState?
  pure (incStates, (incStates.getLast?.map (·.1.commandState.messages.toList)).getD {})

/--
Process some text input, with or without an existing command state.
Supports header caching to avoid reprocessing the same imports repeatedly.

Returns:
1. The resulting command state after processing the entire input
2. List of messages
3. List of info trees along with Command.State from the incremental processing
4. Updated header cache mapping import keys to Command.State
-/
def processInput (input : String) (cmdState? : Option Command.State)
    (incrementalState? : Option IncrementalState := none)
    (headerCache : Std.HashMap String Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Command.State × List (IncrementalState × Option InfoTree) × List Message × (Std.HashMap String Command.State)) := unsafe do
  Lean.initSearchPath (← Lean.findSysroot)
  enableInitializersExecution
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  match cmdState? with
  | none => do
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let importKey := (input.take parserState.pos.byteIdx).trim
    match headerCache.get? importKey with
    | some cachedHeaderState => do
      -- Header is cached, use it as the base command state
      let (incStates, messages) ← processCommandsWithInfoTrees inputCtx parserState cachedHeaderState incrementalState?
      return (cachedHeaderState, incStates, messages, headerCache)
    | none => do
      -- Header not cached, process it and cache the result
      let (env, messages) ← processHeader header opts messages inputCtx
      let headerOnlyState := Command.mkState env messages opts
      let headerCache := headerCache.insert importKey headerOnlyState
      let (incStates, messages) ← processCommandsWithInfoTrees inputCtx parserState headerOnlyState incrementalState?
      return (headerOnlyState, incStates, messages, headerCache)
  | some cmdStateBefore => do
    let parserState : Parser.ModuleParserState := {}
    let (incStates, messages) ← processCommandsWithInfoTrees inputCtx parserState cmdStateBefore incrementalState?
    return (cmdStateBefore, incStates, messages, headerCache)
