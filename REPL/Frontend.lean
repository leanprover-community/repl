/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab

namespace Lean.Elab.IO

partial def filterRootTactics (tree : InfoTree) : Bool :=
  match tree with
  | InfoTree.hole _     => true
  | InfoTree.context _ t => filterRootTactics t
  | InfoTree.node i _   => match i with
      | .ofTacticInfo _ => false
      | _ => true

/-- Traverses a command snapshot tree, yielding each intermediate state. -/
partial def traverseCommandSnapshots (snap : Language.Lean.CommandParsedSnapshot)
(prevCmdState : Command.State) :
    IO (List ((List InfoTree) × Command.State)) := do
  let tree := Language.toSnapshotTree snap
  let snapshots := tree.getAll
  let infotrees := snapshots.map (·.infoTree?)
  let infotrees := (infotrees.filterMap id).toList.filter filterRootTactics
  let results := [(infotrees, snap.resultSnap.task.get.cmdState)]
  -- let results := [(infotrees, prevCmdState)]
  match snap.nextCmdSnap? with
  | none => return results
  | some nextSnapTask =>
      let nextSnap := nextSnapTask.task.get
      let nextResults ← traverseCommandSnapshots nextSnap snap.resultSnap.task.get.cmdState
      return results ++ nextResults

/--
Wrapper for `IO.processCommands` that enables info states, and returns
* the new command state
* messages
* info trees
-/
def processCommandsWithInfoTrees
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (Command.State × List Message × (List ((List InfoTree) × Command.State))) := do
  let commandState := { commandState with infoState.enabled := true }
  let incs ← IO.processCommandsIncrementally inputCtx parserState commandState none
  let infoTrees ← traverseCommandSnapshots incs.initialSnap commandState
  let s := incs.commandState
  pure (s, s.messages.toList, infoTrees)

/--
Process some text input, with or without an existing command state.

Returns:
1. The resulting command state after processing the entire input
2. List of messages
3. List of info trees along with Command.State from the incremental processing
-/
def processInput (input : String) (cmdState? : Option Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Command.State × List Message × (List ((List InfoTree) × Command.State))) := unsafe do
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
  processCommandsWithInfoTrees inputCtx parserState commandState
