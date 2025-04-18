/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Elab.Frontend

open Lean Elab

namespace Lean.Elab.IO

/--
Wrapper for `IO.processCommands` that enables info states, and returns
* the new command state
* messages
* info trees
-/
def processCommandsWithInfoTrees
    (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : IO (Command.State × List Message × List InfoTree) := do
  let commandState := { commandState with infoState.enabled := true }
  let s ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState
  pure (s, s.messages.toList, s.infoState.trees.toList)

/--
Process some text input, with or without an existing command state.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.

Returns the resulting command state, along with a list of messages and info trees.
-/
def processInput (input : String) (cmdState? : Option Command.State)
    (opts : Options := {}) (fileName : Option String := none) :
    IO (Command.State × List Message × List InfoTree) := unsafe do
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


/-
  asTask but with a timeout
-/
def withTimeout {α : Type} (act : IO α) (timeoutMs : Nat) (prio := Task.Priority.default) : IO (Except IO.Error α) := do
  let task ← IO.asTask act prio
  for _ in [0:timeoutMs / 1000] do
    if ← IO.hasFinished task then
      return task.get
    else
      IO.sleep 1000
  IO.cancel task
  -- I'm not sure what the actual error code should be
  return .error <| IO.Error.timeExpired 0 "timeout exceeded"
