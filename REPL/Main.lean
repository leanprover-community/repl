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

def sorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, proofState) ← match g with
        | .tactic g => do
           let s ← ProofSnapshot.create ctx none env? [g]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
           let s ← ProofSnapshot.create ctx lctx env? [] [t]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        let proofStateId ← proofState.mapM recordProofSnapshot
        return Sorry.of goal pos endPos proofStateId

def sorriesGC (trees : List InfoTree) (env? : Option Environment) : IO (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, _) ← match g with
        | .tactic g => do
           let s ← ProofSnapshot.create ctx none env? [g]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
           let s ← ProofSnapshot.create ctx lctx env? [] [t]
           pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        return Sorry.of goal pos endPos none

def ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def tactics (trees : List InfoTree) : M m (List Tactic) :=
  trees.flatMap InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, goals, pos, endPos, ns⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none none goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Tactic.of goals tactic pos endPos proofStateId ns

def tacticsGC (trees : List InfoTree) : IO (List Tactic) :=
  trees.flatMap InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, goals, pos, endPos, ns⟩ => do
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      return Tactic.of goals tactic pos endPos none ns

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
  let sorries ← sorries trees none
  let id ← recordProofSnapshot proofState
  return {
    proofState := id
    goals := (← proofState.ppGoals).map fun s => s!"{s}"
    messages
    sorries
    traces }

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


def getCommandSnapshot (env : Option Nat) :  M IO (Option CommandSnapshot × Bool) :=  do match env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)

def runCommandGCAux (initialCmdState? : Option Command.State) (s : Command) : IO (CommandResponse ⊕ Error) := do
  let (_, messages, trees) ← try
    IO.processInput s.cmd initialCmdState?
  catch ex =>
    return .inr ⟨ex.toString⟩
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorriesGC trees (initialCmdState?.map (·.env))
  let tactics ← match s.allTactics with
  | some true => tacticsGC trees
  | _ => pure []
  let jsonTrees := match s.infotree with
  | some "full" => trees
  | some "tactics" => trees.flatMap InfoTree.retainTacticInfo
  | some "original" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainOriginal
  | some "substantive" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainSubstantive
  | _ => []
  let infotree ← if jsonTrees.isEmpty then
    pure none
  else
    pure <| some <| Json.arr (← jsonTrees.toArray.mapM fun t => t.toJson none)
  return .inl
    { env := none,
      messages,
      sorries,
      tactics
      infotree }

def runCommandGCAuxTimeout (initialCmdState? : Option Command.State) (s : Command) (timeout : Nat) : IO (CommandResponse ⊕ Error) := do
  match ← IO.withTimeout (runCommandGCAux initialCmdState? s) timeout with
  | .ok res => return res
  | .error e => return .inr ⟨e.toString⟩

def runCommandAux (cmdSnapshot? : Option CommandSnapshot) (initialCmdState? : Option Command.State) (s : Command) : M IO (CommandResponse ⊕ Error) := do
  let (cmdState, messages, trees) ← try
    IO.processInput s.cmd initialCmdState?
  catch ex =>
    return .inr ⟨ex.toString⟩
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees (initialCmdState?.map (·.env))
  let tactics ← match s.allTactics with
  | some true => tactics trees
  | _ => pure []
  let jsonTrees := match s.infotree with
  | some "full" => trees
  | some "tactics" => trees.flatMap InfoTree.retainTacticInfo
  | some "original" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainOriginal
  | some "substantive" => trees.flatMap InfoTree.retainTacticInfo |>.flatMap InfoTree.retainSubstantive
  | _ => []
  let infotree ← if jsonTrees.isEmpty then
    pure none
  else
    pure <| some <| Json.arr (← jsonTrees.toArray.mapM fun t => t.toJson none)

  let cmdSnapshot :=
  { cmdState
    cmdContext := (cmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "",
        fileMap := default,
        snap? := none,
        cancelTk? := none } }
  let env ← recordCommandSnapshot cmdSnapshot
  return .inl
    { env := some env,
      messages,
      sorries,
      tactics
      infotree }

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M IO (CommandResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← getCommandSnapshot s.env
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let initialCmdState? := cmdSnapshot?.map fun c => c.cmdState
  if s.gc = some true then
    runCommandGCAux initialCmdState? s
  else
    runCommandAux cmdSnapshot? initialCmdState? s

def splitArray {α : Type} (arr : Array α) (n : Nat) : Array (Array α) := Id.run do
  if n ≤ 0 then #[]
  else if n = 1 then #[arr]
  else if arr.size = 0 then Array.replicate n #[]
  else
    let baseSize := arr.size / n
    let remainder := arr.size % n

    let mut result : Array (Array α) := #[]
    let mut start : Nat := 0

    for i in List.range n do
      let extraElem := if i < remainder then 1 else 0
      let endPos := start + baseSize + extraElem
      let subArray := arr.extract start endPos
      result := result.push subArray
      start := start + baseSize + extraElem
    result

unsafe def batchVerifySequential (initialCmdState : Command.State) (cmds : Array Command) (timeout : Option Nat): IO (Array (CommandResponse ⊕ Error)) :=
  let commandRunner :=
    match timeout with
    | some t => fun cmd => runCommandGCAuxTimeout initialCmdState cmd t
    | none => runCommandGCAux initialCmdState
  cmds.mapM commandRunner

unsafe def batchVerifyParrallelNaive (initialCmdState : Command.State) (cmds : Array Command) (timeout : Option Nat) : IO (Array (CommandResponse ⊕ Error)) := do
  let commandRunner :=
    match timeout with
    | some t => fun cmd => runCommandGCAuxTimeout initialCmdState cmd t
    | none => runCommandGCAux initialCmdState
  let tasks : Array (Task (Except IO.Error (CommandResponse ⊕ Error))) ← (cmds.mapM <| fun cmd => IO.asTask (commandRunner cmd)
  )
  tasks.mapM fun task => do
    try
      match task.get with
      | .ok cmdres => return cmdres
      | .error e => return .inr ⟨e.toString⟩
    catch e =>
      return .inr ⟨e.toString⟩

unsafe def batchVerifyParrallel (commandState : Command.State) (cmds : Array Command) (buckets : Option Nat) (timeout : Option Nat) : IO (Array (CommandResponse ⊕ Error)) := do
  let buckets :=
    match buckets with
    | some x => x
    | none => max 50 cmds.size
  let tasks ← (splitArray cmds buckets |>.mapM <| fun bucket => IO.asTask ( (batchVerifySequential commandState bucket timeout)))
  tasks.flatMapM <|
    fun task => do
      try
        match task.get with
        | .ok cmdres => return cmdres
        | .error e => return Array.replicate buckets (.inr ⟨e.toString⟩)
      catch e =>
        return Array.replicate buckets (.inr ⟨e.toString⟩)

def processFile (s : File) : M IO (CommandResponse ⊕ Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := none, cmd }
  catch e =>
    pure <| .inr ⟨e.toString⟩

unsafe def runBatchVerify (batch : BatchCommand) : M IO (Array (CommandResponse ⊕ Error) ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← getCommandSnapshot batch.env
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let cmdState? := cmdSnapshot?.map fun c => c.cmdState
  let commandState ← match cmdState? with
    | none => do
      let inputCtx   := Parser.mkInputContext "" "<input>"
      let (header, _, messages) ← Parser.parseHeader inputCtx
      let (env, messages) ← processHeader header {} messages inputCtx
      pure (Command.mkState env messages {})
    | some cmdState => do
      pure cmdState
  let cmds : Array Command := (batch.cmds.map fun cmd => { toCommandOptions := batch.toCommandOptions, env := none, cmd := cmd})
  match batch.mode with
  | some x =>
    if x = "naive" then do
      return .inl <| ← batchVerifyParrallelNaive commandState cmds batch.timeout
    if x = "parrallel" then do
      return .inl <| ← batchVerifyParrallel commandState cmds batch.buckets batch.timeout
  | none =>
    pure ()

  return .inl <| ← batchVerifySequential commandState cmds batch.timeout

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


structure Batch where
  header : String
  proofs : Array String
deriving FromJson, ToJson

/-- Commands accepted by the REPL. -/
inductive Input
| command : REPL.Command → Input
| file : REPL.File → Input
| proofStep : REPL.ProofStep → Input
| pickleEnvironment : REPL.PickleEnvironment → Input
| unpickleEnvironment : REPL.UnpickleEnvironment → Input
| pickleProofSnapshot : REPL.PickleProofState → Input
| unpickleProofSnapshot : REPL.UnpickleProofState → Input
| batchVerify : REPL.BatchCommand → Input

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
    | .ok (r : REPL.BatchCommand) => return .batchVerify r
    | .error _ => match fromJson? j with
    | .ok (r : REPL.File) => return .file r
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
  | .batchVerify r => return toJson (← runBatchVerify r)
  | .file r => return toJson (← processFile r)
  | .proofStep r => return toJson (← runProofStep r)
  | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
  | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
  | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
  | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
  printFlush "\n" -- easier to parse the output if there are blank lines
  loop

/-- Main executable function, run as `lake exe repl`. -/
unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl
