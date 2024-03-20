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

open Lean Elab Command

namespace REPL

structure Command where
  parentId? : Option Nat
  childIds : List Nat
  src : String
  stx : Syntax
  snapshot : CommandSnapshot
  incrementalState? : Option IncrementalState

/-- The monadic state for the Lean REPL. -/
structure State where
  /--
  Environment snapshots after complete declarations.
  The user can run a declaration in a given environment using `{"cmd": "def f := 37", "env": 17}`.
  -/
  commands : Array Command := #[]
  /-- A list of `Command`s that do not have a parent. -/
  roots : List Nat := []
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

/-- Find a command from its id. -/
def lookup? (i : Nat) : M m (Option Command) := return (← get).commands[i]?

/--
Retrieves the source code for a given command.

By default this returns the code for all commands up to and including the designated command.
To retrieve only the source of the command, use `before := false`.
To also retrieve the source code of the most recent added subsequent commands, use `after := true`.
-/
def source (i : Nat) (before := true) (self := true) (after := false) : M m String := do
  let mut i? := some i
  let mut src := ""
  let mut first := true
  while i?.isSome do
    match i? with
    | none => continue
    | some i =>
      match ← lookup? i with
      | none => i? := none
      | some c =>
        if (!first) || self then src := c.src ++ "\n" ++ src
        i? := if before then c.parentId? else none
        first := false
  if after then
    -- Also descend the most recent children.
    first := true
    i? := some i
    while i?.isSome do
      match i? with
      | none => continue
      | some i =>
        match ← lookup? i with
        | none => i? := none
        | some c =>
          if !first then src := src ++ "\n" ++ c.src
          i? := c.childIds.head?
          first := false
  return if src.startsWith "\n" then src.drop 1 else src

def processSource (s : JSON.Source) : M IO (JSON.SourceResponse ⊕ JSON.Error) := do
  return .inl ⟨← source s.src (before := s.before') (self := s.self') (after := s.after')⟩

def retrieve (after? : Option Nat) (replace? : Option Nat) :
    M IO (Option (Command × Nat × String) ⊕ JSON.Error) := do
  let additionalSource ← match replace? with
  | none => pure ""
  | some j => source j (before := false) (self := false) (after := true)
  let (r, notFound) ← match after? with
  | none =>
    match replace? with
    | none =>
      let c := (← get).commands
      if c.isEmpty then
        pure (none, false)
      else
        pure (c.back?.map fun s => (s, c.size - 1, ""), false)
    | some j => match (← get).commands[j]? with
      | none => return .inr ⟨"Unknown replace target."⟩
      | some x => match x.parentId? with
        | none => pure (none, false)
        | some p => match (← get).commands[p]? with
          | none => return .inr ⟨"Unreachable code; could not find parent of replace target."⟩
          | some c => pure (some (c, p, additionalSource), false)
  | some i => do match (← get).commands[i]? with
    | some env =>
      pure (some (env, i, additionalSource), false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  else
    return .inl r

/-- Find the ids of children of a command, or the roots if the argument is `none`. -/
def children (i? : Option Nat) : M m (List Nat) := do
  match i? with
  | none => return (← get).roots
  | some i => match ← lookup? i with
    | none => return []
    | some c => return c.childIds

/--
Automatically determine the best `IncrementalState` for a new command.
Traverse all the children of `parent?` (or all the roots if `parent? = none`)
and select the incremental state from the command with the longest common prefix.
-/
def findBestIncrementalState (parent? : Option Nat) (src : String) :
    M m (Option IncrementalState) := do
  let candidates ← (← children parent?).filterMapM lookup?
  let pairs := candidates.filterMap fun c =>
    c.incrementalState?.map fun s => (src.firstDiffPos c.src, s)
  return (·.2) <$> (pairs.toArray.insertionSort fun c₁ c₂ => c₁.1 < c₂.1).back?

/-- Find the most recently constructed incremental state for a given parent. -/
def findLatestIncrementalState (parent? : Option Nat) : M m (Option IncrementalState) := do
  let candidates ← (← children parent?).filterMapM lookup?
  return (candidates.filterMap fun c => c.incrementalState?).head?

/-- Record an `CommandSnapshot` into the REPL state, returning its index for future use. -/
def recordCommandSnapshot
    (parentId? : Option Nat) (src : String)
    (state : CommandSnapshot) (incr : Option IncrementalState) :
    M m Nat := do
  let id := (← get).commands.size
  let cmd : Command :=
  { parentId? := parentId?
    childIds := []
    src := src
    stx := .missing -- FIXME
    snapshot := state
    incrementalState? := incr }
  modify fun s => match parentId? with
  | none => { s with roots := id :: s.roots, commands := s.commands.push cmd }
  | some parentId =>
      { s with
        commands := (s.commands.modify parentId fun c => { c with childIds := id :: c.childIds })
          |>.push cmd }
  return id

/-- Record a `ProofSnapshot` into the REPL state, returning its index for future use. -/
def recordProofSnapshot (proofState : ProofSnapshot) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

open JSON

def sorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) :=
  trees.bind InfoTree.sorries |>.mapM
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

def ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def tactics (trees : List InfoTree) : M m (List Tactic) :=
  trees.bind InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, goals, pos, endPos⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none none goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Tactic.of goals tactic pos endPos proofStateId

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

/-- Pickle a `Command`, generating a JSON response. -/
def pickleCommandSnapshot (n : PickleEnvironment) : M m (CommandResponse ⊕ Error) := do
  match (← get).commands[n.env]? with
  | none => return .inr ⟨"Unknown command."⟩
  | some cmd =>
    -- FIXME presumably we want to pickle more!
    discard <| cmd.snapshot.pickle n.pickleTo
    return .inl { env := n.env, source := "" }

/-- Unpickle a `CommandSnapshot`, generating a JSON response. -/
def unpickleCommandSnapshot (n : UnpickleEnvironment) : M IO CommandResponse := do
  let (env, _) ← CommandSnapshot.unpickle n.unpickleEnvFrom
  let env ← recordCommandSnapshot none "" env none
  return { env, source := "" }

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
  | some i => do match (← get).commands[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let (proofState, _) ← ProofSnapshot.unpickle n.unpickleProofStateFrom ((·.snapshot) <$> cmdSnapshot?)
  Sum.inl <$> createProofStepReponse proofState


/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : JSON.Command) : M IO (CommandResponses ⊕ Error) := do
  let (retrieved?, parentId?, additionalSource) ← match ← retrieve s.env s.replace with
  | .inr e => return .inr e
  | .inl none => pure (none, none, "")
  | .inl (some x) => pure (some x.1, some x.2.1, x.2.2)
  let (incrementalStateBefore?, notFound) ← do
    match s.incr with
    | none => pure (← findLatestIncrementalState s.env, false)
    | some j => do match (← get).commands[j]? with
      | some { incrementalState? := some s, .. } => pure (some s, false)
      | some _
      | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown incremental state."⟩
  let initialCmdSnapshot? := (·.snapshot) <$> retrieved?
  let initialCmdState? := initialCmdSnapshot?.map fun c => c.cmdState
  let (header?, states) ← try
    IO.processInput (s.cmd ++ "\n" ++ additionalSource) initialCmdState? incrementalStateBefore?
  catch ex =>
    return .inr ⟨ex.toString⟩
  -- Drop the "end of input" state.
  let states := states.filter fun s => match s.commands.back? with | none => true | some stx => stx.getKind ≠ ``Lean.Parser.Command.eoi
  let states : List (Command.State × Syntax × Option IncrementalState) :=
    (match header? with | none => [] | some (headerState, headerSyntax) => if isEmptyModuleHeader headerSyntax then [] else [(headerState, headerSyntax, none)]) ++
      states.map fun state => (state.commandState, state.commands.back?.get!, some state)
  let (_, results) ← states.foldlM (init := (parentId?, #[])) fun (i, r) t => do
    let n ← mkResponse i initialCmdSnapshot? s t.1 t.2.1 t.2.2
    pure (n.env, r.push n)
  return .inl { results := results.toList }
where
  isEmptyModuleHeader (stx : Syntax) : Bool :=
    stx.isOfKind ``Parser.Module.header && match stx.getArgs with
    | #[prelude, imports] => prelude.getArgs.size = 0 && imports.getArgs.size = 0
    | _ => false
  mkResponse
    (parentId? : Option Nat) (initialCmdSnapshot? : Option CommandSnapshot) (s : JSON.Command)
    (cmdState : Command.State) (stx : Syntax) (incrementalState? : Option IncrementalState) : M IO CommandResponse := do
  let messages := cmdState.messages.msgs.toList
  let trees := cmdState.infoState.trees.toList
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees (initialCmdSnapshot?.map (·.cmdState.env))
  let tactics ← match s.allTactics with
  | some true => tactics trees
  | _ => pure []
  let cmdContext := (initialCmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "", fileMap := default, tacticCache? := none, snap? := none }
  let cmdSnapshot :=
  { cmdState
    cmdContext }
  let (format, _) ← Command.CommandElabM.toIO (do liftCoreM <| PrettyPrinter.ppCommand ⟨stx⟩) cmdContext cmdState -- FIXME this should be the Command.State before, not after?!
  let source := toString format
  let env ← recordCommandSnapshot parentId? source cmdSnapshot incrementalState?
  let jsonTrees := match s.infotree with
  | some "full" => trees
  | some "tactics" => trees.bind InfoTree.retainTacticInfo
  | some "original" => trees.bind InfoTree.retainTacticInfo |>.bind InfoTree.retainOriginal
  | some "substantive" => trees.bind InfoTree.retainTacticInfo |>.bind InfoTree.retainSubstantive
  | _ => []
  let infotree := if jsonTrees.isEmpty then
    none
  else
    some <| Json.arr (← jsonTrees.toArray.mapM fun t => t.toJson none)
  return {
    source,
    env,
    messages,
    sorries,
    tactics
    infotree }

def processFile (s : File) : M IO (CommandResponses ⊕ Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := none, incr := none, replace := none, cmd }
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
| command : JSON.Command → Input
| file : JSON.File → Input
| source : JSON.Source → Input
| proofStep : JSON.ProofStep → Input
| pickleEnvironment : JSON.PickleEnvironment → Input
| unpickleEnvironment : JSON.UnpickleEnvironment → Input
| pickleProofSnapshot : JSON.PickleProofState → Input
| unpickleProofSnapshot : JSON.UnpickleProofState → Input

/-- Parse a user input string to an input command. -/
def parse (query : String) : IO Input := do
  let json := Json.parse query
  match json with
  | .error e => throw <| IO.userError <| toString <| toJson <|
      (⟨"Could not parse JSON:\n" ++ e⟩ : JSON.Error)
  | .ok j => match fromJson? j with
    | .ok (r : JSON.ProofStep) => return .proofStep r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.PickleEnvironment) => return .pickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.UnpickleEnvironment) => return .unpickleEnvironment r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.PickleProofState) => return .pickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.UnpickleProofState) => return .unpickleProofSnapshot r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.Command) => return .command r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.File) => return .file r
    | .error _ => match fromJson? j with
    | .ok (r : JSON.Source) => return .source r
    | .error e => throw <| IO.userError <| toString <| toJson <|
        (⟨"Could not parse as a valid JSON command:\n" ++ e⟩ : JSON.Error)

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
  | .source r => return toJson (← processSource r)
  | .proofStep r => return toJson (← runProofStep r)
  | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
  | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
  | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
  | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
  IO.println "" -- easier to parse the output if there are blank lines
  loop

/-- Main executable function, run as `lake exe repl`. -/
unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl
