import REPL.Basic
import REPL.Actions.Basic
import REPL.Actions.Tactic
import REPL.Frontend

open Lean Elab InfoTree

namespace REPL.Actions

structure CommandOptions where
  allTactics : Option Bool := none
  rootGoals : Option Bool := none
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

instance : ToJson CommandResponse where
  toJson r := Json.mkObj <| .flatten [
    [("env", r.env)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "tactics" r.tactics,
    match r.infotree with | some j => [("infotree", j)] | none => []
  ]

structure PickleEnvironment where
  env : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleEnvironment where
  unpickleEnvFrom : System.FilePath
deriving ToJson, FromJson

variable [Monad m] [MonadREPL m] [MonadLiftT IO m]

/-- Record an `CommandSnapshot` into the REPL state, returning its index for future use. -/
@[specialize]
def recordCommandSnapshot (state : CommandSnapshot) : m Nat := do
  modifyGetCmdSnaps fun s => (s.size, s.push state)

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M (CommandResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match s.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let initialCmdState? := cmdSnapshot?.map fun c => c.cmdState
  let (initialCmdState, cmdState, messages, trees) ← try
    IO.processInput s.cmd initialCmdState?
  catch ex =>
    return .inr ⟨ex.toString⟩
  let messages ← messages.mapM fun m => Message.of m
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
  let sorries ← sorries trees initialCmdState.env none
  let sorries ← match s.rootGoals with
  | some true => pure (sorries ++ (← collectRootGoalsAsSorries trees initialCmdState.env))
  | _ => pure sorries
  let tactics ← match s.allTactics with
  | some true => tactics trees initialCmdState.env
  | _ => pure []
  let cmdSnapshot :=
  { cmdState
    cmdContext := (cmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "",
        fileMap := default,
        snap? := none,
        cancelTk? := none } }
  let env ← recordCommandSnapshot cmdSnapshot
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
    { env,
      messages,
      sorries,
      tactics
      infotree }

/-- Pickle a `CommandSnapshot`, generating a JSON response. -/
@[specialize]
def pickleCommandSnapshot (n : PickleEnvironment) : m (CommandResponse ⊕ Error) := do
  match (← getCmdSnaps)[n.env]? with
  | none => return .inr ⟨"Unknown environment."⟩
  | some env =>
    discard <| env.pickle n.pickleTo
    return .inl { env := n.env }

/-- Unpickle a `CommandSnapshot`, generating a JSON response. -/
def unpickleCommandSnapshot (n : UnpickleEnvironment) : M CommandResponse := do
  let (env, _) ← CommandSnapshot.unpickle n.unpickleEnvFrom
  let env ← recordCommandSnapshot env
  return { env }
