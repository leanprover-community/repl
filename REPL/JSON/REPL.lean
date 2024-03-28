import REPL.Main
import REPL.Json.Types

namespace REPL

variable [Monad m] [MonadLiftT IO m]

open JSON

def TacticResult.toJson (t : TacticResult) : M m JSON.Tactic := do
  let goals := "\n".intercalate (← t.proofState.ppGoals)
  let proofStateId ← recordProofSnapshot t.proofState
  return Tactic.of goals t.src t.pos t.endPos proofStateId

def SorryResult.toJson (s : SorryResult) : M m JSON.Sorry := do
  return { ← TacticResult.toJson s.toTacticResult with }

def CommandResponse.toJson (r : CommandResponse) : M m JSON.CommandResponse := do
  let messages ← r.messages.mapM fun m => Message.of m
  let sorries ← r.sorries |>.mapM fun s => s.toJson
  let tactics ← r.tactics |>.mapM fun t => t.toJson
  let infotree := if r.infotree.isEmpty then
    none
  else
    some <| Lean.Json.arr (← r.infotree.toArray.mapM fun t => t.toJson none)
  return {
    source := r.source
    env := r.env
    messages
    sorries
    tactics
    infotree }

def InfoTreeOption.ofString (s : Option String) : InfoTreeOption :=
  match s with
  | .some "full" => .full
  | .some "by" => .by
  | .some "tactics" => .tactics
  | .some "original" => .original
  | .some "substantive" => .substantive
  | _ => .none

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def handleCommandRequest (s : JSON.Command) : M IO (JSON.CommandResponses ⊕ JSON.Error) := do
  match ← runCommand s.cmd s.env s.replace s.incr
      (s.allTactics.getD false) (InfoTreeOption.ofString s.infotree) with
  | .inl r => return .inl { results := ← r.mapM fun r => r.toJson }
  | .inr e => return .inr ⟨e⟩

def handleFileRequest (s : JSON.File) : M IO (JSON.CommandResponses ⊕ JSON.Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    handleCommandRequest { s with env := none, incr := none, replace := none, cmd }
  catch e =>
    pure <| .inr ⟨e.toString⟩

def ProofStepResponse.toJson (r : ProofStepResponse) : M m JSON.ProofStepResponse := do
  let messages ← r.messages.mapM fun m => Message.of m
  let sorries ← r.sorries |>.mapM fun s => s.toJson
  let id ← recordProofSnapshot r.proofState
  return {
    proofState := id
    goals := (← r.proofState.ppGoals)
    messages
    sorries
    traces := r.traces }

/-- Record a `ProofSnapshot` and generate a JSON response for it. -/
def createProofStepReponse (proofState : ProofSnapshot) (old? : Option ProofSnapshot := none) :
    M m JSON.ProofStepResponse := do
  (← proofState.diff old?).toJson

/--
Run a single tactic, returning the id of the new proof statement, and the new goals.
-/
-- TODO detect sorries?
def handleProofStep (s : ProofStep) : M IO (JSON.ProofStepResponse ⊕ JSON.Error) := do
  match (← get).proofStates[s.proofState]? with
  | none => return .inr ⟨"Unknown proof state."⟩
  | some proofState =>
    try
      let proofState' ← proofState.runString s.tactic
      return .inl (← createProofStepReponse proofState' proofState)
    catch ex =>
      return .inr ⟨"Lean error:\n" ++ ex.toString⟩

/-- Pickle a `Command`, generating a JSON response. -/
def pickleCommandSnapshot (n : PickleEnvironment) : M m (JSON.CommandResponse ⊕ JSON.Error) := do
  match ← lookup? n.env with
  | none => return .inr ⟨"Unknown command."⟩
  | some cmd =>
    -- FIXME presumably we want to pickle more!
    discard <| cmd.snapshot.pickle n.pickleTo
    return .inl { env := n.env, source := "" }

/-- Unpickle a `CommandSnapshot`, generating a JSON response. -/
def unpickleCommandSnapshot (n : UnpickleEnvironment) : M IO JSON.CommandResponse := do
  let (env, _) ← CommandSnapshot.unpickle n.unpickleEnvFrom
  let env ← recordCommandSnapshot none "" .missing env none
  return { env, source := "" }

/-- Pickle a `ProofSnapshot`, generating a JSON response. -/
-- This generates a new identifier, which perhaps is not what we want?
def pickleProofSnapshot (n : PickleProofState) : M m (JSON.ProofStepResponse ⊕ JSON.Error) := do
  match (← get).proofStates[n.proofState]? with
  | none => return .inr ⟨"Unknown proof State."⟩
  | some proofState =>
    discard <| proofState.pickle n.pickleTo
    return .inl (← createProofStepReponse proofState)

/-- Unpickle a `ProofSnapshot`, generating a JSON response. -/
def unpickleProofSnapshot (n : UnpickleProofState) : M IO (JSON.ProofStepResponse ⊕ JSON.Error) := do
  let (cmdSnapshot?, notFound) ← do match n.env with
  | none => pure (none, false)
  | some i => do match ← lookup? i with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let (proofState, _) ← ProofSnapshot.unpickle n.unpickleProofStateFrom ((·.snapshot) <$> cmdSnapshot?)
  Sum.inl <$> createProofStepReponse proofState

end REPL

open Lean (ToJson toJson Json fromJson? initSearchPath)
open REPL

def handleSourceRequest (s : JSON.Source) : M IO (JSON.SourceResponse ⊕ String) := do
  return .inl ⟨← source s.src (before := s.before') (self := s.self') (after := s.after')⟩

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
partial def repl : IO Unit :=
  StateT.run' loop {}
where loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return ()
  if query.startsWith "#" || query.startsWith "--" then loop else
  IO.println <| toString <| ← match ← parse query with
  | .command r => return toJson (← handleCommandRequest r)
  | .file r => return toJson (← handleFileRequest r)
  | .source r => return toJson (← handleSourceRequest r)
  | .proofStep r => return toJson (← handleProofStep r)
  | .pickleEnvironment r => return toJson (← pickleCommandSnapshot r)
  | .unpickleEnvironment r => return toJson (← unpickleCommandSnapshot r)
  | .pickleProofSnapshot r => return toJson (← pickleProofSnapshot r)
  | .unpickleProofSnapshot r => return toJson (← unpickleProofSnapshot r)
  IO.println "" -- easier to parse the output if there are blank lines
  loop

/-- Main executable function, run as `lake exe repl`. -/
def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl
