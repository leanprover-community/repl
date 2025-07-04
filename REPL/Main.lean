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
  Stores the command text and incremental states for each command, indexed by command ID.
  Used for prefix matching to enable incremental processing reuse.
  -/
  cmdTexts : Array String := #[]
  cmdIncrementalStates : Array (List (IncrementalState × Option InfoTree)) := #[]
  /--
  Stores the environment ID that each command was built upon.
  Used to ensure prefix matching only considers compatible environment chains.
  -/
  cmdEnvChain : Array (Option Nat) := #[]
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

/-- Record command text and incremental states for prefix matching reuse. -/
def recordCommandIncrementals (cmdText : String)
    (incStates : List (IncrementalState × Option InfoTree)) (envId? : Option Nat) : M m Unit := do
  modify fun s => { s with
    cmdTexts := s.cmdTexts.push cmdText
    cmdIncrementalStates := s.cmdIncrementalStates.push incStates
    cmdEnvChain := s.cmdEnvChain.push envId? }

/-- Record a `ProofSnapshot` into the REPL state, returning its index for future use. -/
def recordProofSnapshot (proofState : ProofSnapshot) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

/-- Find the longest common prefix between two strings. -/
def longestCommonPrefix (s1 s2 : String) : Nat :=
  let chars1 := s1.toList
  let chars2 := s2.toList
  let rec loop (acc : Nat) : List Char → List Char → Nat
    | [], _ => acc
    | _, [] => acc
    | c1 :: cs1, c2 :: cs2 =>
      if c1 = c2 then loop (acc + 1) cs1 cs2 else acc
  loop 0 chars1 chars2

/-- Check if two commands start from the exact same base environment. -/
def haveSameBaseEnv (envId1? envId2? : Option Nat) : Bool :=
  match envId1?, envId2? with
  | none, none => true  -- Both are from fresh environments
  | some id1, some id2 => id1 = id2  -- Same environment ID
  | _, _ => false  -- One fresh, one inherited - different base environments

/-- Find the best incremental state to reuse based on longest prefix matching from commands with the same base environment. -/
def findBestIncrementalState (newCmd : String) (envId? : Option Nat) : M m (Option IncrementalState) := do
  let state ← get
  if state.cmdTexts.isEmpty then
    return none

  -- Find the command with the longest common prefix in the same environment chain
  let mut bestPrefix := 0
  let mut bestIncrState : Option IncrementalState := none

  for i in [:state.cmdTexts.size] do
    -- Check if this command starts from the same base environment
    let cmdEnvId := if i < state.cmdEnvChain.size then state.cmdEnvChain[i]! else none
    let hasSameBase := haveSameBaseEnv envId? cmdEnvId

    if hasSameBase then
      let cmdText := state.cmdTexts[i]!
      let prefixLen := longestCommonPrefix newCmd cmdText

      -- Only consider significant prefixes (at least 10 characters to avoid noise)
      if prefixLen > bestPrefix && prefixLen ≥ 10 then
        let incStates := state.cmdIncrementalStates[i]!
        -- Find the latest incremental state that doesn't exceed our prefix
        for (incState, _) in incStates.reverse do
          -- Convert string prefix length to byte position for comparison
          let prefixBytes := (cmdText.take prefixLen).utf8ByteSize
          if incState.cmdPos.byteIdx ≤ prefixBytes then
            bestPrefix := prefixLen
            bestIncrState := some incState
            break

  -- Print debug information about reuse
  match bestIncrState with
  | some _ => IO.println s!"Found incremental state to reuse (prefix length: {bestPrefix}, env chain compatible)"
  | none =>
    if state.cmdTexts.isEmpty then
      IO.println "No previous commands available for reuse"
    else
      IO.println "No suitable incremental state found for reuse (considering environment chain compatibility)"

  return bestIncrState

def sorries (trees : List InfoTree) (env? : Option Environment) (rootGoals? : Option (List MVarId))
: M m (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, proofState) ← match g with
        | .tactic g => do
          let s ← ProofSnapshot.create ctx none env? [g] rootGoals?
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
          let s ← ProofSnapshot.create ctx lctx env? [] rootGoals? [t]
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        let proofStateId ← proofState.mapM recordProofSnapshot
        return Sorry.of goal pos endPos proofStateId

def sorriesCmd (treeList : List (IncrementalState × Option InfoTree)) (prevEnv : Environment)
(rootGoals? : Option (List MVarId))
: M m (List Sorry) :=
  match treeList with
  | [] => pure []
  | (state, infoTree?) :: rest => do
    let s ← sorries infoTree?.toList prevEnv rootGoals?
    let restSorries ← sorriesCmd rest state.commandState.env rootGoals?
    return s ++ restSorries

def ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def tactics (trees : List InfoTree) (env? : Option Environment) : M m (List Tactic) :=
  trees.flatMap InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, rootGoals, goals, pos, endPos, ns⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none env? goals rootGoals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let tactic := Format.pretty (← ppTactic ctx stx)
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Tactic.of goals tactic pos endPos proofStateId ns

def tacticsCmd (treeList : List (IncrementalState × Option InfoTree)) (prevEnv : Environment) : M m (List Tactic) := do
  match treeList with
  | [] => pure []
  | (state, infoTree?) :: rest => do
    let ts ← tactics infoTree?.toList prevEnv
    let restTactics ← tacticsCmd rest state.commandState.env
    return ts ++ restTactics

def collectRootGoalsAsSorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) := do
  trees.flatMap InfoTree.rootGoals |>.mapM
    fun ⟨ctx, goals, pos⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none env? goals goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Sorry.of goals pos pos proofStateId

def collectRootGoalsAsSorriesCmd (treeList : List (IncrementalState × Option InfoTree)) (prevEnv : Environment) :
    M m (List Sorry) := do
  match treeList with
  | [] => pure []
  | (state, infoTree?) :: rest => do
    let sorries ← collectRootGoalsAsSorries infoTree?.toList prevEnv
    let restSorries ← collectRootGoalsAsSorriesCmd rest state.commandState.env
    return sorries ++ restSorries

private def collectFVarsAux : Expr → NameSet
  | .fvar fvarId => NameSet.empty.insert fvarId.name
  | .app fm arg => (collectFVarsAux fm).union $ collectFVarsAux arg
  | .lam _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .forallE _ binderType body _ => (collectFVarsAux binderType).union $ collectFVarsAux body
  | .letE _ type value body _ => ((collectFVarsAux type).union $ collectFVarsAux value).union $ collectFVarsAux body
  | .mdata _ expr => collectFVarsAux expr
  | .proj _ _ struct => collectFVarsAux struct
  | _ => NameSet.empty

/-- Collect all fvars in the expression, and return their names. -/
private def collectFVars (e : Expr) : MetaM (Array Expr) := do
  let names := collectFVarsAux e
  let mut fvars := #[]
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail then
      continue
    if names.contains ldecl.fvarId.name then
      fvars := fvars.push $ .fvar ldecl.fvarId
  return fvars


private def abstractAllLambdaFVars (e : Expr) : MetaM Expr := do
  let mut e' := e
  while e'.hasFVar do
    let fvars ← collectFVars e'
    if fvars.isEmpty then
      break
    e' ← Meta.mkLambdaFVars fvars e'
  return e'

/--
Evaluates the current status of a proof, returning a string description.
Main states include:
- "Completed": Proof is complete and type checks successfully
- "Incomplete": When goals remain, or proof contains sorry/metavariables
- "Error": When kernel type checking errors occur

Inspired by LeanDojo REPL's status tracking.
-/
def getProofStatus (proofState : ProofSnapshot) : M m String := do
  match proofState.tacticState.goals with
    | [] =>
      let res := proofState.runMetaM do
        match proofState.rootGoals with
        | [goalId] =>
          goalId.withContext do
          match proofState.metaState.mctx.getExprAssignmentCore? goalId with
          | none => return "Error: Goal not assigned"
          | some pf => do
            let pf ← instantiateMVars pf

            -- First check that the proof has the expected type
            let pft ← Meta.inferType pf >>= instantiateMVars
            let expectedType ← Meta.inferType (mkMVar goalId) >>= instantiateMVars
            unless (← Meta.isDefEq pft expectedType) do
              return s!"Error: proof has type {pft} but root goal has type {expectedType}"

            let pf ← abstractAllLambdaFVars pf >>= instantiateMVars
            let pft ← Meta.inferType pf >>= instantiateMVars

            if pf.hasExprMVar then
              return "Incomplete: contains metavariable(s)"

            -- Find all level parameters
            let usedLevels := collectLevelParams {} pft
            let usedLevels := collectLevelParams usedLevels pf

            let decl := Declaration.defnDecl {
              name := Name.anonymous,
              type := pft,
              value := pf,
              levelParams := usedLevels.params.toList,
              hints := ReducibilityHints.opaque,
              safety := DefinitionSafety.safe
            }

            try
              let _ ← addDecl decl
            catch ex =>
              return s!"Error: kernel type check failed: {← ex.toMessageData.toString}"

            if pf.hasSorry then
              return "Incomplete: contains sorry"
            return "Completed"

        | _ => return "Not verified: more than one initial goal"
      return (← res).fst

    | _ => return "Incomplete: open goals remain"

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
  let sorries ← sorries trees none (some proofState.rootGoals)
  let id ← recordProofSnapshot proofState
  return {
    proofState := id
    goals := (← proofState.ppGoals).map fun s => s!"{s}"
    messages
    sorries
    traces
    proofStatus := (← getProofStatus proofState) }

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

/--
Run a command, returning the id of the new environment, and any messages and sorries.
-/
def runCommand (s : Command) : M IO (CommandResponse ⊕ Error) := do
  let (cmdSnapshot?, notFound) ← do match s.env with
  | none => pure (none, false)
  | some i => do match (← get).cmdStates[i]? with
    | some env => pure (some env, false)
    | none => pure (none, true)
  if notFound then
    return .inr ⟨"Unknown environment."⟩
  let initialCmdState? := cmdSnapshot?.map fun c => c.cmdState

  -- Find the best incremental state to reuse based on prefix matching
  let bestIncrementalState? ← findBestIncrementalState s.cmd s.env

  let (initialCmdState, incStates, messages) ← try
    IO.processInput s.cmd initialCmdState? (incrementalState? := bestIncrementalState?)
  catch ex =>
    return .inr ⟨ex.toString⟩

  -- Store the command text and incremental states for future reuse
  recordCommandIncrementals s.cmd incStates s.env

  -- showcase the input string for each incremental state
  let mut prevPos := 0
  for (incState, _) in incStates do
    let endPos := incState.cmdPos
    let processedText := incState.inputCtx.input.extract prevPos endPos
    IO.println s!"Processing incremental state [pos: {prevPos}..{endPos}]:\n```lean4\n{processedText}\n```"
    prevPos := endPos

  let cmdState := (incStates.getLast?.map (fun c => c.1.commandState)).getD initialCmdState
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← sorriesCmd incStates initialCmdState.env none
  let sorries ← match s.rootGoals with
  | some true => pure (sorries ++ (← collectRootGoalsAsSorriesCmd incStates initialCmdState.env))
  | _ => pure sorries
  let tactics ← match s.allTactics with
  | some true => tacticsCmd incStates initialCmdState.env
  | _ => pure []
  let cmdSnapshot :=
  { cmdState
    cmdContext := (cmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "",
        fileMap := default,
        snap? := none,
        cancelTk? := none } }
  let env ← recordCommandSnapshot cmdSnapshot
  let trees := cmdState.infoState.trees.toList
  -- For debugging purposes, sometimes we print out the trees here:
  -- trees.forM fun t => do IO.println (← t.format)
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

def processFile (s : File) : M IO (CommandResponse ⊕ Error) := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := s.env, cmd }
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
    return line.trimRight ++ (← getLines)

instance [ToJson α] [ToJson β] : ToJson (α ⊕ β) where
  toJson x := match x with
  | .inl a => toJson a
  | .inr b => toJson b

/-- Commands accepted by the REPL. -/
inductive Input
| command : REPL.Command → Input
| file : REPL.File → Input
| proofStep : REPL.ProofStep → Input
| pickleEnvironment : REPL.PickleEnvironment → Input
| unpickleEnvironment : REPL.UnpickleEnvironment → Input
| pickleProofSnapshot : REPL.PickleProofState → Input
| unpickleProofSnapshot : REPL.UnpickleProofState → Input

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
