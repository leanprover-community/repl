import REPL.Basic
import REPL.Actions.Basic

open Lean Elab InfoTree

namespace REPL.Actions

structure Tactic where
  pos : Pos
  endPos : Pos
  goals : String
  tactic : String
  proofState : Option Nat
  usedConstants : Array Name
deriving ToJson, FromJson

/-- Construct the JSON representation of a Lean tactic. -/
def Tactic.of (goals tactic : String) (pos endPos : Lean.Position) (proofState : Option Nat) (usedConstants : Array Name) : Tactic :=
  { pos := ⟨pos.line, pos.column⟩,
    endPos := ⟨endPos.line, endPos.column⟩,
    goals,
    tactic,
    proofState,
    usedConstants }

/--
Run a tactic in a proof state.
-/
structure ProofStep where
  proofState : Nat
  tactic : String
deriving ToJson, FromJson

/--
A response to a Lean tactic.
`proofState` can be used in later calls, to run further tactics.
-/
structure ProofStepResponse where
  proofState : Nat
  goals : List String
  messages : List Message := []
  sorries : List Sorry := []
  traces : List String
  proofStatus : String
deriving ToJson, FromJson

instance : ToJson ProofStepResponse where
  toJson r := Json.mkObj <| .flatten [
    [("proofState", r.proofState)],
    [("goals", toJson r.goals)],
    Json.nonemptyList "messages" r.messages,
    Json.nonemptyList "sorries" r.sorries,
    Json.nonemptyList "traces" r.traces,
    [("proofStatus", r.proofStatus)]
  ]

structure PickleProofState where
  proofState : Nat
  pickleTo : System.FilePath
deriving ToJson, FromJson

structure UnpickleProofState where
  unpickleProofStateFrom : System.FilePath
  env : Option Nat
deriving ToJson, FromJson

variable [Monad m] [MonadLiftT IO m]

/-- Record a `ProofSnapshot` into the REPL state, returning its index for future use. -/
def recordProofSnapshot (proofState : ProofSnapshot) : M m Nat := do
  let id := (← get).proofStates.size
  modify fun s => { s with proofStates := s.proofStates.push proofState }
  return id

def sorries (trees : List InfoTree) (env? : Option Environment) (rootGoals? : Option (List MVarId))
: M m (List Sorry) :=
  trees.flatMap InfoTree.sorries |>.filter (fun t => match t.2.1 with
    | .term _ none => false
    | _ => true ) |>.mapM
      fun ⟨ctx, g, pos, endPos⟩ => do
        let (goal, proofState) ← match g with
        | .tactic g => do
          let lctx ← ctx.runMetaM {} do
              match ctx.mctx.findDecl? g with
              | some decl => return decl.lctx
              | none => throwError "unknown metavariable '{g}'"
          let s ← ProofSnapshot.create ctx lctx env? [g] rootGoals?
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term lctx (some t) => do
          let s ← ProofSnapshot.create ctx lctx env? [] rootGoals? [t]
          pure ("\n".intercalate <| (← s.ppGoals).map fun s => s!"{s}", some s)
        | .term _ none => unreachable!
        let proofStateId ← proofState.mapM recordProofSnapshot
        return Sorry.of goal pos endPos proofStateId

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

def collectRootGoalsAsSorries (trees : List InfoTree) (env? : Option Environment) : M m (List Sorry) := do
  trees.flatMap InfoTree.rootGoals |>.mapM
    fun ⟨ctx, goals, pos⟩ => do
      let proofState := some (← ProofSnapshot.create ctx none env? goals goals)
      let goals := s!"{(← ctx.ppGoals goals)}".trim
      let proofStateId ← proofState.mapM recordProofSnapshot
      return Sorry.of goals pos pos proofStateId

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

            let pf ← abstractAllLambdaFVars pf
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
