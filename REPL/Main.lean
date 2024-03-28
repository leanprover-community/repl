/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.Frontend
import REPL.Util.Path
import REPL.Lean.ContextInfo
import REPL.Lean.Environment
import REPL.Lean.InfoTree
import REPL.Lean.InfoTree.ToJson
import REPL.Snapshots
import REPL.Proof

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
-- TODO: reduce duplication: there is a `Command.State` in both `snapshot` and `incrementalState?`.


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
        if (!first) || self then src := c.src ++ "\n\n" ++ src
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
          if !first then src := src ++ "\n\n" ++ c.src
          i? := c.childIds.head?
          first := false
  src := src.dropWhile (· == '\n')
  src := src.dropRightWhile (· == '\n')
  return src

/--
Retrieve a previous command.

If `after? = some i`, retrieves the command at index `i`.
Otherwise, if `replace? = some j`, retrieves the parent of the command at index `j`.

If there is such a command, returns `.inl (.some (c, i, s))`
where `c` is the command, `i` is its index,
and `s` is the source code of any subsequent commands the command (if any) referenced in `replace?`.

If `after? = none` and `replace? = none`, returns either `.inl (.some (c, i, ""))`, as above,
for the most recently executed command, or `.inl .none` if no commands have been executed yet.

Finally, returns `.inr e`, where `e : String` is an error message,
if the commands referenced in `after? = some i` or `replace? = some j` did not exist.
-/
def retrieve (after? : Option Nat) (replace? : Option Nat) :
    M m (Option (Command × Nat × String) ⊕ String) := do
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
    | some j => match ← lookup? j with
      | none => return .inr s!"Unknown environment: {replace?.get!}."
      | some x => match x.parentId? with
        | none => pure (none, false)
        | some p => match ← lookup? p with
          | none => return .inr "Unreachable code; could not find parent of `replace?` target."
          | some c => pure (some (c, p, additionalSource), false)
  | some i => do match ← lookup? i with
    | some env =>
      pure (some (env, i, additionalSource), false)
    | none => pure (none, true)
  if notFound then
    return .inr s!"Unknown environment {after?.get!}"
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
    (parentId? : Option Nat) (src : String) (stx : Syntax)
    (state : CommandSnapshot) (incr : Option IncrementalState) :
    M m Nat := do
  let id := (← get).commands.size
  let cmd : Command :=
  { parentId? := parentId?
    childIds := []
    src := src
    stx := stx
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

structure TacticResult where
  proofState : ProofSnapshot
  src : String
  stx : Syntax
  pos : Position
  endPos  : Position

structure SorryResult extends TacticResult where
  src := "sorry"
  stx := Syntax.missing -- FIXME

def tactics (trees : List InfoTree) : m (List TacticResult) :=
  trees.bind InfoTree.tactics |>.mapM
    fun ⟨ctx, stx, goals, pos, endPos⟩ => do
      let src := Format.pretty (← ppTactic ctx stx)
      return { proofState := (← ProofSnapshot.create ctx none none goals), pos, endPos, src, stx }
where ppTactic (ctx : ContextInfo) (stx : Syntax) : IO Format :=
  ctx.runMetaM {} try
    Lean.PrettyPrinter.ppTactic ⟨stx⟩
  catch _ =>
    pure "<failed to pretty print>"

def sorries (trees : List InfoTree) (env? : Option Environment) : m (List SorryResult) := do
  trees.bind InfoTree.sorries |>.filterMapM
    fun ⟨ctx, g, pos, endPos⟩ => do
      match g with
      | .tactic g => do
        pure <| some { proofState := (← ProofSnapshot.create ctx none env? [g]), pos, endPos }
      | .term lctx (some t) => do
        pure <| some { proofState := (← ProofSnapshot.create ctx lctx env? [] [t]), pos, endPos }
      | .term _ none =>
        pure none

structure ProofStepResponse where
  proofState : ProofSnapshot
  messages : List Lean.Message := []
  sorries : List SorryResult := []
  traces : List String := []

def ProofSnapshot.diff (proofState : ProofSnapshot) (old? : Option ProofSnapshot := none) :
    m ProofStepResponse := do
  let messages := proofState.newMessages old?
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
  return {
    proofState
    messages
    sorries
    traces }

structure CommandResponse where
  source : String
  stx : Syntax
  env : Nat
  messages : List Lean.Message := []
  sorries : List SorryResult := []
  tactics : List TacticResult := []
  infotree : List InfoTree := []
  proofs : List Proof := []

inductive InfoTreeOption
| none
| full
| by
| tactics
| original
| substantive

/--
Run a command, returning the id of the new environment, and any messages and sorries.

Base environment:
* If `after? = some i`,
  then the command is run using the `Environment` produced after the command at index `i`.
* If `after? = none`, and `replace? = some j`,
  then the command is run using the `Environment` produced after the parent of the command at index `j`.
* If `after? = none` and `replace? = none`,
  then the command is run in a new environment. (This is the only way to use `import` commands.)

Incrementality:
* If `incr? = none`, then we use the most recently generated incrementality state from the base environment
  as selected above. In particular, if we have not previously run a command from the same base environment,
  then there will be no incrementality.
* If `incr? = some k`, then the command is run using the incrementality state from the command at index `k`,
  regardless of whether that is compatible with the base environment.
  (Incompatibilities should just result in the incrementality state not being used.)
  This is typically only needed when you are trying out multiple next continuations from the same base environment,
  and want to re-use incrementality state from a continuation before the most recent one.

Replacing source code:
* If `replace? = none`, then the code is the source code associated to `after?`, followed by the new command.
* If `replace? = some l`, then the code is the source code associated to the base environment, followed by the new command,
  followed by any source code that follows the command at index `l`.
  This source code following the command at index `l` is also re-executed along with the new command.

Returns either
* a list of `CommandResponse`s (one for each command in the execute source code)
* an error message

By default the `CommandResponse`s only include information about the `sorry`s in the code,
not all tactic invocations. -- FIXME this will probably change

By default the `CommandResponse`s do not contain the full `InfoTree`s. Setting `infotree` to
* `none` results in no `InfoTree`s being included
-/
def runCommand (cmd : String)
    (after? : Option Nat := none) (replace? : Option Nat := none) (incr? : Option Nat := none)
    (allTactics : Bool := false) (infotree : InfoTreeOption := .none) :
    M IO (List CommandResponse ⊕ String) := do
  let (retrieved?, parentId?, additionalSource) ← match ← retrieve after? replace? with
  | .inr e => return .inr e
  | .inl none => pure (none, none, "")
  | .inl (some x) => pure (some x.1, some x.2.1, x.2.2)

  let (incrementalStateBefore?, notFound) ← do
    match incr? with
    | none => pure (← findLatestIncrementalState after?, false)
    | some j => do match  ← lookup? j with
      | some { incrementalState? := some s, .. } => pure (some s, false)
      | some _
      | none => pure (none, true)
  if notFound then
    return .inr s!"Unknown incremental state {incr?.get!}"

  let initialCmdSnapshot? := (·.snapshot) <$> retrieved?
  let initialContext :=
    (initialCmdSnapshot?.map fun c => c.cmdContext).getD
      { fileName := "", fileMap := default, tacticCache? := none, snap? := none }
  let initialCmdState? := initialCmdSnapshot?.map fun c => c.cmdState
  let initialEnv? := initialCmdState?.map (·.env)

  let (header?, states) ← try
    IO.processInput (cmd ++ "\n" ++ additionalSource) initialCmdState? incrementalStateBefore?
  catch ex =>
    return .inr ex.toString

  -- Drop the "end of input" state.
  let states := states.filter fun s => match s.commands.back? with | none => true | some stx => stx.getKind ≠ ``Lean.Parser.Command.eoi
  let states : List (Command.State × Syntax × Option IncrementalState) :=
    (match header? with | none => [] | some (headerState, headerSyntax) => if isEmptyModuleHeader headerSyntax then [] else [(headerState, headerSyntax, none)]) ++
      states.map fun state => (state.commandState, state.commands.back?.get!, some state)

  let (_, results) ← states.foldlM (init := (parentId?, #[])) fun (p, r) ⟨state, stx, incr⟩ => do
    let src ← source initialContext state stx
    let i ← record p initialContext state stx src incr
    let n ← mkResponse i initialEnv? allTactics infotree state src stx
    pure (n.env, r.push n)
  return .inl results.toList
where
  isEmptyModuleHeader (stx : Syntax) : Bool :=
    stx.isOfKind ``Parser.Module.header && match stx.getArgs with
    | #[prelude, imports] => prelude.getArgs.size = 0 && imports.getArgs.size = 0
    | _ => false
  source (ctx : Context) (cmdState : Command.State) (stx : Syntax) : M IO String := do
    let (format, _) ← Command.CommandElabM.toIO (do liftCoreM <| PrettyPrinter.ppCommand ⟨stx⟩) ctx cmdState -- FIXME this should be the Command.State before, not after?!
    return toString format
  record (parentId? : Option Nat) (cmdContext : Context) (cmdState : Command.State)
      (stx : Syntax) (source : String) (incrementalState? : Option IncrementalState) : M IO Nat := do
    let cmdSnapshot :=
    { cmdState
      cmdContext }
    recordCommandSnapshot parentId? source stx cmdSnapshot incrementalState?
  mkResponse
      (env : Nat) (initialEnv : Option Environment) (allTactics : Bool) (infotrees : InfoTreeOption)
      (cmdState : Command.State) (source : String) (stx : Syntax) : M IO CommandResponse := do
    let messages := cmdState.messages.msgs.toList
    let trees := cmdState.infoState.trees.toList
    -- For debugging purposes, sometimes we print out the trees here:
    -- trees.forM fun t => do IO.println (← t.format)
    let sorries ← sorries trees initialEnv
    let tactics ← if allTactics then tactics trees else pure []
    let byTrees := (·.1) <$> trees.bind InfoTree.byTrees
    let proofs := byTrees.filterMap fun t => Proof.ofInfoTree t
    let infotree := match infotrees with
    | .full => trees
    | .by => trees.bind InfoTree.retainBy
    | .tactics => trees.bind InfoTree.retainTacticInfo
    | .original => trees.bind InfoTree.retainTacticInfo |>.bind InfoTree.retainOriginal
    | .substantive => trees.bind InfoTree.retainTacticInfo |>.bind InfoTree.retainSubstantive
    | .none => []
    return {
      source,
      stx,
      env,
      messages,
      sorries,
      tactics
      infotree,
      proofs }
