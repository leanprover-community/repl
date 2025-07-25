import Lean
import REPL.Snapshots

open Lean Elab

namespace REPL

class MonadCommandSnapshots (m : Type → Type) where
  getCmdSnaps : m (Array CommandSnapshot)
  setCmdSnaps : Array CommandSnapshot → m Unit
  modifyGetCmdSnaps {α} : (Array CommandSnapshot → (α × Array CommandSnapshot)) → m α

class MonadProofSnapshots (m : Type → Type) where
  getProofSnaps : m (Array ProofSnapshot)
  setProofSnaps : Array ProofSnapshot → m Unit
  modifyGetProofSnaps {α} : (Array ProofSnapshot → (α × Array ProofSnapshot)) → m α

attribute [specialize] MonadCommandSnapshots.modifyGetCmdSnaps MonadProofSnapshots.modifyGetProofSnaps

class MonadREPL (m : Type → Type) extends MonadCommandSnapshots m, MonadProofSnapshots m where

export MonadCommandSnapshots (getCmdSnaps setCmdSnaps modifyGetCmdSnaps)
export MonadProofSnapshots (getProofSnaps setProofSnaps modifyGetProofSnaps)

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

-- /--
-- The Lean REPL monad.
-- -/
abbrev M : Type → Type := StateRefT State IO

@[inline]
instance : MonadREPL M where
  getCmdSnaps := State.cmdStates <$> get
  setCmdSnaps snaps := modify ({· with cmdStates := snaps})
  modifyGetCmdSnaps f := modifyGet fun x => let (a, v) := f x.cmdStates; (a, {x with cmdStates := v})
  getProofSnaps := State.proofStates <$> get
  setProofSnaps snaps := modify ({· with proofStates := snaps})
  modifyGetProofSnaps f := modifyGet fun x => let (a, v) := f x.proofStates; (a, {x with proofStates := v})

@[always_inline, specialize]
def modifyCmdSnaps [MonadCommandSnapshots m] : (Array CommandSnapshot → Array CommandSnapshot) → m Unit := fun f => modifyGetCmdSnaps fun x => ((), f x)

@[always_inline, specialize]
def modifyProofSnaps [MonadProofSnapshots m] : (Array ProofSnapshot → Array ProofSnapshot) → m Unit := fun f => modifyGetProofSnaps fun x => ((), f x)

@[inline]
instance {m n} [MonadLift m n] [MonadREPL m] : MonadREPL n where
  getCmdSnaps := MonadLift.monadLift (m := m) (n := n) getCmdSnaps
  setCmdSnaps snaps := MonadLift.monadLift (m := m) (n := n) <| setCmdSnaps snaps
  modifyGetCmdSnaps f := MonadLift.monadLift (m := m) (n := n) <| modifyGetCmdSnaps f
  getProofSnaps := MonadLift.monadLift (m := m) (n := n) getProofSnaps
  setProofSnaps snaps := MonadLift.monadLift (m := m) (n := n) <| setProofSnaps snaps
  modifyGetProofSnaps f := MonadLift.monadLift (m := m) (n := n) <| modifyGetProofSnaps f

namespace Attr

/-- Specify that a type is an repl request, and optionally its corresponding constructor name. -/
syntax (name := repl_request) &"repl_request " (ident)? : attr

/-- Specify a handler for a request. -/
syntax (name := repl_request_handler) &"repl_request_handler " ident : attr

private def validateReplRequestAttr : Name → Syntax → AttrM Name := fun name stx => do
  let `(attr| repl_request $[$cname?]?) := stx | throwUnsupportedSyntax
  if !name.isStr then
    throwError "type must have simple name"
  let .inductInfo info ← getConstInfo name | throwError "can only apply to an inductive/structure type"
  if info.numCtors = 0 then
    throwError "type must have at least one constructor"
  if info.numParams != 0 then
    throwError "type must have no type parameters"
  if info.numIndices != 0 then
    throwError "type must have no indices"
  let s := name.getString!.data
  let s := String.mk <| s[0]!.toLower :: s.tail
  let cname := cname?.map (fun x => x.getId) |>.getD (Name.mkStr1 s)
  return cname

initialize replRequestAttr : ParametricAttribute Name ←
  registerParametricAttribute {
      name := `repl_request
      descr := "the corresponding constructor name, optional"
      getParam := validateReplRequestAttr
  }

def getAllReplRequests [Monad m] [MonadEnv m] : m (Array (Name × Name)) := do
  let env ← getEnv
  let ext := replRequestAttr.ext
  let s := ext.toEnvExtension.getState env
  let imported := s.importedEntries
  let current := s.state.toArray
  return imported.flatMap id ++ current

open Meta in
private def validateReplRequestHandlerAttr : Name → Syntax → AttrM (Name × Name × Term) := fun name stx => do
  let `(attr| repl_request_handler $reqNameStx) := stx | throwUnsupportedSyntax
  let reqName ← resolveGlobalConstNoOverload reqNameStx
  addConstInfo reqNameStx reqName
  let env ← getEnv
  let some reqCtor := replRequestAttr.getParam? env reqName |
    throwErrorAt reqNameStx "type {MessageData.ofConstName reqName} has no attribute `repl_request`"
  let .defnInfo info ← getConstInfo name |
    throwError "this attribute can only be applied to a function"
  let fnType := info.type.consumeMData
  let arity := fnType.getForallArity
  if arity = 0 then
    throwError "type of {MessageData.ofConstName name} is not a function"
  if arity > 1 then
    let s ← `($(mkIdent name) ($(mkIdent `m) := $(mkIdent ``M)))
    return (reqName, reqCtor, s)
  let s ← `($(mkIdent name))
  return (reqName, reqCtor, s)

initialize replRequestHandlerAttr : ParametricAttribute (Name × Name × Term) ←
  registerParametricAttribute {
      name := `repl_request_handler
      descr := "the request type name"
      getParam := validateReplRequestHandlerAttr
  }

def getAllReplRequestHandlers [Monad m] [MonadEnv m] : m (Array (Name × Name × Name × Term)) := do
  let env ← getEnv
  let ext := replRequestHandlerAttr.ext
  let s := ext.toEnvExtension.getState env
  let imported := s.importedEntries
  let current := s.state.toArray
  return imported.flatMap id ++ current
