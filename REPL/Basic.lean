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
