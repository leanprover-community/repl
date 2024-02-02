import Mathlib

theorem bar (x : Nat) : x = x := by
  induction x with
  | zero => sorry
  | succ n ih => sorry
