import Mathlib
open Real
open Nat
open BigOperators

/--
error: type mismatch
  h₀ x
has type
  p x = 2 - x ^ 2 : Prop
but is expected to have type
  p x = 6 / x * p x : Prop
---
error: unsolved goals
p q : ℝ → ℝ
h₀ : ∀ (x : ℝ), p x = 2 - x ^ 2
h₁ : ∀ (x : ℝ), x ≠ 0 → q x = 6 / x
hQ : ∀ (x : ℝ), p x = 6 / x
⊢ p (q 2) = -7
-/
#guard_msgs in
theorem mathd_algebra_35
  (p q : ℝ → ℝ)
  (h₀ : ∀ x, p x = 2 - x^2)
  (h₁ : ∀ x, x ≠ 0 -> q x = 6 / x) :
  p (q 2) = -7 := by
have hQ : ∀ x, p x = 6 / x := by
  intro x
  calc p x = 6 / x * p x := h₀ (x)
     _ = (6/2) * 6 / x * (6 / x) := sub_sub_sub_cancel sq_ne_zero
