import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Complex.Exponential
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.Nat.Digits
import Mathlib.Tactic.NormNum.GCD

open BigOperators
open Real
open Nat
open Topology

theorem mathd_numbertheory_188 : Nat.gcd 180 168 = 12 := by norm_num

theorem mathd_numbertheory_403 : ∑ k in (Nat.properDivisors 198), k = 270 := by simp (config := {decide := true})

theorem mathd_numbertheory_109 (v : ℕ → ℕ) (h₀ : ∀ n, v n = 2 * n - 1) : (∑ k in Finset.Icc 1 100, v k) % 7 = 4 := by simp_rw (config := {decide := true}) [h₀]
