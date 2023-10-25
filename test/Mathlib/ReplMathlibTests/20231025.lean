import Mathlib.Data.Real.Basic

open Real

variable (x y : ℝ)
variable (f : ℝ → ℝ)

theorem problem (h0 : f 5 = 3) (h1 : f (4 * x * y) = 2 * y * (f (x + y) + f (x - y))) :
    ∃ (k : ℝ), f 2015 = k := by
  sorry
