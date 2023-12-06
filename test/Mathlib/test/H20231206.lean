import Mathlib
import Mathlib.Tactic.GoalNormalization.NormalizeHyps

/--
info: theorem extracted_1 (h0 : ZMod (11 ^ 2)) (h1 : h0 = 24⁻¹) : ∃ k, h0 = k := sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem problem
    (b :  ZMod (11^2))
    (h₀ : b = 24⁻¹) :
    ∃ (k : ZMod (11^2)), b = k := by
  normalize_hyps
  extract_goal
  sorry
