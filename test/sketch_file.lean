theorem add_comm_proved_formal_sketch : ∀ n m : Nat, n + m = m + n := by
  intros n m
  induction n with
    | zero =>
      have h_base: 0 + m = m := sorry
      have h_symm: m + 0 = m := sorry
      sorry
    | succ n ih => sorry

theorem add_rfl : ∀ n m : Nat, n + m = n + m := by intros; rfl
theorem add_rfl2 : ∀ n m : Nat, n + m = n + m := by sorry
