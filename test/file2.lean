def a : Nat := 37
def b : Nat := 37

theorem h1 : a = b := rfl

theorem h (x y z : Nat) : x + y + (z + a) = x + (z + b + y) := by
  rw [Nat.add_assoc, Nat.add_comm y, h1]
