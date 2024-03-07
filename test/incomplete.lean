def f : Nat := by apply Nat.succ

def g (x : Bool) : Nat := by
  by_cases x
  { apply Nat.succ }
