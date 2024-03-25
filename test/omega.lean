example {x y z : Nat} (_ : x - y - z = 0) (_ : x > y + z) : False := by sorry

example {x y : Nat} (_ : x / 2 - y / 3 < 1) (_ : 3 * x ≥ 2 * y + 4) : False := by sorry

example {x : Nat} : 1 < (1 + ((x + 1 : Nat) : Int) + 2) / 2 := by sorry

example {x : Nat} (_ : 10000 ∣ x) (_ : ¬ 100 ∣ x) : False := by sorry

example (x : Nat) : x % 1024 - x % 2048 = 0 := by sorry
