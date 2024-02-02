theorem foo (x : Int) : x = x := by
  by_cases h : x < 0
  next => rfl
  next => rfl
