import Std.Tactic.Simpa

example : False := by
  simpa using show False by done
