import REPL.Main

open REPL

def no_such_file : M IO Unit := do
  let r ← processFile { path := "test/no_such_file.lean" }
  match r with
  | .inl _ => IO.println "Success"
  | .inr error => IO.println s!"Error: {error.message}"

/--
info: Error: no such file or directory (error code: 2)
  file: test/no_such_file.lean
-/
#guard_msgs in
#eval no_such_file.run' {}

def process_file : M IO Unit := do
  let r ← processFile { path := "test/file.lean" }
  match r with
  | .inl r =>
    IO.println s!"{r.results.length} results"
    for r in r.results do
      IO.println s!"env {r.env}:\n{r.source}"
  | .inr error => IO.println s!"Error: {error.message}"

/--
info: 3 results
env 0:
def f : Nat :=
  37
env 1:
def g :=
  2
env 2:
theorem h : f + g = 39 := by exact rfl
-/
#guard_msgs in
#eval process_file.run' {}