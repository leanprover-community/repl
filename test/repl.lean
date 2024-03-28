import REPL.JSON.REPL

open REPL

def no_such_file : M IO Unit := do
  let r ← handleFileRequest { path := "test/no_such_file.lean" }
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
  let r ← handleFileRequest { path := "test/file.lean" }
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

def run_command : M IO Unit := do
  match ← runCommand (infotree := .full) "def x := 1\ndef y := 2\ntheorem h : x + 1 = 2 := by\n  by_cases h : 0 < 1\n  · have z := 4\n    have z' := by sorry\n  · sorry" with
  | .inl r => do
    IO.println s!"{r.length} results"
    if h : r.length = 3 then
        -- IO.println r[2].stx
        IO.println r[2].proofs.length
        for p in r[2].proofs do
          IO.println p.ppRaw
        -- IO.println r[2].infotree.length
        -- IO.println <| ← (r[2].infotree.toArray.mapM fun t => do pure <| toString (← t.format))
        -- IO.println <| Lean.Json.arr (← r[2].infotree.toArray.mapM fun t => t.toJson none)
  | .inr e => IO.println s!"Error: {e}"

/--
info: 3 results
Source looks correct.
-/
#guard_msgs in
#eval run_command.run' {}
