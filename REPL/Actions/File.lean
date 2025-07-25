import REPL.Basic
import REPL.Actions.Basic
import REPL.Actions.Command

open Lean Elab InfoTree

namespace REPL.Actions

/-- Process a Lean file in a fresh environment if `env` is not provided. -/
@[repl_request]
structure File extends CommandOptions where
  env : Option Nat
  path : System.FilePath
deriving ToJson, FromJson

@[repl_request_handler File]
def processFile (s : File) : ResultT M CommandResponse := do
  try
    let cmd ← IO.FS.readFile s.path
    runCommand { s with env := s.env, cmd }
  catch e : IO.Error =>
    throw ⟨e.toString⟩
