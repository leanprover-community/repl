import Lake
open Lake DSL

package REPL {
  -- add package configuration options here
}

lean_lib REPL {
  -- add library configuration options here
}

@[default_target]
lean_exe repl where
  root := `REPL.JSON.REPL
  supportInterpreter := true
