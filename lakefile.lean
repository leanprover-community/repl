import Lake
open Lake DSL

package REPL {
  -- add package configuration options here
}

lean_lib REPL {
  -- add library configuration options here
}

-- Unfortunately the compiled version doesn't work: `unknown package 'Init'`
@[default_target]
lean_exe repl where
  root := `REPL.Main
  supportInterpreter := true