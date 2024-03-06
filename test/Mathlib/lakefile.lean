import Lake
open Lake DSL

package «repl-mathlib-tests» where
  -- add package configuration options here
  require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.7.0-rc2"

@[default_target]
lean_lib «ReplMathlibTests» where
  globs := #[.submodules `test]
  -- add library configuration options here
