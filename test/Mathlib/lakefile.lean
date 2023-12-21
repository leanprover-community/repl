import Lake
open Lake DSL

package «repl-mathlib-tests» where
  -- add package configuration options here
  require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "nightly-testing-2023-12-20"

lean_lib «ReplMathlibTests» where
  -- add library configuration options here
