import Lake
open Lake DSL

package «repl-mathlib-tests» where
  -- add package configuration options here
  require mathlib from git "https://github.com/semorrison/mathlib4" @ "goal_normalization"

lean_lib «ReplMathlibTests» where
  -- add library configuration options here
