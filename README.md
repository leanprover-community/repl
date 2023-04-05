# A read-eval-print-loop for Lean 4

Run using `./run`.
Communicates via JSON on stdin and stdout.
Commands should be separated by blank lines.
Commands may be of the form

```json
{ "cmd" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```

or

```json
{ "cmd" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form

```json
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
```

showing any messages generated, or sorries with their goal states.

Information is generated for tactic mode sorries,
but currently not for term mode sorries.

## Python package
This repository comes with `pylean`, a package that creates Python bindings for the repl. Currently, the python package depends on `pexpect`, and is therefore is only compatible with MacOS/Linux/FreeBSD systems.

To use the python bindings, first `cd` into the root directory of this repository and run `lake build`. Then, run `pip install pylean`. Now, you should be able to execute python scripts such as 
```python
from pylean import LeanServer

lean = LeanServer()

out = lean.run_code("example : 2 = 2 := rfl", verbose=True)

out1 = lean.run_code("def f := 37")

env_num = out1["env"]
out2 = lean.run_code("#check (rfl: f = 37)", env=env_num)

print(out2)
```

This should output
```
{ "cmd" : "example : 2 = 2 := rfl" }
{"sorries": [], "messages": [], "env": 0}
{'sorries': [], 'messages': [{'severity': 'info', 'pos': {'line': 1, 'column': 0}, 'endPos': {'line': 1, 'column': 6}, 'data': 'rfl : f = f'}], 'env': 2}
```
Running Lean programs that `import Mathlib` is a common use case. To enable `mathlib4` imports, simply add the following to `lakefile.lean` and run `lake exe cache get` before running `lake build`.
```
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```
