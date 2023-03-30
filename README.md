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
   "type mismatch
  rfl
has type
  f = f : Prop
but is expected to have type
  f = 2 : Prop"}],
 "env": 6}
```

showing any messages generated, or sorries with their goal states.

Information is generated for tactic mode sorries,
but currently not for term mode sorries.
