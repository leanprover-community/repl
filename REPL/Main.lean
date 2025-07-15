/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.Basic
import REPL.Frontend
import REPL.Util.Path
import REPL.Lean.ContextInfo
import REPL.Lean.Environment
import REPL.Lean.InfoTree
import REPL.Lean.InfoTree.ToJson
import REPL.Snapshots
import REPL.Actions

/-!
# A REPL for Lean.

Communicates via JSON on stdin and stdout. Commands should be separated by blank lines.

Commands may be of the form
```
{ "cmd" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```
or
```
{ "cmd" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form
```
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "\n⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
 ```
 showing any messages generated, or sorries with their goal states.
 Information is generated for tactic mode sorries, but not for term mode sorries.
-/

open Lean Elab

open REPL Actions

/-- Get lines from stdin until a blank line is entered. -/
partial def getLines : IO String := do
  let line ← (← IO.getStdin).getLine
  if line.trim.isEmpty then
    return line
  else
    return line.trimRight ++ (← getLines)

local instance [ToJson ε] [ToJson α] : ToJson (Except ε α) where
  toJson
  | .error e => toJson e
  | .ok a => toJson a

def makeFromJson_Input (input_name : Ident) : Command.CommandElabM Unit := do
  let .inductInfo info ← getConstInfo input_name.getId | throwError "type is not an inductive type"
  if info.numCtors = 0 then
    throwError "type must have at least one constructor"
  if info.numParams != 0 then
    throwError "type must have no type parameters"
  if info.numIndices != 0 then
    throwError "type must have no indices"
  let ctors ← info.ctors.mapM getConstInfo
  let ts ← ctors.mapM fun c => do
    let type := c.type.consumeMData
    if h : type.isForall then
      let arity := type.getForallArity
      if arity != 1 then
        throwError "constructor {MessageData.ofConstName c.name} has non-singular arity, got {arity}"
      return type.forallDomain h
    else
      throwError "constructor {MessageData.ofConstName c.name} has non-singular arity, got 0"
  let br ← (ctors.zip ts).mapM fun (x, y) => do
    let t ← Command.runTermElabM fun _ => PrettyPrinter.delab y
    `($(mkIdent x.name):ident <$> tryThe $t)
  let br := br.reverse
  let ctors ← match br with
    | [] => unreachable!
    | [x] => pure x
    | x :: tail => tail.foldlM (init := x) fun r l => `($l <|> $r)
  let code ← `(command|
    instance : FromJson $input_name where
      fromJson? json := do
        let rec @[specialize, always_inline] tryThe (α : Type) [FromJson α] : Except String α := fromJson? (α := α) json
        $ctors:term)
  trace[REPL.mkInput] "{code}"
  Command.elabCommand code

local elab "#mkInput " colGt input_name:ident : command => do
  let names ← Attr.getAllReplRequests
  let cs ← names.mapM fun (t, c) =>
    `(Parser.Command.ctor| | $(mkIdent c):ident : $(mkIdent t):ident → $input_name)
  let code ← `(command|
    /-- Commands accepted by the REPL. -/
    inductive $input_name where
    $cs*)
  trace[REPL.mkInput] "{code}"
  Command.elabCommand code
  makeFromJson_Input input_name

#mkInput Input

local syntax (name := makeReplDispatch) "make_repl_dispatch% " colGt term : term

@[local term_elab makeReplDispatch]
def elabMakeReplDispatch : Term.TermElab := fun stx type? => do
  let `(make_repl_dispatch% $input) := stx | throwUnsupportedSyntax
  let requests ← Attr.getAllReplRequests
  let rs := RBTree.fromArray requests.unzip.fst Name.cmp
  let handlers ← Attr.getAllReplRequestHandlers
  let (r, cf) := handlers.unzip.snd.unzip
  let r := RBTree.fromArray r Name.cmp
  for d in RBTree.diff rs r do -- short-circuit by the first throw
    throwError "no handler found for request type {MessageData.ofConstName d}"
  let (c, f) := cf.unzip
  let c := c.map mkIdent
  let toJson := mkIdent ``toJson
  let toJsons := Array.replicate c.size toJson
  let s ← `(
    match $input:term with
    $[| .$c:ident r => $toJsons <$> ($f:term r)]*
    )
  trace[REPL.make_repl_dispatch] "{s}"
  Term.withMacroExpansion stx s do
    Term.elabTerm s type?

/-- Parse a user input string to an input command. -/
def parse (query : String) : IO Input := do
  let json? := Json.parse query
  match json? with
  | .error e => throw <| IO.userError <| toString <| toJson <|
      (⟨"Could not parse JSON:\n" ++ e⟩ : Actions.Error)
  | .ok j =>
    match fromJson? (α := Input) j with
    | .error e => throw <| IO.userError <| toString <| toJson <|
        (⟨"Could not parse as a valid JSON command:\n" ++ e⟩ : Actions.Error)
    | .ok r => return r

/-- Avoid buffering the output. -/
def printFlush [ToString α] (s : α) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (toString s)
  out.flush -- Flush the output

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit :=
  loop.run' {}
where loop : M Unit := do
  let query ← getLines
  if query = "" then
    return ()
  if query.startsWith "#" || query.startsWith "--" then loop else
  let input ← parse query
  let response ← make_repl_dispatch% input
  IO.println <| toString response
  printFlush "\n" -- easier to parse the output if there are blank lines
  loop

/-- Main executable function, run as `lake exe repl`. -/
unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot)
  repl
