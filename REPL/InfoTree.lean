/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# Code to move (eventually) to core.

Mostly additional functions to deal with `InfoTree`.
-/

open Lean Elab Meta

namespace Lean.Syntax

/-- Check if a `Syntax` is an explicit invocation of the `sorry` tactic. -/
def isSorryTactic (stx : Syntax) : Bool :=
  s!"{stx}" = "(Tactic.tacticSorry \"sorry\")"

/-- Check if a `Syntax` is an explicit `sorry` term. -/
def isSorryTerm (stx : Syntax) : Bool :=
  s!"{stx}" = "(Term.sorry \"sorry\")"

end Lean.Syntax

namespace Lean.Elab

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.Elab

namespace Lean.Elab.InfoTree

/-- Analogue of `Lean.Elab.InfoTree.findInfo?`, but that returns all results. -/
partial def findAllInfo (t : InfoTree) (ctx : Option ContextInfo) (p : Info → Bool) :
    List (Info × Option ContextInfo) :=
  match t with
  | context ctx t => t.findAllInfo ctx p
  | node i ts  => (if p i then [(i, ctx)] else []) ++ ts.toList.bind (fun t => t.findAllInfo ctx p)
  | _ => []

/-- Return all `TacticInfo` nodes in an `InfoTree`
corresponding to explicit invocations of the `sorry` tactic,
each equipped with its relevant `ContextInfo`. -/
def findSorryTacticNodes (t : InfoTree) : List (TacticInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
  | .ofTacticInfo i => i.stx.isSorryTactic
  | _ => false
  infos.filterMap fun p => match p with
  | (.ofTacticInfo i, some ctx) => (i, ctx)
  | _ => none

/-- Return all `TermInfo` nodes in an `InfoTree`
corresponding to explicit `sorry` terms,
each equipped with its relevant `ContextInfo`. -/
def findSorryTermNodes (t : InfoTree) : List (TermInfo × ContextInfo) :=
  let infos := t.findAllInfo none fun i => match i with
  | .ofTermInfo i => i.stx.isSorryTerm
  | _ => false
  infos.filterMap fun p => match p with
  | (.ofTermInfo i, some ctx) => (i, ctx)
  | _ => none

inductive SorryType
| tactic : MVarId → SorryType
| term : LocalContext → Option Expr → SorryType

/--
Finds all appearances of `sorry` in an `InfoTree`, reporting
* the `ContextInfo` at that point,
* the `MVarId` for a goal that was closed by `sorry`,
  or the `Option Expr` expected type for a term supplied by `sorry`
* and the start and end positions of the `sorry` in the file.
-/
def sorries (t : InfoTree) : List (ContextInfo × SorryType × Position × Position) :=
  (t.findSorryTacticNodes.map fun ⟨i, ctx⟩ =>
    ({ ctx with mctx := i.mctxBefore }, .tactic i.goalsBefore.head!, stxRange ctx.fileMap i.stx)) ++
  (t.findSorryTermNodes.map fun ⟨i, ctx⟩ =>
    (ctx, .term i.lctx i.expectedType?, stxRange ctx.fileMap i.stx))

end Lean.Elab.InfoTree
