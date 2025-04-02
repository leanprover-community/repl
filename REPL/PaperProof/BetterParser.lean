/-
MIT License

Copyright (c) 2023 Anton Kovsharov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-
Modified.
-/

import Lean
import Lean.Meta.Basic
import Lean.Meta.CollectMVars
import REPL.Lean.InfoTree.ToJson
import REPL.JSON

open Lean Elab Server REPL

namespace PaperProof

def stepGoalsAfter (step : ProofStepInfo) : List GoalInfo := step.goalsAfter ++ step.spawnedGoals

def noInEdgeGoals (allGoals : Std.HashSet GoalInfo) (steps : List ProofStepInfo) : Std.HashSet GoalInfo :=
  -- Some of the orphaned goals might be matched by tactics in sibling subtrees, e.g. for tacticSeq.
  (steps.bind stepGoalsAfter).foldl Std.HashSet.erase allGoals

/-
  Instead of doing parsing of what user wrote (it wouldn't work for linarith etc),
  let's do the following.
  We have assigned something to our goal in mctxAfter.
  All the fvars used in these assignments are what was actually used instead of what was in syntax.
-/
def findHypsUsedByTactic (goalId: MVarId) (goalDecl : MetavarDecl) (mctxAfter : MetavarContext) : MetaM (List String) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []

  -- Need to instantiate it to get all fvars
  let fullExpr ← instantiateExprMVars expr
  let fvarIds := (collectFVars {} fullExpr).fvarIds
  let fvars := fvarIds.filterMap goalDecl.lctx.find?
  let proofFvars ← fvars.filterM (Meta.isProof ·.toExpr)
  -- let pretty := proofFvars.map (fun x => x.userName)
  -- dbg_trace s!"Used {pretty}"
  return proofFvars.map (fun x => x.fvarId.name.toString) |>.toList

-- This is used to match goalsBefore with goalsAfter to see what was assigned to what
def findMVarsAssigned (goalId : MVarId) (mctxAfter : MetavarContext) : MetaM (List MVarId) := do
  let some expr := mctxAfter.eAssignment.find? goalId
    | return []
  let (_, s) ← (Meta.collectMVars expr).run {}
  return s.result.toList


-- Returns unassigned goals from the provided list of goals
def getUnassignedGoals (goals : List MVarId) (mctx : MetavarContext) : IO (List MVarId) := do
  goals.filterMapM fun id => do
    if let none := mctx.findDecl? id then
      return none
    if mctx.eAssignment.contains id ||
       mctx.dAssignment.contains id then
      return none
    return some id

structure Result where
  steps : List ProofStepInfo
  allGoals : Std.HashSet GoalInfo

def getGoalsChange (ctx : ContextInfo) (tInfo : TacticInfo) : IO (List (List String × GoalInfo × List GoalInfo)) := do
  -- We want to filter out `focus` like tactics which don't do any assignments
  -- therefore we check all goals on whether they were assigned during the tactic
  let goalMVars := tInfo.goalsBefore ++ tInfo.goalsAfter
  -- For printing purposes we always need to use the latest mctx assignments. For example in
  -- have h := by calc
  --  3 ≤ 4 := by trivial
  --  4 ≤ 5 := by trivial
  -- at mctxBefore type of `h` is `?m.260`, but by the time calc is elaborated at mctxAfter
  -- it's known to be `3 ≤ 5`
  let printCtx := {ctx with mctx := tInfo.mctxAfter}
  let mut goalsBefore ← getUnassignedGoals goalMVars tInfo.mctxBefore
  let mut goalsAfter ← getUnassignedGoals goalMVars tInfo.mctxAfter
  let commonGoals := goalsBefore.filter fun g => goalsAfter.contains g
  goalsBefore := goalsBefore.filter (!commonGoals.contains ·)
  goalsAfter :=  goalsAfter.filter (!commonGoals.contains ·)
  -- We need to match them into (goalBefore, goalsAfter) pairs according to assignment.
  let mut result : List (List String × GoalInfo × List GoalInfo) := []
  for goalBefore in goalsBefore do
    if let some goalDecl := tInfo.mctxBefore.findDecl? goalBefore then
      let assignedMVars ← ctx.runMetaM goalDecl.lctx (findMVarsAssigned goalBefore tInfo.mctxAfter)
      let tacticDependsOn ← ctx.runMetaM goalDecl.lctx
          (findHypsUsedByTactic goalBefore goalDecl tInfo.mctxAfter)

      result := (
        tacticDependsOn,
        ← printGoalInfo printCtx goalBefore,
        ← goalsAfter.filter assignedMVars.contains |>.mapM (printGoalInfo printCtx)
      ) :: result
  return result

-- TODO: solve rw_mod_cast

def prettifySteps (stx : Syntax) (ctx : ContextInfo) (steps : List ProofStepInfo) : IO (List ProofStepInfo) := do
  let range := stx.toRange ctx
  let prettify (tStr : String) :=
    let res := tStr.trim.dropRightWhile (· == ',')
    -- rw puts final rfl on the "]" token
    -- TODO: is this correct for `rewrite`?
    if res == "]" then "rfl" else res
  -- Each part of rw is a separate step none of them include the initial 'rw [' and final ']'.
  -- So we add these to the first and last steps.
  let extractRwStep (steps : List ProofStepInfo) (atClause? : Option Syntax) : IO (List ProofStepInfo) := do
    -- If atClause is present, call toJson on it and retrieve the `pp` field.
    let atClauseStr? ← match atClause? with
      | some atClause => do
        let j ← atClause.toJson ctx (LocalContext.mkEmpty ())
        pure j.pp
      | none =>
        pure none

    -- Turn the `Option String` into a (possibly-empty) string so we can insert it.
    let maybeAtClause := atClauseStr?.getD ""   -- getD "" returns `""` if `atClauseStr?` is `none`
    let rwSteps := steps.map fun a =>
      { a with tacticString := s!"rw [{prettify a.tacticString}]{maybeAtClause}" }

    match rwSteps with
    | [] =>
      return []
    | [step] =>
      return [{ step with start := some range.start, finish := some range.finish }]
    | steps =>
      let first := { steps.head! with start := some range.start }
      let last := { steps.getLast! with finish := some range.finish }
      let middle := steps.drop 1 |>.dropLast
      return first :: middle ++ [last]

  match stx with
  | `(tactic| rw [$_,*] $(at_clause)?)
  | `(tactic| rewrite [$_,*] $(at_clause)?) =>
    extractRwStep steps at_clause
  | `(tactic| rwa [$_,*] $(at_clause)?) =>
    let rwSteps ← extractRwStep steps at_clause
    let assumptionSteps := (if rwSteps.isEmpty then [] else rwSteps.getLast!.goalsAfter).map fun g =>
      {
        tacticString := "assumption",
        infoTree := none,
        goalBefore := g,
        goalsAfter := [],
        mctxBefore := none,
        mctxAfter := none,
        tacticDependsOn := [],
        spawnedGoals := [],
        start := none,
        finish := none
      }
    return rwSteps ++ assumptionSteps
  | _ => return steps
-- Comparator for names, e.g. so that _uniq.34 and _uniq.102 go in the right order.
-- That's not completely right because it doesn't compare prefixes but
-- it's much shorter to write than correct version and serves the purpose.
def nameNumLt (n1 n2 : Name) : Bool :=
  match n1, n2 with
  | .num _ n₁, .num _ n₂ => n₁ < n₂
  | .num _ _,  _ => true
  | _, _ => false

partial def postNode (ctx : ContextInfo) (i : Info) (_: PersistentArray InfoTree) (res : List (Option Result)) : IO Result := do
    let res := res.filterMap id
    let some ctx := i.updateContext? ctx
      | panic! "unexpected context node"
    let steps := res.map (fun r => r.steps) |>.join
    let allSubGoals := Std.HashSet.empty.insertMany $ res.bind (·.allGoals.toList)
    if let .ofTacticInfo tInfo := i then
      -- shortcut if it's not a tactic user wrote
      -- \n trim to avoid empty lines/comments until next tactic,
      -- especially at the end of theorem it will capture comment for the next one
      let some tacticString := tInfo.stx.getSubstring?.map (·.toString)
        | return {steps, allGoals := allSubGoals}

      let infoTreeJson ← (InfoTree.node i PersistentArray.empty).toJson ctx

      let steps ← prettifySteps tInfo.stx ctx steps

      let proofTreeEdges ← getGoalsChange ctx tInfo
      let currentGoals := proofTreeEdges.map (fun ⟨ _, g₁, gs ⟩ => g₁ :: gs)  |>.join
      let allGoals := allSubGoals.insertMany $ currentGoals
      -- It's like tacticDependsOn but unnamed mvars instead of hyps.
      -- Important to sort for have := calc for example, e.g. calc 3 < 4 ... 4 < 5 ...
      let orphanedGoals := currentGoals.foldl Std.HashSet.erase (noInEdgeGoals allGoals steps)
        |>.toArray.insertionSort (nameNumLt ·.id.name ·.id.name) |>.toList

      let mctxBeforeJson ← MetavarContext.toJson tInfo.mctxBefore ctx
      let mctxAfterJson ← MetavarContext.toJson tInfo.mctxAfter ctx

      let newSteps := proofTreeEdges.filterMap fun ⟨ tacticDependsOn, goalBefore, goalsAfter ⟩ =>
       -- Leave only steps which are not handled in the subtree.
        if steps.map (·.goalBefore) |>.elem goalBefore then
          none
        else
          let range := tInfo.stx.toRange ctx
          some {
            tacticString,
            goalBefore,
            goalsAfter,
            mctxBefore := mctxBeforeJson,
            mctxAfter := mctxAfterJson,
            tacticDependsOn,
            spawnedGoals := orphanedGoals,
            start := range.start,
            finish := range.finish,
            infoTree := some infoTreeJson
          }

      return { steps := newSteps ++ steps, allGoals }
    else
      return { steps, allGoals := allSubGoals }

partial def BetterParser (i : InfoTree) := i.visitM (postNode := postNode)

end PaperProof
