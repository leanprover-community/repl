import Lean

open Lean Elab Lean.Parser.Tactic

namespace Proof

/-- The metavariable context and goals observed at some point in a proof. -/
structure State where
  mctx : MetavarContext
  goals : List MVarId

/-- The goals both before and after a proof step. -/
structure Goals where
  before : State
  after : State

/-- The syntax of a proof step, and if already observed, the goals before and after. -/
structure Step where
  stx : Syntax
  goals? : Option Goals := none

def Step.ofTacticInfo (i : TacticInfo) : Step where
  stx := i.stx
  goals? := some <|
  { before := { mctx := i.mctxBefore, goals := i.goalsBefore },
    after := { mctx := i.mctxAfter, goals := i.goalsAfter} }

end Proof

open Proof

/--
An inductive type representing a structured proof script.

The constructors do not exhaustively represent possible structuring tactics:
as a fallback some blocks will be represented by `atom`.
-/
inductive Proof where
  | atom : Step → Proof
  | tacticSeq : Step → Array Proof → Proof
  | cdot : Step → Proof → Proof
namespace Proof

instance : Inhabited Proof := ⟨.atom { stx := .missing }⟩

def step : Proof → Step
  | atom d => d
  | tacticSeq d _ => d
  | cdot d _ => d

-- -- We're probably not going to use this: reading the `InfoTree` immediately is easier than
-- -- doing one pass on the Syntax and then trying to merge in the `InfoTree` data.
-- partial def ofSyntax (stx : Syntax) : Proof :=
--   match stx with
--   | Syntax.node _ ``tacticSeq #[Syntax.node _ ``tacticSeq1Indented ps] =>
--     .tacticSeq { stx } (ps.map ofSyntax)
--   | Syntax.node _ _ _  => atom { stx }
--   | _ => unreachable!

-- def ofString (s : String) : CoreM Proof := do
--   match Parser.runParserCategory (← getEnv) `tactic s with
--   | .ok stx => pure (ofSyntax stx)
--   | .error _ => throwError "failed to parse tactic string"

partial def ofInfoTree (tree : InfoTree) : Option Proof :=
  match tree with
  | .node (.ofTacticInfo info) children =>
    let step := .ofTacticInfo info
    match info.stx with
    | Syntax.node _ ``Lean.Parser.Term.byTactic _
    | Syntax.node _ ``Lean.Parser.Tactic.tacticSeq _
    | Syntax.atom _ "by" =>
      match children.toList with
      | [t] => ofInfoTree t
      | _ => none -- malformed: should have exactly one child
    | Syntax.node _ ``Lean.Parser.Tactic.tacticSeq1Indented _ =>
      .some (.tacticSeq step (children.toList.filterMap ofInfoTree).toArray)
    | Syntax.node _ ``_root_.cdot _ =>
      match children.toList with
      | [_, c] =>
        match ofInfoTree c with
        | some p => .some (.cdot step p)
        | none => none
      | _ => none
    | _ => .some (.atom step)
  | _ => none

-- partial def ppRaw (p : Proof) : String :=
--   match p with
--   | atom d => ".raw: " ++ toString d.stx
--   | tacticSeq _ ps => ".tacticSeq\n" ++ (ps.map ppRaw).foldl (· ++ "\n  " ++ ·) "  "
--   | cdot _ p => ".cdot\n" ++ ppRaw p

partial def pp (p : Proof) : String :=
  match p with
  | atom d => d.stx.reprint.get!
  | tacticSeq _ ps => "{" ++ (ps.map pp).foldl (· ++ "; " ++ ·) "" ++ "}"
  | cdot _ p => "· " ++ pp p

end Proof

open Proof
