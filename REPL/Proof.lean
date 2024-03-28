import Lean

open Lean Elab Lean.Parser.Tactic

namespace Proof

structure State where
  mctx : MetavarContext
  goals : Array MVarId

structure Goals where
  before : State
  after : State

structure Data where
  stx : Syntax
  goals? : Option Goals := none

end Proof

open Proof

inductive Proof where
  | atom : Data → Proof
  | tacticSeq : Data → Array Proof → Proof
  | cdot : Data → Proof → Proof
namespace Proof

instance : Inhabited Proof := ⟨.atom { stx := .missing }⟩

def data : Proof → Data
  | atom d => d
  | tacticSeq d _ => d
  | cdot d _ => d

-- We're probably not going to use this: reading the `InfoTree` immediately is easier than
-- doing one pass on the Syntax and then trying to merge in the `InfoTree` data.
partial def ofSyntax (stx : Syntax) : Proof :=
  match stx with
  | Syntax.node _ ``tacticSeq #[Syntax.node _ ``tacticSeq1Indented ps] =>
    .tacticSeq { stx } (ps.map ofSyntax)
  | Syntax.node _ _ _  => atom { stx }
  | _ => unreachable!

def ofString (s : String) : CoreM Proof := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => pure (ofSyntax stx)
  | .error _ => throwError "failed to parse tactic string"

partial def ofInfoTree (tree : InfoTree) : Option Proof :=
  match tree with
  | .node (.ofTacticInfo { stx .. }) children =>
    match stx with
    | Syntax.node _ ``Lean.Parser.Term.byTactic _
    | Syntax.node _ ``Lean.Parser.Tactic.tacticSeq _
    | Syntax.atom _ "by" =>
      match children.toList with
      | [t] => ofInfoTree t
      | _ => none -- malformed: should have exactly one child
    | Syntax.node _ ``Lean.Parser.Tactic.tacticSeq1Indented _ =>
      -- TODO extract goal information
      .some (.tacticSeq { stx } (children.toList.filterMap ofInfoTree).toArray)
    | Syntax.node _ ``_root_.cdot _ =>
      match children.toList with
      | [_, c] =>
        match ofInfoTree c with
        | some p => .some (.cdot { stx } p)
        | none => none
      | _ => none
    | _ => .some (.atom { stx })
  | _ => none

partial def ppRaw (p : Proof) : String :=
  match p with
  | atom d => ".raw: " ++ toString d.stx
  | tacticSeq _ ps => ".tacticSeq\n" ++ (ps.map ppRaw).foldl (· ++ "\n  " ++ ·) "  "
  | cdot _ p => ".cdot\n" ++ ppRaw p

partial def pp (p : Proof) : String :=
  match p with
  | atom d => d.stx.reprint.get!
  | tacticSeq _ ps => "{" ++ (ps.map pp).foldl (· ++ "; " ++ ·) "" ++ "}"
  | cdot _ p => "· " ++ pp p

end Proof

open Proof
