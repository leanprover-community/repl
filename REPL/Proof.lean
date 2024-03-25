import Lean

open Lean Lean.Parser.Tactic

inductive Proof where
  | raw : Syntax → Proof
  | list : Option Syntax → Array Proof → Proof

namespace Proof

instance : Inhabited Proof := ⟨raw .missing⟩

partial def toSyntax : Proof → Syntax
  | raw s => s
  | list stx? ps => stx?.getD <| Syntax.node .none ``tacticSeq (ps.map toSyntax)

partial def ofSyntax (stx : Syntax) : Proof :=
  match stx with
  | Syntax.node _ ``tacticSeq ps => .list stx (ps.map ofSyntax)
  | Syntax.node _ _ _  => raw stx
  | _ => unreachable!

def ofString (s : String) : CoreM Proof := do
  match Parser.runParserCategory (← getEnv) `tactic s with
  | .ok stx => pure (ofSyntax stx)
  | .error _ => throwError "failed to parse tactic string"

partial def ppRaw (p : Proof) : String :=
  match p with
  | raw s => ".raw" ++ toString s
  | list _ ps => ".list\n" ++ (ps.map ppRaw).foldl (· ++ "\n  " ++ ·) "  "

partial def pp (p : Proof) : String :=
  match p with
  | raw s => s.reprint.get!
  | list _ ps => "{" ++ (ps.map pp).foldl (· ++ "; " ++ ·) "" ++ "}"

end Proof

open Proof

#eval show MetaM _ from do IO.println (← ofString "{ cases x; sorry }").pp
