import Lean

/-! Inspired by Jixia examples -/

open IO in
def hello : IO Unit :=
  println "Hello, world!"

universe u
variable {α : Type u}

theorem eq_trans_sym {a b c : α} : a = b → b = c → c = a := by
  intro h₁ h₂
  rw [h₁, h₂]

/-- Docstring test
pow' x n = x ^ (n + 1) -/
def pow' [Mul α] (x : α) : Nat → α
  | .zero => x
  | .succ n => pow' x n * x

structure FermatTriple (k : Nat) : Type where
  x : Nat
  y : Nat
  z : Nat
  eqn : x ^ k + y ^ k = z ^ k

example : FermatTriple 2 := ⟨ 3, 4, 5, rfl ⟩

namespace Demo

inductive MyType
  | val

scoped infix:68 " ≋ " => BEq.beq

scoped instance : BEq MyType where
  beq _ _ := true

end Demo


section

open scoped Demo

def open_scoped_test1 : IO Unit := do
  let x : Demo.MyType := Demo.MyType.val
  let y : Demo.MyType := Demo.MyType.val
  if x ≋ y then
    IO.println "x and y are equal"
  else
    IO.println "x and y are not equal"
end

section

private def private_test (a : Nat) : Nat :=
  a * a

private noncomputable def non_computable_test (a : Nat) : Nat := a

namespace Example
/--
 dododo-/
protected partial def prot_part_def (a : Nat) : Nat := a
end Example

@[simp, instance] def t : Nat := 42

variable {β : Type u}
public def public_test (a : Nat) : Nat :=
  a + t
