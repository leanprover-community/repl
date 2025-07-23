-- This theorem demonstrates function composition/transitivity of implication
-- It shows that if P implies Q, and Q implies R, then P implies R
theorem demo (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  -- Introduce the hypotheses and antecedent:
  -- h1: P → Q    h2: Q → R    p: P
  intro h1 h2 p

  -- First prove Q using h1 and p
  have q : Q := by
    apply h1
    aesop  -- aesop from Mathlib

  -- Then use h2 and the proven Q to get R
  apply h2
  sorry  -- Need to prove Q here
