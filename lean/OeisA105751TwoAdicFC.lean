import FormalConjectures.OEIS.«105751»

/-!
# OEIS A105751: the exact Formal Conjectures 2-adic target

This file deliberately targets only `OeisA105751.conjecture`.  The separate theorem for odd
primes congruent to `1 mod 4` is not claimed here.

The file is a proof scaffold: it records the exact current target and the stronger four-class
valuation statement from which that target is intended to follow.  It does not reuse the imported
open theorem as if it were a proof.
-/

open Complex Filter Topology Nat

namespace A105751TwoAdic

noncomputable section

/-- The exact proposition of `OeisA105751.conjecture` on the pinned Formal Conjectures commit. -/
def formalConjecturesTarget : Prop :=
  Tendsto
    (fun n ↦ (4 : ℚ) * (padicValInt 2 (OeisA105751.a n) : ℚ) / (n : ℚ))
    atTop (nhds 1)

/-- `formalConjecturesTarget` is definitionally the current registered statement. -/
theorem formalConjecturesTarget_eq_current :
    formalConjecturesTarget ↔
      Tendsto
        (fun n ↦ (4 : ℚ) * (padicValInt 2 (OeisA105751.a n) : ℚ) / (n : ℚ))
        atTop (nhds 1) :=
  Iff.rfl

/-- The natural-number ceiling `⌈m/2⌉`. -/
def halfCeil (m : ℕ) : ℕ :=
  (m + 1) / 2

/--
The stronger four-residue-class formula reported for the nonzero terms of A105751.

The last two clauses start at `m = 1`, excluding the zero terms `a 0` and `a 3`.
This proposition is the central remaining arithmetic proof obligation.
-/
def exactFourClassValuationFormula : Prop :=
  (∀ m : ℕ, padicValInt 2 (OeisA105751.a (4 * m + 1)) = m) ∧
  (∀ m : ℕ, padicValInt 2 (OeisA105751.a (4 * m + 2)) = m) ∧
  (∀ m : ℕ, 1 ≤ m →
    padicValInt 2 (OeisA105751.a (4 * m)) =
      m + 2 + padicValInt 2 (halfCeil m : ℤ)) ∧
  (∀ m : ℕ, 1 ≤ m →
    padicValInt 2 (OeisA105751.a (4 * m + 3)) =
      m + 3 + padicValInt 2 (halfCeil m : ℤ))

-- The exact open declaration whose proof this project is intended to supply.
#check OeisA105751.conjecture

-- Explicitly outside the scope of this project.
#check OeisA105751.conjecture.variants.moll_p_mod_4_eq_1

#print axioms formalConjecturesTarget_eq_current

end


end A105751TwoAdic
