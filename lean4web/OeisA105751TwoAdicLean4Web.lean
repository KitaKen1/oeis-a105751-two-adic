import Mathlib

#eval Lean.versionString

/-!
# OEIS A105751: standalone Lean4Web target

This file reproduces the current Formal Conjectures definition and exact 2-adic limit target using
mathlib only.  It is a compiling proof scaffold, not a completed proof of the open conjecture.
-/

open Complex Filter Topology Nat

namespace A105751TwoAdicLean4Web

noncomputable section

/--
The A105751 sequence: the imaginary part of `∏ k ∈ range (n+1), (1 + k i)`.
This is the definition currently used by Formal Conjectures.
-/
noncomputable def a (n : ℕ) : ℤ :=
  let productTerm (k : ℕ) : ℂ := 1 + (k : ℂ) * I
  Int.floor (((Finset.range (n + 1)).prod productTerm).im)

@[simp] theorem a_zero : a 0 = 0 := by
  delta a
  norm_num [Finset.prod]

@[simp] theorem a_one : a 1 = 1 := by
  delta a
  norm_num [Finset.prod]

@[simp] theorem a_two : a 2 = 3 := by
  delta a
  norm_num [Finset.prod]

@[simp] theorem a_three : a 3 = 0 := by
  delta a
  norm_num [Finset.prod]

@[simp] theorem a_four : a 4 = -40 := by
  delta a
  norm_num [Finset.prod]

/-- The exact 2-adic limit proposition registered in Formal Conjectures. -/
def formalConjecturesTarget : Prop :=
  Tendsto
    (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ))
    atTop (nhds 1)

/-- The natural-number ceiling `⌈m/2⌉`. -/
def halfCeil (m : ℕ) : ℕ :=
  (m + 1) / 2

/--
The stronger four-residue-class statement intended to imply `formalConjecturesTarget`.
The hypotheses on the last two clauses exclude the zero terms at indices `0` and `3`.
-/
def exactFourClassValuationFormula : Prop :=
  (∀ m : ℕ, padicValInt 2 (a (4 * m + 1)) = m) ∧
  (∀ m : ℕ, padicValInt 2 (a (4 * m + 2)) = m) ∧
  (∀ m : ℕ, 1 ≤ m →
    padicValInt 2 (a (4 * m)) = m + 2 + padicValInt 2 (halfCeil m : ℤ)) ∧
  (∀ m : ℕ, 1 ≤ m →
    padicValInt 2 (a (4 * m + 3)) = m + 3 + padicValInt 2 (halfCeil m : ℤ))

/-- A transparent check that the standalone target has the intended current shape. -/
theorem formalConjecturesTarget_unfold :
    formalConjecturesTarget ↔
      Tendsto
        (fun n ↦ (4 : ℚ) * (padicValInt 2 (a n) : ℚ) / (n : ℚ))
        atTop (nhds 1) :=
  Iff.rfl

#print axioms a_zero
#print axioms a_one
#print axioms a_two
#print axioms a_three
#print axioms a_four
#print axioms formalConjecturesTarget_unfold

end


end A105751TwoAdicLean4Web
