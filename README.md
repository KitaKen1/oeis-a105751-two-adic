# OEIS A105751: the 2-adic asymptotic

This repository contains a Lean proof of the **2-adic asymptotic target**
registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/105751.lean).

Try it in Lean4Web:
[Open the standalone formalization in Lean4Web](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Foeis-a105751-two-adic%2Frefs%2Fheads%2Fmain%2Flean4web%2FOeisA105751TwoAdicLean4Web.lean)

The sequence is

```text
a(n) = Im ∏_{k=0}^n (1 + k i),    i² = -1.
```

The exact Formal Conjectures target is

```lean
theorem OeisA105751.conjecture :
    Tendsto
      (fun n ↦ (4 : ℚ) * (padicValInt 2 (OeisA105751.a n) : ℚ) / (n : ℚ))
      atTop (nhds 1)
```

In ordinary notation, it states

```text
ν₂(a(n)) ~ n / 4.
```

## Status

**Solved locally and checked by Lean.** The proof establishes the four exact residue-class
valuation formulas and derives the registered limit. The Formal Conjectures version proves the
target directly; it does not invoke the imported open declaration.

The proof gives the stronger formulas, away from the zero terms
`a(0) = a(3) = 0`:

```text
ν₂(a(4m+1)) = m,                         m ≥ 0,
ν₂(a(4m+2)) = m,                         m ≥ 0,
ν₂(a(4m))   = m + 2 + ν₂(⌈m/2⌉),        m ≥ 1,
ν₂(a(4m+3)) = m + 3 + ν₂(⌈m/2⌉),        m ≥ 1.
```

These imply

```text
ν₂(a(n)) = n/4 + O(log n),
```

which is stronger than the registered limit.

## Formal Conjectures theorem

The file in `lean/` imports the current Formal Conjectures module and proves the exact proposition
as `A105751Proof.oeisA105751_conjecture`:

```lean
theorem oeisA105751_conjecture :
  Tendsto
    (fun n ↦ (4 : ℚ) * (padicValInt 2 (OeisA105751.a n) : ℚ) / (n : ℚ))
    atTop (nhds 1) := by
  ...
```

The project is pinned to Formal Conjectures commit
[`638da20efd8eeeed2993fc2550fc596dc90c1ce8`](https://github.com/google-deepmind/formal-conjectures/commit/638da20efd8eeeed2993fc2550fc596dc90c1ce8),
where the target is still marked `research open`.

## Mathmatical Explanation (AI generated)

Write the product in Gaussian-integer coordinates:

```text
P_n = ∏_{k=0}^n (1 + ki) = X_n + iY_n.
```

Lean first proves that the original complex product is the image of this Gaussian-integer
product, so `a(n) = Y_n` exactly. Multiplication by the next factor gives the integer recurrence

```text
X_{n+1} = X_n - (n+1)Y_n,
Y_{n+1} = (n+1)X_n + Y_n.
```

For a four-factor block, the proof extracts one factor of `2` and represents the remaining
Gaussian integer as `r + 4si`. Adjacent normalized blocks are paired into two polynomial
superblock families (one for even starts and one for odd starts). Their real and imaginary
coordinates are odd, while their cross-differences have the divisibility needed for a dyadic
block induction.

That induction proves that the normalized imaginary coordinate of a nonempty block of length
`L` has exact 2-adic valuation `ν₂(L)`. Regrouping the original product then yields the four
residue-class formulas displayed above. Their main term is `m` when `n = 4m + r`; the remaining
term is at most logarithmic because
`ν₂(⌈m/2⌉) ≤ log₂(m) + 1`.  Hence

```text
ν₂(a(n)) = n/4 + O(log n).
```

Lean bounds the absolute error by `(12 + 4 log₂ n) / n`, proves this bound tends to zero, and
applies the squeeze theorem. The exceptional zero terms `a(0)` and `a(3)` are outside the
eventual estimate and therefore do not affect convergence at infinity.

## Proof structure

1. Identify the complex product with an integer Gaussian product.
2. Normalize each four-factor block and prove the general dyadic block lemma.
3. Derive exact valuations in all four residue classes.
4. Convert `ExactTwo` statements to `padicValInt` equalities.
5. Bound the asymptotic error and prove the rational-valued `Tendsto` theorem.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Exact Formal Conjectures target, pinned to commit `638da20e...` |
| `lean4web/` | `v4.27.0` | Standalone mathlib-only definitions and target for Lean4Web |

Each directory contains one Lean source file, `lakefile.toml`, `lean-toolchain`, and
`lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both builds check the completed proof. The final axiom audit reports only Lean/mathlib's standard
axioms:

```text
[propext, Classical.choice, Quot.sound]
```

In particular, the final theorem does not depend on `sorryAx`.

## Status boundary

What this repository targets:

```text
ν₂(a(n)) ~ n/4.
```

What it does not target:

```text
For every prime p ≡ 1 (mod 4),  νₚ(a(n)) ~ n/(p-1).
```

The latter is the separate Formal Conjectures theorem
`OeisA105751.conjecture.variants.moll_p_mod_4_eq_1` and remains open even after the 2-adic target
is solved.  The `textbook` theorem `OeisA105751.prime_divides_some_term` is also outside this
repository's scope.

## Sources

- [OEIS A105751](https://oeis.org/A105751)
- [Formal Conjectures: `OEIS/105751.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OEIS/105751.lean)

## AI usage disclosure

This formalization was developed with assistance from OpenAI Codex.
