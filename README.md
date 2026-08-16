# OEIS A105751: the 2-adic asymptotic target

This repository is a Lean formalization workspace for the **2-adic asymptotic target**
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

This repository currently fixes the exact target and the intended theorem boundary.  It is a
**compiling formalization scaffold**, not yet a completed kernel-checked proof of the conjecture.
The four residue-class valuation formulas and their implication for the limit remain proof
obligations.  No file in this repository claims that an imported `sorry` is a proof.

The mathematical route under study gives the stronger formulas, away from the zero terms
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

## Formal Conjectures target

The file in `lean/` imports the current Formal Conjectures module and defines
`A105751TwoAdic.formalConjecturesTarget` with exactly the same proposition as
`OeisA105751.conjecture`:

```lean
def formalConjecturesTarget : Prop :=
  Tendsto
    (fun n ↦ (4 : ℚ) * (padicValInt 2 (OeisA105751.a n) : ℚ) / (n : ℚ))
    atTop (nhds 1)
```

The project is pinned to Formal Conjectures commit
[`638da20efd8eeeed2993fc2550fc596dc90c1ce8`](https://github.com/google-deepmind/formal-conjectures/commit/638da20efd8eeeed2993fc2550fc596dc90c1ce8),
where the target is still marked `research open`.

## Mathmatical Explanation (AI generated)

Write the product in Gaussian-integer coordinates:

```text
P_n = ∏_{k=0}^n (1 + ki) = X_n + iY_n.
```

Then `a(n) = Y_n`.  Multiplication by the next factor gives the integer recurrence

```text
X_{n+1} = X_n - (n+1)Y_n,
Y_{n+1} = (n+1)X_n + Y_n.
```

This removes complex-number bookkeeping and turns the problem into tracking powers of two in
two integer sequences.  Grouping the factors into blocks of four (and, for the correction term,
blocks of eight) leads to the four residue-class formulas displayed above.  Their main term is
`m` when `n = 4m + r`; the remaining term is at most logarithmic because
`ν₂(⌈m/2⌉) ≤ log₂(m) + 1`.  Hence

```text
ν₂(a(n)) = n/4 + O(log n).
```

After dividing by `n` and multiplying by `4`, the error tends to zero, giving the Formal
Conjectures limit.  The exceptional zero terms `a(0)` and `a(3)` are only finitely many indices
and therefore do not affect convergence at infinity.  This section is a mathematical roadmap;
the residue-class identities still need complete Lean proofs before the conjecture is solved.

## Intended proof split

1. Replace the noncomputable complex product by an integer/Gaussian-integer recurrence and prove
   that its imaginary coordinate is `OeisA105751.a`.
2. Formalize the four residue-class valuation formulas above.
3. Prove that the extra valuation term is `O(log n)` and derive the registered `Tendsto` theorem.
4. Audit the final theorem with `#print axioms`; only then propose changing this target to
   `research solved`.

The reported mathematical proof uses four- and eight-factor blocks, a 2-adic cross-difference
identity, a formal-arctangent product-to-sum transformation, and a complete-residue-system sum.

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

The current checks verify the definitions, the exact target restatement, and the initial sequence
values.  They do **not** certify the open conjecture.

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

This repository scaffold was prepared with assistance from OpenAI Codex.
