# Problem: Minimal Polynomial of √n over ℚ: Eisenstein Generalization

**Slug**: sqrt2-minpoly-oq-01
**Created**: 2026-04-23T02:11:45+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For any } n \in \mathbb{Z}_{> 0} \text{ that is not a perfect square,}
\quad \mathrm{minpoly}_{\mathbb{Q}}(\sqrt{n}) = X^2 - n.
$$

Equivalently: if $p$ is any prime with $p \mid n$ and $p^2 \nmid n$, then $X^2 - n$
is irreducible over $\mathbb{Q}$ by Eisenstein's criterion at $p$.

In Lean 4 / Mathlib:

```lean
theorem minpoly_sqrt_n (n : ℤ) (hn : 0 < n) (hsq : ¬ IsSquare n) :
    minpoly ℚ (Real.sqrt n) = X ^ 2 - C (n : ℚ) := by
  sorry
```

### Plain Language

The gallery already proves `minpoly ℚ (√2) = X² - 2` using Eisenstein's criterion at
the prime 2.  The open question asks for the analogous statement for any non-perfect-square
positive integer $n$: the minimal polynomial of $\sqrt{n}$ over the rationals is the
degree-2 polynomial $X^2 - n$.

The proof strategy is identical: pick a prime $p$ that divides $n$ exactly once; then
Eisenstein at $p$ shows $X^2 - n$ is irreducible, and since $\sqrt{n}$ satisfies it,
it must be the minimal polynomial.

### Why This Matters

This is a clean and self-contained generalization of the flagship `sqrt2-minpoly` gallery
entry.  Formalizing it:
- Closes the first listed open question from that proof's conclusion
- Provides a reusable pattern for proving irrationality of $\sqrt{n}$ for all non-squares
- Connects `minpoly` API to `Polynomial.Irreducible.eisenstein` in Mathlib
- Could become a Mathlib PR candidate (straightforward, general, and cited often)

## Known Results

### What's Already Proven

- `minpoly ℚ (√2) = X² - 2` — `proofs/Proofs/Sqrt2MinPoly.lean` (gallery entry)
- `Polynomial.irreducible_of_eisenstein_criterion` — Mathlib (`Mathlib.RingTheory.Eisenstein.Basic`)
- `Nat.sqrt_lt_self` + `Nat.sqrt_eq` for checking perfect-square status

### What's Still Open

- The general case: $n$ any non-perfect-square positive integer
- Handling squarefree vs. non-squarefree $n$ (e.g. $n = 12$: $\sqrt{12} = 2\sqrt{3}$, still irrational; pick $p = 3$)

### Our Goal

Prove `minpoly ℚ (Real.sqrt n) = X ^ 2 - C n` for all non-square positive integers $n$,
using Eisenstein at a prime $p \mid n$ with $p \nmid n/p$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `sqrt2-minpoly` | Direct parent — proves the $n=2$ case | `minpoly`, Eisenstein at 2 |
| `sqrt2-irrational` | Alternate irrationality proof | Divisibility argument |
| `sqrt2-plus-sqrt3-irrational` | Related irrationality result | Field extension degree |
| `algebraic-numbers-countable` | Algebraic number context | `minpoly`, degree arguments |

## Initial Thoughts

### Potential Approaches

1. **Direct Eisenstein generalization** (primary):
   - Pick a prime `p` with `p ∣ n` and `p^2 ∤ n` (exists because n is not a perfect square)
   - Apply `Polynomial.irreducible_of_eisenstein_criterion` at `p`
   - Show `Real.sqrt n` satisfies `X^2 - n` (i.e., `(Real.sqrt n)^2 = n`)
   - Conclude via `minpoly.eq_of_irreducible_of_monic`
   - Risk: Lean's coercion between `ℤ` and `ℚ` may need careful handling

2. **Irrationality-first approach**:
   - Show `√n ∉ ℚ` (irrationality) then use `[ℚ(√n):ℚ] = 2`
   - Conclude degree-2 minimal polynomial
   - Risk: Requires more field extension infrastructure

### Key Difficulties

- Choosing the right prime `p`: need `Nat.minFac n` or similar to extract a prime factor
- Coercions: `n : ℤ` vs `n : ℚ` in polynomial context
- `Real.sqrt n` satisfies `X^2 - n` over `ℝ`, need it over `ℚ` embedding
- Non-perfect-square condition must be stated precisely (use `Nat.sqrt n ^ 2 ≠ n` or `¬ IsSquare (n : ℤ)`)

### What Would a Proof Need?

- Key lemma 1: `∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬ (p^2 ∣ n)` for non-perfect-square n
- Key lemma 2: `(Real.sqrt n) ^ 2 = n` (for positive n)
- Key lemma 3: `Polynomial.irreducible_of_eisenstein_criterion` applied to `X^2 - C (n:ℚ)` at prime `p`
- Technical: `minpoly.eq_of_irreducible_of_monic` or `minpoly.unique`

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The $n=2$ case is already proven in the gallery — the structure is identical
- Eisenstein's criterion is available in Mathlib and was used in the parent proof
- The only new work is parameterizing over `n` and finding the right prime `p`
- No new mathematical ideas required — purely a generalization of existing infrastructure

**Estimated Effort**:
- Exploration: 1-2 hours (map out the Mathlib API)
- If tractable: 1-2 days of proof writing
- Expected outcome: high confidence this can be fully verified

## References

### Papers
- Eisenstein, G., "Über die Irreductibilität und einige andere Eigenschaften der Gleichung...", 1850

### Mathlib
- `Mathlib.RingTheory.Eisenstein.Basic` — `Polynomial.irreducible_of_eisenstein_criterion`
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` — pattern for parameterized irreducibility
- `Mathlib.FieldTheory.Minpoly.Basic` — `minpoly.unique`, `minpoly.eq_of_irreducible_of_monic`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.sqrt_sq`

## Metadata

```yaml
tags:
  - algebraic-number-theory
  - minimal-polynomial
  - eisenstein
  - irrationality
  - polynomial-irreducibility
related_proofs:
  - sqrt2-minpoly
  - sqrt2-irrational
  - sqrt2-plus-sqrt3-irrational
  - algebraic-numbers-countable
difficulty: low
source: gallery-gap
created: 2026-04-23T02:11:45+02:00
```

**Significance**: 7/10
**Tractability**: 9/10
