# Problem: Binomial Convolution Identity n! = Σ C(n,k)·D(n−k)

**Slug**: derangements-convergence-oq-07
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: derangements-convergence

## Problem Statement

### Formal Statement

$$
n! = \sum_{k=0}^{n} \binom{n}{k}\, D(n-k),\qquad D = \text{numDerangements}
$$

### Plain Language

Prove that the factorial equals the binomial convolution of derangement numbers.
Combinatorially, every permutation of an $n$-element set is uniquely determined by its
fixed-point set (of size $k$, chosen in $\binom{n}{k}$ ways) together with a derangement
of the remaining $n-k$ elements. Algebraically this is the **inverse binomial transform**
of the inclusion–exclusion formula $D(n) = \sum_k (-1)^k n!/k!$ — the dual direction to the
parent's analytic $D(n)/n! \to e^{-1}$ story.

### Why This Matters

All 12 existing siblings concern the *analytic* side (convergence rate, round/floor/ceiling
$n!/e$ formulas, sign/two-sided sandwiches, the one-term recurrence and its congruences,
the Poisson(1) fixed-point distribution). None states the binomial **convolution** identity,
which is purely combinatorial and absent from Mathlib. It is the counting identity that
*defines* the relationship between permutations and derangements.

## Known Results

### What's Already Proven

- Parent entry `derangements-convergence` is verified (0-axiom) and supplies
  `numDerangements_eq_factorial_mul_altSum` ($D(n) = n!\sum_{k\le n}(-1)^k/k!$).
- Mathlib has `numDerangements`, `numDerangements_sum`, `numDerangements_succ`,
  `numDerangements_add_two`.

### What's Still Open

- The target identity below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child of `derangements-convergence`.
Category: **connection**.

## Target Lean Sketch

```lean
open Finset

/-- The factorial is the binomial convolution of derangement numbers. -/
theorem numDerangements_binomial_convolution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), n.choose k * numDerangements (n - k) = n.factorial := by
  sorry
```

Two routes:
- **Double-sum route**: cast to ℝ, expand `D(n−k)` via the parent identity and
  `C(n,k)·(n−k)! = n!/k!`, swap summation order with `Finset.sum_comm`, and collapse the
  inner alternating binomial sum with `Int.alternating_sum_range_choose`.
- **Induction route** (lower risk): strong induction on `n` using `numDerangements_add_two`
  and Pascal's rule `Nat.choose_succ_succ`; base cases `n = 0, 1` by `decide`, step by
  `push_cast; ring`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `derangements-convergence` | Parent: D(n)/n! → e⁻¹ | inclusion–exclusion, alternating sum |
| `derangements-convergence-oq-05` | Sibling: fixed-point distribution (analytic) | Poisson limit |

## Tractability Assessment

**Difficulty**: Moderate

**Significance**: 7/10  |  **Tractability**: 6/10  |  **Tier**: B

**Justification**: All ingredients exist in Mathlib, but the double-sum reindexing (or the
induction bookkeeping with mixed ℕ/ℤ casts) requires some care. The induction route is a
reliable fallback.

### Suggested First Steps

1. Reduce to ℝ (or ℤ): rewrite `D(n−k)` using the parent identity and
   `Nat.choose_mul_factorial_mul_factorial` / `Nat.cast_choose`.
2. Swap the order of summation with `Finset.sum_comm`; collapse the inner alternating
   binomial sum with `Int.alternating_sum_range_choose`.
3. If the swap is fiddly, prove by strong induction on `n` via `numDerangements_add_two`
   + `Nat.choose_succ_succ`, closing the step with `ring` after `push_cast`.

## References

### Mathlib

- `Nat.choose_mul_factorial_mul_factorial` — Data/Nat/Choose/Basic.lean
- `Nat.cast_choose` — Data/Nat/Choose/Cast.lean
- `Int.alternating_sum_range_choose` — Data/Nat/Choose/Sum.lean
- `numDerangements_sum` — Combinatorics/Derangements/Finite.lean
- `numDerangements_succ`, `numDerangements_add_two` — Combinatorics/Derangements/Finite.lean
- `Finset.sum_comm` — Algebra/BigOperators/Basic.lean
- Parent lemma `numDerangements_eq_factorial_mul_altSum` — proofs/Proofs/DerangementsConvergence.lean

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - binomial-transform
  - convolution-identity
  - inclusion-exclusion
related_proofs:
  - derangements-convergence
  - derangements-convergence-oq-05
difficulty: moderate
source: proof-suggestion
created: 2026-07-01
```
