# Problem: The Negative Binomial Series - sum of C(n+k,k) r^n = 1/(1-r)^(k+1)

**Slug**: geometric-series-oq-11
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: geometric-series

## Problem Statement

### Formal Statement

For a fixed $k \in \mathbb{N}$ and $|r| < 1$:
$$
\sum_{n=0}^{\infty} \binom{n+k}{k} r^n = \frac{1}{(1-r)^{k+1}}.
$$

### Plain Language

The geometric series $1/(1-r)$ is the $k=0$ case of an entire family. For a fixed
nonnegative integer $k$ and real ratio $|r| < 1$, the generating function of the binomial
coefficients along a diagonal satisfies the closed form $\sum_{n\ge 0}\binom{n+k}{k}r^n =
1/(1-r)^{k+1}$. This is Newton's generalized binomial theorem specialized to the negative
integer exponent $-(k+1)$. Unlike the moment siblings (coefficients polynomial in $n$ via
differentiation), here the coefficients are binomial coefficients and the identity comes
from iterated Cauchy self-convolution of the geometric series.

### Why This Matters

Distinct from all 9 siblings: oq-06/07/10 are polynomial moments (differentiation), oq-09
is parity splitting, oq-08 is a finite-tail defect, oq-04 is q-analog finite sums. None
treats binomial-coefficient (negative-binomial) generating functions. The $k=0$ case
recovers the parent geometric series, and the derivation gives a **combinatorial** route to
the first moment $\sum n\,r^n = r/(1-r)^2$ (distinct from oq-06's differentiation).

## Known Results

### What's Already Proven

- Parent `geometric-series` is verified (0-axiom).
- Mathlib has `tsum_choose_mul_geometric_of_norm_lt_one` and
  `summable_choose_mul_geometric_of_norm_lt_one`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a verified (0-axiom) child. Category: **generalization**.

## Target Lean Sketch

```lean
namespace GeometricSeriesNegBinom
open scoped BigOperators

/-- The negative binomial / diagonal generating-function identity. -/
theorem negBinom_series (k : ℕ) (r : ℝ) (hr : |r| < 1) :
    ∑' n : ℕ, ((n + k).choose k : ℝ) * r ^ n = 1 / (1 - r) ^ (k + 1) := by
  sorry -- tsum_choose_mul_geometric_of_norm_lt_one (Real.norm_eq_abs)

theorem recover_parent (r : ℝ) (hr : |r| < 1) :
    ∑' n : ℕ, r ^ n = 1 / (1 - r) := by
  sorry -- simpa using negBinom_series 0 r hr

theorem sum_succ_mul (r : ℝ) (hr : |r| < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * r ^ n = 1 / (1 - r) ^ 2 := by
  sorry -- negBinom_series 1 with Nat.choose_one_right

/-- Combinatorial derivation of the first moment (distinct from differentiation). -/
theorem first_moment_via_negBinom (r : ℝ) (hr : |r| < 1) :
    ∑' n : ℕ, (n : ℝ) * r ^ n = r / (1 - r) ^ 2 := by
  sorry -- ∑ (n+1) r^n − ∑ r^n via Summable.tsum_sub, then field_simp/ring

end GeometricSeriesNegBinom
```

Plus concrete instances, e.g. $\sum_n (n+1)/2^n = 4$ and $\sum_n \binom{n+2}{2}/2^n = 8$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `geometric-series` | Parent: geometric series | infinite sums |
| `geometric-series-oq-06` | Sibling: first moment via differentiation | power series |
| `binomial-theorem` | Newton generalized binomial (α = -1 case) | binomial coefficients |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The core identity is a direct wrapper of Mathlib's
`tsum_choose_mul_geometric_of_norm_lt_one`; the added value (k=0/k=1 specializations, the
combinatorial first-moment derivation via `Summable.tsum_sub`, numeric examples) is
standard `simp [Nat.choose_one_right]` / `field_simp` / `ring` work.

### Suggested First Steps

1. Prove `negBinom_series` by converting `|r| < 1` to `‖r‖ < 1` (`Real.norm_eq_abs`) and
   applying `tsum_choose_mul_geometric_of_norm_lt_one`.
2. Specialize to $k=0$ (recover parent) and $k=1$ (`Nat.choose_one_right`).
3. Derive the first moment by `Summable.tsum_sub` of the $k=1$ and $k=0$ series, then
   `field_simp`/`ring`; add numeric examples.

## References

### Mathlib

- `tsum_choose_mul_geometric_of_norm_lt_one`, `summable_choose_mul_geometric_of_norm_lt_one`, `hasSum_choose_mul_geometric_of_norm_lt_one` — Analysis/SpecificLimits/Normed.lean
- `hasSum_geom_series_inverse` — Analysis/SpecificLimits/Normed.lean
- `Nat.choose_one_right` — Data/Nat/Choose/Basic.lean
- `Summable.tsum_sub` — Topology/Algebra/InfiniteSum

### Literature

- Newton's generalized binomial theorem; negative binomial series / generating functions.

## Metadata

```yaml
tags:
  - analysis
  - geometric-series
  - generating-functions
  - binomial-coefficients
  - infinite-series
related_proofs:
  - geometric-series
  - geometric-series-oq-06
  - binomial-theorem
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
