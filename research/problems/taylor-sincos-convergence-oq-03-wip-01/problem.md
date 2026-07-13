# Problem: Alternating Series Estimation for Sin/Cos Taylor Series

**Slug**: taylor-sincos-convergence-oq-03-wip-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Complete 3 sorries in `TaylorSinCosConvergenceOQ03.lean`:
1. `alternating_tail_bound` — the alternating series estimation theorem: tail error ≤ first omitted term
2. `sin_alternating_remainder` — apply (1) to bound sin Taylor remainder
3. `cos_alternating_remainder` — apply (1) to bound cos Taylor remainder

### Formal Statement

```lean
-- 1. KEY RESULT: Alternating Series Estimation
theorem alternating_tail_bound {a : ℕ → ℝ}
    (ha_pos : ∀ k, 0 ≤ a k)
    (ha_dec : Antitone a)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    (ha_sum : Summable (fun k => (-1 : ℝ) ^ k * a k))
    (n : ℕ) :
    ‖∑' k, (-1 : ℝ) ^ (k + n) * a (k + n)‖ ≤ a n := by sorry

-- 2. Sin remainder bound (follows from 1)
theorem sin_alternating_remainder (n : ℕ) (x : ℝ) :
    ‖Real.sin x - ∑ k ∈ range n,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)‖ ≤
    sinTermAbs x n := by sorry

-- 3. Cos remainder bound (follows from 1)
theorem cos_alternating_remainder (n : ℕ) (x : ℝ) :
    ‖Real.cos x - ∑ k ∈ range n,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)‖ ≤
    cosTermAbs x n := by sorry
```

### Why This Matters

The alternating series error bound for sin/cos is a fundamental result:
- Tighter than Lagrange remainder by a factor of (2n+1)
- Used in numerical analysis for bounding approximation error
- Completing this entry provides a verified `alternating_tail_bound` for use across the gallery

## Known Results

### What's Already Proven

In `TaylorSinCosConvergenceOQ03.lean`:
- `lhopital_infty_right_zero` (private): c=0 reduction for L'Hôpital
- `sinTermAbs_nonneg`, `cosTermAbs_nonneg`: positivity of series terms
- `sinTermAbs_antitone`: sin terms are decreasing for |x| ≤ 1
- `sinTermAbs_tendsto`: sin terms tend to 0
- `alternating_tighter_than_lagrange_sin`: bounds relation
- `alternating_vs_lagrange_at_one`: concrete example at x=1, n=3

Mathlib has:
- `Mathlib.Topology.Algebra.InfiniteSum.Alternating` — alternating series machinery
- `Real.hasSum_sin`, `Real.hasSum_cos` — sin/cos power series convergence
- `summable_pow_div_factorial` — summability of `|x|^n / n!`

### Our Goal

Prove `alternating_tail_bound` using Mathlib's alternating series tools, then derive the sin/cos bounds.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `taylor-sincos-convergence` | Parent: Lagrange remainder for sin/cos |
| `taylor-sincos-convergence-oq-03` | This file's source: OQ asking for alternating bound |
| `mean-value-theorem` | MVT underlies Lagrange remainder |

## Potential Approaches

### For `alternating_tail_bound`:

**Approach 1 — Direct Mathlib**: Look for `Mathlib.Topology.Algebra.InfiniteSum.Alternating`. The key theorem may be `Finset.inner_mul_le_norm_mul_iff` or an alternating series tail bound.
- Check: `HasSum.alternating_series_estimation` or `alternating_series_sum_lt`
- The statement `‖∑' k, (-1)^(k+n) * a(k+n)‖ ≤ a n` is the tail-sum form

**Approach 2 — Induction on partial sums**: The standard proof shows:
- The even partial sums $S_{2m}$ are increasing and bounded above by $a_n$
- The odd partial sums $S_{2m+1}$ are decreasing and bounded below by $-a_n$
- They converge to the same limit (by antitone + tendency to 0)
- Therefore the limit lies in $[-a_n, a_n]$

**Key Mathlib search**: `exact?` or `apply?` after setting up the goal in terms of Mathlib's `tsum`.

### For `sin_alternating_remainder`:

Once `alternating_tail_bound` is proved:
1. The sin series `∑' k, (-1)^k * x^(2k+1)/(2k+1)!` converges (use `Real.hasSum_sin`)
2. The remainder is a tail sum: apply `alternating_tail_bound` to `sinTermAbs x`
3. Need: antitone property (proved in file for |x| ≤ 1; needs extension for all x or restriction)

**Note**: `sinTermAbs_antitone` assumes `|x| ≤ 1`. For general x, a different antitone argument may be needed (using eventual antitone rather than global).

### For `cos_alternating_remainder`:

Same structure as sin, using `cosTermAbs` and `Real.hasSum_cos`.

## Key Difficulties

1. `sinTermAbs_antitone` only proved for `|x| ≤ 1` — need eventual antitone for general x
2. Connecting `Real.hasSum_sin` (which expresses sin as an infinite sum) to the tail remainder form
3. Getting from `HasSum` to `tsum` form matching the sorry statement

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- `alternating_tail_bound` is a standard textbook result; Mathlib likely has direct API
- The sin/cos specializations follow from (1) + existing file infrastructure
- Main challenge is API navigation: finding the right Mathlib lemmas

**Estimated Effort**: 2-4 hours

## References

### Mathlib
- `Mathlib.Topology.Algebra.InfiniteSum.Alternating` — alternating series
- `Mathlib.Analysis.SpecificLimits.Basic` — `Real.hasSum_sin`, `Real.hasSum_cos`
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum` API

### Local Files
- `proofs/Proofs/TaylorSinCosConvergenceOQ03.lean` — target file with 3 sorries

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - sorry-completion
  - alternating-series
  - taylor-series
related_proofs:
  - taylor-sincos-convergence-oq-03
  - mean-value-theorem
difficulty: low-medium
source: gallery-gap
created: 2026-04-05
```

**Significance**: 7/10
**Tractability**: 7/10
