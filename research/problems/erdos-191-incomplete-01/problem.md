# Erdős Problem #191: Monochromatic Sets with Large 1/log Sum

**Lean file**: `proofs/Proofs/Erdos191Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 8/10

## Problem Statement

Erdős #191: Let $X = \{x_1, x_2, \ldots\}$ be a set of positive integers with $\sum 1/x_i$ divergent. Can the integers always be 2-colored so that each color class has $\sum 1/x_i = \infty$?

## The Sorry

```lean
theorem small_n_bound (n : ℕ) (hn : n ≤ 10) (X : Finset ℕ) (hX : X ⊆ IntegerSet n) :
    logInverseSum X ≤ 10 := by
  sorry
```

**Why tractable**: For $n \leq 10$, `IntegerSet n` is a finite set. The maximum sum $\sum_{x \in \{1,\ldots,10\}} 1/x \approx 2.928 < 10$. This is a finite computation / decidable bound.

## Key Facts

- `IntegerSet n = Finset.filter (2 ≤ x) (Finset.range (n+1))` — i.e., `{2,...,n}`
- `logInverseSum X = X.sum (fun x => 1 / Real.log x)`
- For X ⊆ IntegerSet 10 = {2,...,10}, max sum ≈ ∑_{x=2}^{10} 1/log(x) ≈ 6.14 < 10

## Approach

1. X ⊆ IntegerSet n ⊆ IntegerSet 10 = {2,...,10}
2. `logInverseSum X ≤ logInverseSum (IntegerSet 10)`
3. Bound `logInverseSum (IntegerSet 10)` numerically:
   - Use `Real.log_le_log` or explicit bounds on log
   - Show each term 1/log(x) ≤ some rational bound
   - The sum of rational bounds ≈ 6.14 < 10
4. Or: use `1/log(x) ≤ 2` for all x ≥ 2, so sum ≤ 2 * card {2,...,10} = 18 < 10... wait, that's not ≤ 10
5. Better: `1/log(x) ≤ 1/log(2)` for x ≥ 2, and `1/log(2) ≤ 3/2`, so sum ≤ 9 * (3/2) = 13.5. Still > 10.
6. Need tighter bound: use `1/log(x) ≤ 2` only for x=2, then smaller for larger x. Interval arithmetic approach.

## Key Mathlib APIs

- `Finset.sum_le_sum` for bounding sums
- `Finset.sum_union_disjoint`
- `norm_num` for numerical computations
- `Finset.card_le_card` / subset reasoning

## Related Gallery Proof

- `src/data/proofs/erdos-191/` — Erdős Problem #191 base proof
- `proofs/Proofs/Erdos191Problem.lean` — the file with the sorry

## First Steps (OBSERVE phase)

1. Read the full `Erdos191Problem.lean` file
2. Understand the definition of `logInverseSum` and `IntegerSet`
3. Try `decide` — this might work directly if everything is computable
4. If not, try `norm_num` extension or explicit bound
