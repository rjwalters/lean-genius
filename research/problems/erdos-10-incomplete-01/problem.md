# Erdős Problem #10: Sums of a Prime and Powers of 2

**Lean file**: `proofs/Proofs/Erdos10OQ01.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 7/10

## Problem Statement

Erdős #10 OQ-01: Do the non-squares have density 1 among the positive integers? (Auxiliary density lemma for the Erdős Problem #10 about sums of a prime and powers of 2.)

## The Sorry

```lean
sorry -- Density computation: #{m² ≤ N} / N = ⌊√N⌋/N → 0
```

**Why tractable**: The density of perfect squares in {1,...,N} is `⌊√N⌋/N`. As N → ∞, `√N/N = 1/√N → 0`. This is a standard real analysis limit.

## Mathematical Content

- Number of perfect squares ≤ N: `⌊√N⌋`
- Density = `⌊√N⌋/N ≤ √N/N = 1/√N → 0`
- So non-squares have density 1

## Approach

1. Bound `#{m : ℕ | m^2 ≤ N}` above by `Nat.sqrt N + 1` or `Real.sqrt N + 1`
2. Show `(Nat.sqrt N : ℝ) / N → 0` using `Nat.sqrt_lt_self` or squeeze theorem
3. Key: `Nat.sqrt N ≤ Real.sqrt N` and `Real.sqrt N / N = 1/Real.sqrt N`
4. Apply `Filter.Tendsto.atTop` with the standard `1/√N → 0` argument

## Key Mathlib APIs

- `Nat.sqrt_lt_self : 1 < n → Nat.sqrt n < n`
- `Real.sqrt_div_self`
- `tendsto_const_nhds`, `Filter.atTop`
- `Real.tendsto_pow_atTop_atTop_of_one_lt`
- `Nat.card_sq_le_of_le`: counting perfect squares

## Related Gallery Proof

- `src/data/proofs/erdos-10/` — Erdős Problem #10 base proof
- `proofs/Proofs/Erdos10OQ01.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos10OQ01.lean` fully — what is the exact statement of the theorem?
2. Look at what's already proved above and below the sorry
3. Try `Filter.Tendsto` approach: `1/Real.sqrt N → 0` as `N → ∞`
4. Check if `Nat.sqrt_lt_self` and `div_tendsto_zero` close the goal
