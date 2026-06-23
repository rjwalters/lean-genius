# Erdős Problem #32: Additive Complements of Primes

**Lean file**: `proofs/Proofs/Erdos32Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 4/10

## Problem Statement

Erdős #32: What is the minimum size of a set B such that every integer is the sum of a prime and an element of B?

## The Sorry

```lean
sorry -- Technical proof omitted
```

Context (from surrounding code):
```lean
intro A hA C hC hBound
have := ruzsa_lower_bound A hA ((lowerBoundConstant - C) / 2) (by linarith)
-- The bound contradicts the liminf condition
sorry
```

**Context**: A lower bound result using Ruzsa's inequality. The sorry needs to derive a contradiction from the bound and the liminf condition.

## Mathematical Content

The sorry is in a proof by contradiction: assuming `liminf |A ∩ [1,N]| / f(N) < lowerBoundConstant`, we use `ruzsa_lower_bound` to derive a contradiction.

This is a combinatorial counting argument: the lower bound on A's density contradicts the assumed upper bound.

## Approach

1. Read `Erdos32Problem.lean` to understand `ruzsa_lower_bound` and `lowerBoundConstant`
2. The sorry likely needs: `linarith` or `omega` combining the two bounds
3. Or: the conclusion follows from a strict inequality chain
4. Check if `linarith [this, hBound]` or similar closes the goal

## Key Mathlib APIs

- `linarith` for inequality chains
- `Filter.liminf` if used
- Check what `ruzsa_lower_bound` states exactly

## Related Gallery Proof

- `src/data/proofs/erdos-32/` — Erdős Problem #32
- `proofs/Proofs/Erdos32Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos32Problem.lean` fully
2. Understand `ruzsa_lower_bound`, `lowerBoundConstant`, the liminf condition
3. Check the exact goal at the sorry location using the context
4. Try `linarith` with the available hypotheses first
