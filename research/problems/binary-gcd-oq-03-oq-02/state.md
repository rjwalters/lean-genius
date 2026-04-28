# Current State

**Phase**: ORIENT
**Since**: 2026-04-28
**Iteration**: 2

## Current Focus

Decide scope of formalization: correctness-only (recommended) vs correctness-plus-complexity (deferred). See knowledge.md "Research strategy (recommended)" for the split.

## Active Approach

Session 1 survey recommendation: pursue **correctness-only** formalization of `hgcdMatrix : ℕ → ℕ → CofactorMatrix` in a new `BinaryGcdOQ03OQ02.lean`, reusing the cofactor-matrix machinery already verified in `BinaryGcdOQ03.lean`. Defer the O(M(n)·log n) complexity claim until Mathlib has a bit-complexity model and fast multiplication.

## Blockers

- **Complexity claim only**: O(M(n)·log n) is currently unfalsifiable in Lean. Mathlib has no bit-complexity model for arithmetic operations and no fast multiplication (Karatsuba / Toom-Cook / FFT). Filling these gaps is a multi-thousand-line foundational project that should not be attempted as part of an HGCD formalization.

No blocker on the correctness side; all needed cofactor-matrix machinery exists.

## Next Action

1. Confirm scope decision (correctness-only).
2. Draft `hgcdMatrix` definition + termination measure (`bitsize a + bitsize b`).
3. State and prove the size-reduction lemma: applying `hgcdMatrix(a,b)` to `(a,b)` yields `(a',b')` with `bitsize(max a' b') ≤ bitsize(max a b)/2 + O(1)`. This is the only genuinely new mathematical content vs. the existing Lehmer formalization.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0
