# Problem: Burnside Counting OQ-02: Verify `fixed_point_sum_binary_4` via native_decide

**Slug**: burnside-counting-oq-02
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Source**: `src/data/proofs/burnside-counting/meta.json`, open question 2

Use `native_decide` (or `decide`) to verify the fixed point count computation
`fixed_point_sum_binary_4` in the Burnside counting formalization.

## Lean Context

From `proofs/Proofs/BurnsideCounting.lean`:
- Burnside's lemma: `|X/G| = (1/|G|) Σ_{g∈G} |X^g|`
- Applied to counting binary necklaces of length 4
- `fixed_point_sum_binary_4` should count fixed points for each rotation

## Approach

1. Check what `fixed_point_sum_binary_4` is in the Lean file
2. Try `native_decide` or `decide` directly
3. Or compute the sum explicitly using `Fin.sum_univ_eight` etc.

## Tractability: LOW (computation)
