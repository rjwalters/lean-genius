# Problem: Does the analogous shallow-diagonal sum with a fixed stride s (stepping s col...

**Slug**: combinations-formula-oq-08-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Does the analogous shallow-diagonal sum with a fixed stride s (stepping s columns per row) recover the s-bonacci / higher-order recurrence numbers, and can that be formalized uniformly?

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"Fibonacci Numbers as Shallow-Diagonal Sums of Pascal's Triangle" (combinations-formula-oq-08). It records a natural next step flagged during
formalization: Does the analogous shallow-diagonal sum with a fixed stride s (stepping s columns per row) recover the s-bonacci / higher-order recurrence numbers, and can that be formalized uniformly?

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: Fibonacci Numbers as Shallow-Diagonal Sums of Pascal's Triangle (`combinations-formula-oq-08`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Does the analogous shallow-diagonal sum with a fixed stride s (stepping s columns per row) recover the s-bonacci / higher-order recurrence numbers, and can that be formalized uniformly?

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `combinations-formula-oq-08` — parent proof / direct source of this open question.

## Tags

combinatorics, fibonacci, pascals-triangle, binomial-coefficients, finset-sums, number-theory
