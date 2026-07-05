# Problem: Does the same cut-set / double-erase technique extend to other graded refinem...

**Slug**: composition-parts-choose-oq-01-oq-03
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

Does the same cut-set / double-erase technique extend to other graded refinements of Mathlib's ungraded composition cardinalities?

### Why This Matters

This is an open-question extension (generalization) arising from the gallery proof
"Composition Parts OQ-01: Compositions of n into k Parts Number C(n−1, k−1)" (composition-parts-choose-oq-01). It records a natural next step flagged during
formalization: Does the same cut-set / double-erase technique extend to other graded refinements of Mathlib's ungraded composition cardinalities?

Estimated tractability: challenging.

## Known Results

### What's Already Proven

- Parent gallery proof: Composition Parts OQ-01: Compositions of n into k Parts Number C(n−1, k−1) (`composition-parts-choose-oq-01`) — provides the base result and
  the machinery this extension builds on.

### What's Still Open

- Does the same cut-set / double-erase technique extend to other graded refinements of Mathlib's ungraded composition cardinalities?

### Our Goal

Formalize the statement above in Lean 4, reusing the parent proof's development
where possible and filling the specific gap this open question identifies.

## Related Gallery Proofs

- `composition-parts-choose-oq-01` — parent proof / direct source of this open question.

## Tags

combinatorics, enumerative-combinatorics, compositions, counting, binomial-coefficients, bijective-proof, stars-and-bars
