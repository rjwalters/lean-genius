# Problem: Erdős #565: Induced Ramsey Numbers — Complete `induced_ramsey_ge_ordinary`

**Slug**: erdos-565-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos565Problem.lean`

The sorry is in `induced_ramsey_ge_ordinary`:
```lean
theorem induced_ramsey_ge_ordinary (n : ℕ) (G : Graph (Fin n)) :
    inducedRamseyNumber n G ≥ ordinaryRamseyNumber n G := by
  -- Every monochromatic induced copy is also a monochromatic copy
  sorry
```

## Key Argument

- `inducedRamseyNumber n G`: minimum N such that every 2-coloring of K_N contains
  a monochromatic *induced* copy of G
- `ordinaryRamseyNumber n G`: minimum N such that every 2-coloring contains
  a monochromatic copy of G (not necessarily induced)

Since every monochromatic induced copy is also a monochromatic copy (induced ⊆ ordinary),
any N satisfying the induced property also satisfies the ordinary property.
Therefore `inducedRamseyNumber ≥ ordinaryRamseyNumber` by minimality.

## Approach

The proof is a straightforward application of:
- The induced property implies the ordinary property
- `Nat.find` monotonicity (the condition for ordinary is weaker, so the minimum is ≤)

Key Mathlib tools: `Nat.find_mono`, `Nat.find_le`, set membership reasoning.

## Tractability: MEDIUM
