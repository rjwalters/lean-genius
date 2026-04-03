# Problem: Erdős #314: Harmonic Sum Error Term — Complete `erdos_conjecture_true`

**Slug**: erdos-314-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos314Problem.lean`

The sorry is in `erdos_conjecture_true`:
```lean
theorem erdos_conjecture_true : erdos_conjecture := by
  intro δ hδ
  -- The Lim-Steinerberger bound goes to 0, so eventually it's < δ
  sorry
```

Where `erdos_conjecture` is: for every `δ > 0`, eventually `ε(n) < δ` where `ε(n)` 
is a discrepancy measure related to `k^2 * ε(k)`.

## Key Argument

The proof follows from an axiomatized Lim-Steinerberger theorem stating that 
`k^2 * ε(k) → 0`. Since this goes to 0 at `atTop`, for any δ > 0 there exists N 
such that for n ≥ N, `n^2 * ε(n) < δ * n^2`, i.e., `ε(n) < δ`.

## Approach

1. Find the `lim_steinerberger_bound` axiom/theorem in the file
2. Apply `Filter.Tendsto.eventually_lt` or similar 
3. Use the fact that the bound goes to 0 at Filter.atTop

## Tractability: MEDIUM
