# Problem: Erdős #160: Rainbow-Free Colorings — Complete 2 sorries

**Slug**: erdos-160-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos160Problem.lean`

Two sorries:
1. `h_sublinear`: `∀ ε > 0, ε < 1/3 → ∃ N₀, ∀ n ≥ N₀, h(n) ≤ n^(1-ε)`
   - Comment: "Follows from upper_bound_two_thirds for ε < 1/3; needs rpow_le_rpow"

2. `h_superlog`: `∀ C : ℝ, ∃ N₀, ∀ n ≥ N₀, h(n) ≥ C`
   - Comment: "Requires showing exp(c · (log n)^{1/9}) → ∞, needs Filter.Tendsto infrastructure"

## Context

`h n` is the minimum number of colors needed for a rainbow-free coloring of arithmetic
progressions in `[n]`. The two sorries establish:
- Upper bound: `h(n) = O(n^{2/3+ε})`
- Lower bound: `h(n) → ∞`

## Approach

For `h_superlog`: use that `exp(c * (Real.log n)^(1/9))` tends to infinity at `Filter.atTop`.
Key Mathlib: `Real.tendsto_exp_atTop`, `Filter.Tendsto.comp`.

For `h_sublinear`: apply `upper_bound_two_thirds` (axiomatized) via `rpow_le_rpow`.

## Tractability: MEDIUM
