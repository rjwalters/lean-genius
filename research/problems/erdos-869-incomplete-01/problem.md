# Problem: Erdős #869: Minimal Additive Bases — Complete `union_of_bases`

**Slug**: erdos-869-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos869Problem.lean`

The sorry is in `union_of_bases`:
```lean
theorem union_of_bases (A₁ A₂ : Set ℕ) (h : areDisjointBases A₁ A₂) :
    isAdditiveBasis2 (A₁ ∪ A₂) := by
  simp only [isAdditiveBasis2, containsAllLarge, doubling] at *
  obtain ⟨_, h1, h2⟩ := h
  -- A₁ ∪ A₂ + A₁ ∪ A₂ ⊇ A₁ + A₁
  -- so its complement is ⊆ the complement of A₁ + A₁
  -- which is finite
  sorry  -- requires detailed set manipulation
```

## Key Argument

`isAdditiveBasis2 A` means: the sumset `A + A` contains all sufficiently large integers.

If `A₁` is a basis2, then `A₁ + A₁` contains all `n ≥ N₁` for some `N₁`.
Since `A₁ ⊆ A₁ ∪ A₂`, we have `A₁ + A₁ ⊆ (A₁ ∪ A₂) + (A₁ ∪ A₂)`.
So `(A₁ ∪ A₂) + (A₁ ∪ A₂)` contains all `n ≥ N₁`.

The hard part: showing set inclusion properly in Lean's `Set ℕ` framework.

## Key Steps
1. Unfold `isAdditiveBasis2`: show complement of `(A₁∪A₂)+(A₁∪A₂)` is finite
2. Use `h1: isAdditiveBasis2 A₁` → `∃ N, ∀ n ≥ N, n ∈ A₁ + A₁`
3. Show `A₁ + A₁ ⊆ (A₁ ∪ A₂) + (A₁ ∪ A₂)` via `Set.add_subset_add`
4. Conclude the union is also a basis2

## Tractability: MEDIUM
