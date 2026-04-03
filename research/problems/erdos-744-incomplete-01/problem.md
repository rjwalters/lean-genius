# Problem: Erdős #744: Critical Graphs — Complete `bipartitionNumber` definition

**Slug**: erdos-744-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos744Problem.lean`

The sorry is in the definition `bipartitionNumber`:
```lean
noncomputable def bipartitionNumber {V : Type*} [Fintype V] (G : SimpleGraph' V) : ℕ :=
  Nat.find ⟨Fintype.card V * (Fintype.card V - 1) / 2,
    by sorry⟩ -- Existence: deleting all edges always works
```

Need to prove the witness is valid: deleting all edges of G yields a bipartite graph.
The complete edge deletion gives the empty graph (no edges), which is bipartite.

## Key Argument

The empty graph is bipartite (trivially — empty edge sets satisfy bipartiteness).
So `bipartitionNumber G ≤ G.edgeFinset.card` is always valid.

Need to prove: ∃ k, k-edge-deletion of G is bipartite. The upper bound k = #edges works.

## Approach

```lean
-- The empty graph on V is bipartite
have : ∃ (k : ℕ), k ≤ Fintype.card V * (Fintype.card V - 1) / 2 ∧
    ∃ (H : SimpleGraph' V), H.edgeFinset.card = 0 ∧ IsBipartite H := by
  exact ⟨_, le_refl _, emptyGraph, by simp, emptyGraph_bipartite⟩
```

## Tractability: MEDIUM (definition sorry)
