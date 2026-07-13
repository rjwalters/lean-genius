# Problem: Complete Simplicial Complex Infrastructure for Gowers Hypergraph Regularity

**Slug**: szemeredi-hypergraph-core-oq-01-incomplete-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Plain Language

`SzemerediHypergraphCore.lean` defines a "naive" regularity notion for k-uniform hypergraphs
but this is insufficient for applications (counting lemma, removal lemma, multidimensional
Szemerédi). The full Gowers (2007) regularity requires measuring k-graph density relative to
a simplicial complex — a nested family of (k-1)-graphs, (k-2)-graphs, ..., down to edges.

The open question: define `SimplicialComplex`, the relative density notion, and the
Gowers-regular predicate in Lean 4, building on the existing `UHypergraph` infrastructure.

### Formal Statement

```lean
-- Target: SimplicialComplex for Gowers (2007) regularity
structure SimplicialComplex (V : Type*) (k : ℕ) where
  faces : ∀ j : Fin k, Finset (Finset V)
  downClosed : ∀ (j : Fin k) (s : Finset V), s ∈ faces j →
               ∀ (t : Finset V), t ⊆ s → t.card = j.val → t ∈ faces j

def relativeKDensity (H : UHypergraph V k) (C : SimplicialComplex V k) : ℝ := ...

def IsGowersRegular (H : UHypergraph V k) (ε : ℝ) (C : SimplicialComplex V k) : Prop := ...
```

### Why This Matters

1. Prerequisite for the hypergraph regularity lemma and counting lemma (Nagle-Rödl-Schacht 2006)
2. The `UHypergraph` definition already exists — this extends it with the right regularity notion
3. Would replace 27+ per-problem hypergraph definitions across Erdős files with centralized infra

## Known Results

### What's Already Proven (in SzemerediHypergraphCore.lean)

- `UHypergraph V k`: k-uniform hypergraph structure (0 sorries, 0 axioms)
- `kPartiteDensity`: density of k-graph within a k-partite setting
- `IsHypergraphRegular`: naive regularity (density deviation ≤ ε)
- 4 helper lemmas proved

### What's Still Open

- `SimplicialComplex V k`: nested family of j-graphs for j < k
- `relativeKDensity`: density of k-graph relative to a simplicial complex
- `IsGowersRegular`: Gowers (2007) full regularity predicate

### Our Goal

Define the simplicial complex infrastructure and prove basic properties connecting it
to the existing `IsHypergraphRegular` (naive regularity is a special case of Gowers
regularity with respect to the complete complex).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `szemeredi-hypergraph-core` | Direct parent — UHypergraph, naive regularity | Finset, HypergraphRegular |
| `szemeredi-regularity-lemma` | Graph case regularity | SzemerediCore, bipartite density |

## Initial Thoughts

### Potential Approaches

1. **Inductive SimplicialComplex**: `∀ j : Fin k, Finset (Finset V)` with down-closure as a field
2. **Subtype approach**: `kFace V j = {s : Finset V // s.card = j}` — cleaner types

### Key Difficulties

- Dependent type `Fin k` vs `ℕ` in face indexing
- Connecting relative density to existing `kPartiteDensity`

## Tractability Assessment

**Difficulty**: Challenging (5/10)

The definitions are mathematically clear (Gowers 2007). The challenge is Lean's dependent
type system for the nested face structure. First steps (defining SimplicialComplex) are
tractable; proving the full regularity lemma is moonshot.

## References

- Gowers (2007) "Hypergraph regularity and the multidimensional Szemerédi theorem"
- Nagle, Rödl, Schacht (2006) "The counting lemma for regular k-uniform hypergraphs"
- Mathlib: `Mathlib.Combinatorics.SetFamily.Shadow` — shadow operations on Finset families

## Metadata

```yaml
tier: A
significance: 9
tractability: 5
tags:
  - combinatorics
  - hypergraph-regularity
  - szemeredi
  - simplicial-complex
related_proofs:
  - szemeredi-hypergraph-core
  - szemeredi-regularity-lemma
source: gallery-gap
created: 2026-04-21
```

**Significance**: 9/10
**Tractability**: 5/10
