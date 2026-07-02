# Problem: Packing–Covering Bracket νᵣ ≤ ρᵣ ≤ τᵣ for K_r-Freeness

**Slug**: szemeredi-counting-oq-01-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- open question of the verified parent szemeredi-counting-oq-01 -->

## Problem Statement

### Formal Statement

$$
\nu_r(G) \le \rho_r(G) \le \tau_r(G),
$$
$$
\text{where } \nu_r = \text{max edge-disjoint } K_r\text{-packing},\
\rho_r = \min \text{ edges to delete to make } G\ K_r\text{-free},\
\tau_r = \min\ K_r\text{-covering by edges, with } |s \cap t| \le r-2 \text{ for edge-disjoint } r\text{-cliques.}
$$

### Plain Language

The parent proof establishes, for triangles, the packing–covering bracket ν ≤ ρ ≤ τ: the maximum number of edge-disjoint triangles is at most the minimum number of edges whose deletion destroys all triangles, which is at most the minimum edge cover of all triangles. This problem asks to prove the same bracket for r-cliques (K_r) for general r, using the sharpened shared-vertex bound: two edge-disjoint copies of K_r share at most r−2 vertices.

### Why This Matters

The triangle bracket is the combinatorial skeleton of quantitative triangle removal. Generalizing it to K_r is the natural next step toward a quantitative K_r-removal statement and clarifies exactly where the "edge-disjoint ⇒ bounded overlap" input enters. It is a self-contained extremal-combinatorics result with a clear LP-duality flavor.

### Our Goal

Formalize νᵣ ≤ ρᵣ ≤ τᵣ for all r ≥ 3, mirroring the parent's triangle argument, with the shared-vertex lemma |s ∩ t| ≤ r−2 for edge-disjoint r-cliques as the key structural input.

## Known Results

### What's Already Proven

- The triangle case ν ≤ ρ ≤ τ — parent `szemeredi-counting-oq-01` (verified, 0-axiom, original).
- The two inequalities as counting/covering arguments over the triangle hypergraph.

### What's Still Open (in the gallery)

- The r-clique generalization with the r−2 overlap bound.

### Our Goal

Reproduce the two inequalities for the K_r hypergraph: ν ≤ ρ (an edge-disjoint packing forces at least that many deletions) and ρ ≤ τ (any edge cover of all K_r's is a valid deletion set).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| szemeredi-counting-oq-01 | Direct parent; triangle bracket and proof template | packing/covering, hypergraph counting, LP duality |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Lift the triangle argument (recommended)**: recast G's r-cliques as a hypergraph H whose hyperedges are the edge-sets of K_r's; νᵣ = matching number of H, τᵣ = covering number; ρᵣ is the min hitting set of H by graph-edges. The two inequalities are then generic matching ≤ transversal facts plus the r−2 shared-vertex bound to control double counting.
   - Why it might work: it's the parent's argument with r-clique edge-sets replacing triangle edge-sets.
   - Risk: bookkeeping for `|s ∩ t| ≤ r-2` and edge multiplicity when r > 3.

### Key Difficulties

- Formalizing "edge-disjoint K_r's share ≤ r−2 vertices" and its consequence for edge overlaps.
- Choosing a clean Lean model of the K_r hypergraph (Finset of Finset of edges).

### What Would a Proof Need?

- Key lemma 1: edge-disjoint r-cliques s, t ⇒ |s ∩ t| ≤ r−2.
- Key lemma 2 (ν ≤ ρ): a max edge-disjoint packing needs ≥ νᵣ deleted edges.
- Key lemma 3 (ρ ≤ τ): any K_r edge-cover is a K_r-destroying deletion set.
- Technical requirements: `SimpleGraph`, `Finset`, clique API (`SimpleGraph.IsNClique`).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Direct generalization of a verified original result; the proof structure is known.
- Main cost is the r−2 overlap lemma and hypergraph bookkeeping.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–5 days

## References

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Clique` — `IsNClique`, clique finsets.
- `Mathlib.Combinatorics.SimpleGraph.Finite` — edge finsets, counting.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - extremal-graph-theory
  - packing-covering
  - lp-duality
related_proofs:
  - szemeredi-counting-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```
