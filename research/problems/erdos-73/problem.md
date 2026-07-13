# Problem: Erdős #73 — Almost Bipartite Graphs (Reed's Theorem Extensions)

**Slug**: erdos-73
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Context

The gallery proof `erdos-73` formalizes Reed's theorem (1999): if every subgraph of $G$
has an independent set covering at least $\frac{|V(H)|}{2} - k$ vertices, then $G$ is
*almost bipartite* — the union of a bipartite graph and at most $f(k)$ extra vertices.

Current status: **axiomatized** with 3 axioms: `reed_bound`, `reed_theorem`,
`reed_bound_zero`. These encode Reed's deep probabilistic/structural result.

### Open Questions to Pursue

**OQ-A** (primary): What is the optimal growth rate of $f(k)$? Is $f(k) = O(k)$ or
$f(k) = O(\text{poly}(k))$?

**OQ-B**: Can the Erdős-Pósa constant for odd cycles be improved to yield tighter bounds?

**OQ-C**: Is there a polynomial-time algorithm to find the minimum odd cycle transversal
for graphs satisfying the $k$-independence condition?

### Formal Goal

```lean
-- Current axioms to eventually prove or extend:
axiom reed_bound : ∀ (k : ℕ) (G : SimpleGraph V),
    almostBipartite G k → ∃ f : ℕ → ℕ, G.ExtraVertices ≤ f k

-- Research: tighten the bound
theorem reed_bound_linear : ∃ C : ℕ, ∀ k, f k ≤ C * k
```

### Plain Language

Reed proved that graphs with "near-bipartite" local structure are globally near-bipartite,
but the bound $f(k)$ on the extra vertices is not explicitly optimized. The research
questions are: (1) how fast can $f(k)$ grow, and (2) can we prove computational versions.

### Why This Matters

- Odd cycle transversals have applications in constraint satisfaction and circuit complexity
- Reed's theorem is a key result in structural graph theory (χ-boundedness)
- Better bounds on $f(k)$ could improve algorithms for odd cycle transversal problems

## Known Results

### What's Already Proven (Gallery)

- `erdos-73` (axiomatized) — Reed's theorem: k-independence → almost bipartite
- `trivial_case`, `bipartite_deficiency_zero`, `strict_implies_bipartite`, `K3_violates_strict` — all verified in gallery
- Remaining axioms: `reed_bound`, `reed_theorem`, `reed_bound_zero`

### What's Still Open

- Optimal growth rate of $f(k)$
- Constructive algorithm for odd cycle transversal
- Better Erdős-Pósa constants for odd cycles

### Our Goal

Explore OQ-A (growth rate of f(k)) or attempt to formalize a simple bound like
$f(k) \leq 2k+1$ as a weakening of `reed_bound`. This would lower the axiom count
by replacing `reed_bound` with a weaker verified lemma.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-73` | Direct parent — Reed's theorem | SimpleGraph, independent sets |
| `erdos-476` | Another Erdős graph problem | graph coloring |

## Initial Thoughts

### Potential Approaches

1. **Prove a weak explicit bound** (most tractable):
   - Show $f(k) \leq 2k^2$ or similar via a combinatorial argument
   - This would create a weaker but verified `reed_bound_weak` that can replace the axiom
   - Why it might work: quadratic bounds follow from greedy arguments
   - Risk: may require non-trivial probabilistic arguments even for weaker bounds

2. **Formalize OQ-A survey**:
   - Document known literature bounds on $f(k)$
   - Check if $f(k) = O(k)$ is known or open
   - Create a knowledge.md documenting the state of the art
   - Why it might work: literature survey with Scout is tractable
   - Risk: may not produce Lean code, only documentation

3. **Algorithmic formalization** (OQ-C):
   - Formalize that odd cycle transversal is NP-hard in general
   - Note: Mathlib has `SimpleGraph.IsAcyclic`, `SimpleGraph.IsBipartite`
   - Risk: computational complexity arguments are hard to formalize in Lean

### Key Difficulties

- Reed's theorem uses probabilistic arguments (Lovász Local Lemma or similar)
- Lean 4 has limited probabilistic combinatorics infrastructure
- The axioms encode genuinely hard mathematics

### What Would a Proof Need?

- Key lemma: Independent set size bounds for k-near-bipartite graphs
- Mathlib: `SimpleGraph.independenceNumber`, `SimpleGraph.chromaticNumber`
- Technical: Ramsey-type arguments about small separators

## Tractability Assessment

**Difficulty**: High (for removing axioms) / Medium (for OQ survey/documentation)

**Justification**:
- Reed's proof uses probabilistic methods not yet in Mathlib
- Weak combinatorial bounds might be provable but still require new lemmas
- A literature survey + documentation pass (OQ-A) is tractable in 1-2 days

**Estimated Effort**:
- Literature survey: 1-2 days
- Weak bound proof: 1-2 weeks
- Full axiom removal: months (if ever)

## References

### Papers
- Reed, "Mangoes and Blueberries" (1999) — The core result
- Gyárfás, "Problems from Graph Theory" (1975) — Original Erdős problem
- Pontecorvi & Wollan, "Disjoint cycles intersecting a set of vertices" (2012) — Erdős-Pósa for odd cycles

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` — SimpleGraph API
- `Mathlib.Combinatorics.SimpleGraph.Coloring` — Bipartiteness and 2-colorability
- `Mathlib.Combinatorics.SimpleGraph.Clique` — Clique and independent sets

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - bipartite
  - erdos-problems
  - structural-graph-theory
related_proofs:
  - erdos-73
  - erdos-476
difficulty: hard
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 6/10
