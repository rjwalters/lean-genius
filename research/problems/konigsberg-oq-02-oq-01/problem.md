# Problem: Hierholzer's Algorithm — Directed Eulerian Circuit Formalization in Lean 4

**Slug**: konigsberg-oq-02-oq-01
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Formalize Hierholzer's algorithm for directed graphs in Lean 4:}\\
\text{if } G \text{ is strongly connected with } \mathrm{indeg}(v) = \mathrm{outdeg}(v) \text{ for all } v,\\
\text{then } G \text{ has an Eulerian circuit.}
$$

### Plain Language

Prove `directed_euler_circuit_sufficient`: given a strongly connected directed graph where every vertex has equal in-degree and out-degree, construct an Eulerian circuit using Hierholzer's algorithm.

The `konigsberg` gallery proof formalizes the undirected case. The `konigsberg-oq-02` extension targets the directed characterization. This problem asks for the constructive proof via Hierholzer's algorithm.

### Why This Matters

Eulerian circuits in directed graphs appear in combinatorial algorithms, de Bruijn sequences, and the BEST theorem (counting Eulerian circuits). Hierholzer's algorithm is constructive and translates naturally to Lean 4's functional style.

## Known Results

### What's Already Proven

- `konigsberg` gallery: undirected Eulerian circuit existence via degree-parity characterization
- Mathlib: `SimpleGraph.Walk`, `SimpleGraph.Euler`, degree theory for simple graphs
- `konigsberg-oq-02` gallery extension (if present): directed degree balance as necessary condition

### What's Still Open

- Constructive Hierholzer proof for directed graphs in Lean 4
- `directed_euler_circuit_sufficient`: the sufficiency direction via algorithm

### Our Goal

Formalize the constructive direction of directed Eulerian circuits via Hierholzer's algorithm, building on the `konigsberg` gallery entry and Mathlib graph theory infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `konigsberg` | Undirected Eulerian circuit formalization | SimpleGraph, degree parity |
| `konigsberg-oq-02` | Directed graph degree characterization | Sister problem |

## Initial Thoughts

### Potential Approaches

1. **Hierholzer constructive algorithm**: Follow edges from any vertex greedily until returning to start, then extend by inserting sub-tours at vertices with unused edges.
   - Why it might work: Standard algorithm, well-understood, maps to Lean functional style
   - Risk: Termination proof requires well-founded induction on remaining edges

2. **Induction on edge count**: If every vertex has equal degree, find a cycle, remove it, apply induction.
   - Why it might work: Clean structural induction, avoids algorithmic termination issues
   - Risk: Strong connectivity preservation after removing a cycle needs a non-trivial lemma

### Key Difficulties

- Termination of Hierholzer's algorithm in Lean 4 (well-founded recursion on edge count)
- Showing the constructed walk visits every edge exactly once
- Directed graph API in Mathlib: Quiver vs SimpleGraph differences

### What Would a Proof Need?

- Key lemma 1: Strongly connected + equal in/out-degree → contains a directed cycle
- Key lemma 2: Removing a directed cycle preserves the equal-degree property on remaining subgraph
- Key lemma 3: Combining two Eulerian circuits sharing a vertex gives a larger Eulerian circuit
- Technical requirements: Mathlib directed graph types, `Finset.card` induction, possibly `Quiver.Path`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The algorithm is classical with a clear proof outline
- `konigsberg` (undirected case) already in gallery — techniques directly transferable
- Main challenge: well-founded recursion for Hierholzer's termination in Lean 4
- Directed graph API may need exploration (Mathlib's Quiver vs SimpleGraph)

**Estimated Effort**:
- Exploration: 1-2 days (API discovery, directed graph support assessment)
- If tractable: 3-5 days (full formalization)

## References

### Papers
- Hierholzer, C. (1873), "Über die Möglichkeit, einen Linienzug ohne Wiederholung zu umfahren"
- van Aardenne-Ehrenfest & de Bruijn (1951), "Circuits and trees in oriented linear graphs" — BEST theorem

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Euler` — Eulerian circuits (undirected)
- `Mathlib.Combinatorics.SimpleGraph.Walk` — graph walks
- `Mathlib.Combinatorics.SimpleGraph.Degree` — degree theory

## Metadata

```yaml
tags:
  - graph-theory
  - euler-paths
  - combinatorics
  - algorithms
  - directed-graphs
related_proofs:
  - konigsberg
  - konigsberg-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 6/10
