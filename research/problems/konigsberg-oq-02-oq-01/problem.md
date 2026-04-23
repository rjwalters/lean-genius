# Problem: Hierholzer's Algorithm — Directed Eulerian Circuit Formalization in Lean 4

**Slug**: konigsberg-oq-02-oq-01
**Created**: 2026-04-23T11:40:52+02:00
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

- `konigsberg` gallery: undirected Eulerian circuit existence
- Mathlib: `SimpleGraph.Walk`, `SimpleGraph.Euler`, degree theory for simple graphs

### What's Still Open

- Constructive Hierholzer proof for directed graphs in Lean 4
- `directed_euler_circuit_sufficient` theorem

### Our Goal

Formalize the constructive direction of directed Eulerian circuits via Hierholzer's algorithm, building on the `konigsberg` gallery entry and Mathlib graph theory.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `konigsberg` | Undirected Eulerian circuit formalization | SimpleGraph, degree parity |

## Initial Thoughts

### Potential Approaches

1. **Hierholzer constructive algorithm**: Follow edges from any vertex greedily until returning to start, then extend by inserting sub-tours at vertices with unused edges.
   - Why it might work: Standard algorithm, well-understood, functional style
   - Risk: Termination proof requires well-founded induction on remaining edges

2. **Induction on edge count**: If every vertex has equal degree, find a cycle, remove it, apply induction.
   - Why it might work: Clean structural induction
   - Risk: Strong connectivity preservation after removing a cycle needs proof

### Key Difficulties

- Termination of Hierholzer's algorithm in Lean 4 (well-founded recursion on edge count)
- Showing the constructed walk visits every edge exactly once
- Directed graph API in Mathlib may differ from undirected (Quiver vs SimpleGraph)

### What Would a Proof Need?

- Key lemma 1: Strongly connected + equal degree → has a directed cycle
- Key lemma 2: Removing a cycle preserves the equal-degree property on remaining components
- Technical requirements: Mathlib directed graph types, `Finset.card` induction

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The algorithm is well-known with clear proof structure
- `konigsberg` (undirected case) already formalized in the gallery — techniques available
- Main challenge: well-founded recursion for Hierholzer's termination

**Estimated Effort**:
- Exploration: 1-2 days (API discovery, proof outline)
- If tractable: 3-5 days (full formalization)

## References

### Papers
- Hierholzer, C. (1873), "Über die Möglichkeit, einen Linienzug ohne Wiederholung zu umfahren"

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Euler` — Eulerian circuits
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
difficulty: medium
source: gallery-gap
created: 2026-04-23T11:40:52+02:00
```
