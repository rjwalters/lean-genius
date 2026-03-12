# Problem: Directed Euler Paths

**Slug**: konigsberg
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{A directed graph } G \text{ has an Eulerian path iff it is connected and}
$$
$$
\forall v,\; \text{in-deg}(v) = \text{out-deg}(v) \text{ except possibly two vertices where}
$$
$$
\text{out-deg}(s) - \text{in-deg}(s) = 1 \text{ and } \text{in-deg}(t) - \text{out-deg}(t) = 1
$$

### Plain Language

Characterize when a directed graph has an Eulerian path (a path that uses every edge exactly once). The answer: in-degree must equal out-degree for all vertices except possibly two, where one has one extra outgoing edge (the start) and one has one extra incoming edge (the end).

### Why This Matters

Directed Euler paths are fundamental in combinatorics and have applications in DNA sequencing (de Bruijn sequences), circuit design, and algorithm design. This is the natural directed extension of the classic Konigsberg bridge result.

## Known Results

### What's Already Proven

- Undirected Eulerian circuit/path characterization — `proofs/Proofs/KonigsbergBridge*.lean`
- Mathlib has `SimpleGraph` and basic walk infrastructure

### What's Still Open

- Directed graph Eulerian path characterization in Lean
- Connection between undirected and directed versions

### Our Goal

Formalize the directed Eulerian path theorem: existence iff connected + degree balance condition.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg | Source proof — undirected case | Graph walks, degree counting |

## Initial Thoughts

### Potential Approaches

1. **Direct proof via walk construction**: Build the path greedily, prove it uses all edges
   - Why it might work: Standard textbook proof
   - Risk: Walk manipulation in Lean can be complex

2. **Reduction to undirected case**: Transform directed graph, apply known result
   - Why it might work: Reuses existing formalization
   - Risk: The transformation is non-trivial

### Key Difficulties

- Mathlib's directed graph infrastructure may be less developed than undirected
- Walk/path manipulation in dependent type theory

### What Would a Proof Need?

- Directed graph type with in/out degree
- Directed walk/trail/path definitions
- Degree-sum arguments for directed graphs

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Well-known textbook result
- Existing undirected formalization to build on
- Mathlib has some digraph infrastructure

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - euler-paths
related_proofs:
  - konigsberg
difficulty: medium
source: gallery-gap
created: 2026-03-06
```
