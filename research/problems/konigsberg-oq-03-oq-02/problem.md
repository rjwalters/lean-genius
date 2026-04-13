# Problem: Infinite Path Formalization in Lean

**Slug**: konigsberg-oq-03-oq-02
**Created**: 2026-04-04T02:41:19-07:00
**Status**: Active
**Source**: konigsberg-oq-03 <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

Is there a clean Lean formalization of "infinite path" (bi-infinite or one-way infinite) in a graph using Mathlib's `Stream` or `Path` API? The `HasInfiniteEulerPath` stub needs this semantic foundation before the theorem can be stated precisely.

### Formal Statement

$$
\text{Define a type } \text{InfinitePath}(G) \text{ representing a one-way or bi-infinite walk in graph } G
\text{ visiting each edge exactly once.}
$$

### Plain Language

Before we can prove theorems about infinite Euler paths, we need a clean definition of what an "infinite path" means in Lean 4. This involves choosing the right type (Stream, Nat-indexed sequence, or codata) and encoding the path's edge-traversal constraint.

### Why This Matters

This is a foundational definitional problem. The `HasInfiniteEulerPath` stub in the gallery cannot be stated precisely without a solid definition of infinite paths. Getting this right unlocks the Erdős-Grünwald-Weiszfeld theorem formalization.

## Known Results

### What's Already Proven

- Finite paths in Mathlib's SimpleGraph API
- Stream API for infinite sequences in Mathlib

### What's Still Open

- Clean definition of infinite graph paths using Mathlib's existing API
- Edge-traversal constraints (visiting each edge exactly once) for infinite paths

### Our Goal

Define a usable `InfinitePath` or `InfiniteWalk` type in Lean 4 that integrates with Mathlib's `SimpleGraph` and supports the Eulerian path predicate.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg-oq-03 | Parent proof: Eulerian Paths in Hypergraphs and Infinite Graphs | Graph theory, path types |
| konigsberg-oq-03-oq-01 | Sibling: Erdős-Grünwald-Weiszfeld theorem needs this definition | Infinite graphs |

## Initial Thoughts

### Potential Approaches

1. **Stream-based**: Define path as `Stream (G.Dart)` with adjacency constraint
   - Why it might work: Mathlib has Stream API; natural for one-way infinite paths
   - Risk: Edge-uniqueness constraint may be hard to encode coinductively

2. **Nat-indexed**: Define path as `f : Nat → G.Dart` with constraints
   - Why it might work: Simple type, easy to work with
   - Risk: Less elegant; bi-infinite case requires `Int → G.Dart`

### Key Difficulties

- Encoding the "each edge visited exactly once" constraint for infinite paths
- Choosing between one-way and bi-infinite paths
- Integration with existing Mathlib SimpleGraph API

### What Would a Proof Need?

- Key lemma 1: Equivalence of different infinite path encodings
- Key lemma 2: Compactness/limit construction compatibility
- Technical requirements: SimpleGraph.Walk extensions in Mathlib

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Definitional work without heavy mathematics
- Mathlib's SimpleGraph API has finite path support to extend
- Main challenge is design choices, not deep mathematics

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 3-5 days
- If hard: 1-2 weeks

## References

### Papers
- Mathlib SimpleGraph documentation

### Online Resources
- Lean 4 Mathlib SimpleGraph module

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Walk` — finite walk/path types
- `Mathlib.Data.Stream.Init` — infinite stream types

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - infinite-graphs
  - lean-formalization
related_proofs:
  - konigsberg-oq-03
  - konigsberg-oq-03-oq-01
difficulty: challenging
source: konigsberg-oq-03
category: extension
created: 2026-04-04T02:41:19-07:00
```

**Significance**: 7/10
**Tractability**: 7/10
