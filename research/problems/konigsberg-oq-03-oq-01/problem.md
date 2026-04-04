# Problem: Erdős-Grünwald-Weiszfeld Theorem for Infinite Graphs

**Slug**: konigsberg-oq-03-oq-01
**Created**: 2026-04-04T02:41:19-07:00
**Status**: Active
**Source**: konigsberg-oq-03 <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

Can the Erdős-Grünwald-Weiszfeld theorem be proved in Lean for locally finite countable graphs? The key step is constructing an Euler path as a limit of finite Euler paths on increasing subgraphs — a compactness argument.

### Formal Statement

$$
\text{For a locally finite, countable, connected graph } G \text{ with all vertices of even degree,}
\text{ there exists an Eulerian path.}
$$

### Plain Language

The Erdős-Grünwald-Weiszfeld theorem extends the classical Eulerian path result (König's bridge problem) to infinite graphs. For a locally finite countable graph where every vertex has even degree, we want to prove an Euler path exists by constructing it as a limit of finite Euler paths on increasing finite subgraphs.

### Why This Matters

This is a fundamental result connecting finite combinatorics (Euler paths) with infinite graph theory and compactness arguments. Formalizing it in Lean would demonstrate Mathlib's capability to handle infinite combinatorial structures.

## Known Results

### What's Already Proven

- Eulerian paths in finite graphs — classical result in gallery (konigsberg-oq-03)
- Eulerian paths in hypergraphs — gallery proof konigsberg-oq-03

### What's Still Open

- Lean formalization of infinite Euler paths for locally finite countable graphs
- Compactness argument constructing path as limit of finite paths

### Our Goal

Prove the Erdős-Grünwald-Weiszfeld theorem for locally finite countable graphs in Lean 4, using a compactness argument over finite subgraphs.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg-oq-03 | Parent proof: Eulerian Paths in Hypergraphs and Infinite Graphs | Graph theory, Euler circuits |

## Initial Thoughts

### Potential Approaches

1. **Compactness limit**: Construct Euler paths on finite subgraphs and take a limit
   - Why it might work: Standard proof technique
   - Risk: Mathlib may lack the needed API for infinite path limits

2. **König's lemma**: Use König's infinity lemma to extract infinite path
   - Why it might work: Direct combinatorial argument
   - Risk: Requires locally finite assumption to be encoded precisely

### Key Difficulties

- Lean formalization of "infinite path" semantics
- Mathlib support for locally finite infinite graphs
- Compactness arguments in the combinatorial setting

### What Would a Proof Need?

- Key lemma 1: Infinite path type using Stream or codata
- Key lemma 2: König's lemma or compactness in Mathlib
- Technical requirements: Locally finite graph typeclass

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is classical but requires significant Lean infrastructure
- Infinite path formalization is a prerequisite (see konigsberg-oq-03-oq-02)
- Mathlib's graph API may need extension

**Estimated Effort**:
- Exploration: 2-3 days
- If tractable: 1-2 weeks
- If hard: unknown

## References

### Papers
- Erdős, Grünwald, Weiszfeld — original theorem on Euler paths in infinite graphs

### Online Resources
- Mathlib SimpleGraph API documentation

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph` — graph API
- `Mathlib.Data.Stream` — infinite sequences

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - infinite-graphs
  - euler-paths
related_proofs:
  - konigsberg-oq-03
  - konigsberg-oq-03-oq-02
difficulty: challenging
source: konigsberg-oq-03
category: extension
created: 2026-04-04T02:41:19-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
