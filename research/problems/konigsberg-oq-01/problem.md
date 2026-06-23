# Problem: Efficient Eulerian Path Finding (Hierholzer's Algorithm)

**Slug**: konigsberg-oq-01
**Created**: 2026-02-23T14:21:20-08:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given a connected graph G with exactly 0 or 2 vertices of odd degree,
Hierholzer's algorithm finds an Eulerian path in O(|E|) time.

Formally, we want to prove:
1. **Existence**: A connected graph has an Eulerian circuit iff all vertices have even degree; an Eulerian path iff exactly 2 vertices have odd degree.
2. **Construction**: Hierholzer's algorithm correctly constructs such a path/circuit.
3. **Efficiency**: The algorithm runs in linear time O(|E|).

### Plain Language

The Königsberg Bridge Problem showed that an Eulerian path exists iff exactly 0 or 2 vertices have odd degree. But *finding* such a path efficiently is the constructive next step.

Hierholzer's algorithm does this in linear time: start a trail from any vertex, splice in sub-trails at unexplored edges, and merge into a final Eulerian circuit/path.

We want to formalize this in Lean 4:
- Prove correctness (the output is indeed an Eulerian path)
- Possibly prove termination and complexity

### Why This Matters

The gallery proof already establishes *when* Eulerian paths exist (the necessary/sufficient degree condition). The natural next question is: *how do we find one efficiently?* Hierholzer's algorithm is the standard constructive answer, used in:
- DNA sequencing (genome assembly via de Bruijn graphs)
- Circuit board routing
- Network analysis

## Known Results

### What's Already Proven

- **Eulerian circuit condition** — `src/data/proofs/konigsberg/` — all vertices have even degree iff Eulerian circuit exists
- **Mathlib SimpleGraph.Eulerian** — Mathlib has some Eulerian path infrastructure
- **Hierholzer's algorithm** — classical, linear-time algorithm known since 1873

### What's Still Open (in Lean)

- Formal proof of Hierholzer's algorithm correctness in Lean 4
- Complexity bound formalization

### Our Goal

Formalize that a connected graph with an Eulerian path has a constructive algorithm (Hierholzer's) to find one. The primary goal is correctness; complexity is a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg | Direct parent: establishes existence condition | Graph degree counting, SimpleGraph |
| friendship-theorem | Graph theory formalization patterns | SimpleGraph, Finset |

## Initial Thoughts

### Potential Approaches

1. **Mathlib search**: Check if Mathlib.Combinatorics.SimpleGraph.Eulerian or similar already has Hierholzer
   - Why it might work: Mathlib is extensive, may have this
   - Risk: May not have constructive algorithm, only existence

2. **Constructive implementation**: Implement the algorithm as a computable function, prove it returns an Eulerian path
   - Why it might work: Algorithm is well-understood
   - Risk: Lean 4 termination proofs for imperative-style algorithms can be subtle

3. **Existence via induction**: Non-constructive proof that if conditions hold, a path can be assembled
   - Why it might work: Avoids algorithmic complexity
   - Risk: Doesn't give us the efficient construction

### Key Difficulties

- Lean termination proofs for graph traversal algorithms (need well-founded recursion)
- Representing a "trail" (sequence of edges, no edge repeated) formally
- Mathlib's graph representations may differ from what the algorithm needs

### What Would a Proof Need?

- Key lemma 1: If all vertices have even degree, we can always extend a non-closed trail
- Key lemma 2: The union of two edge-disjoint trails sharing a vertex can be merged
- Technical requirements: SimpleGraph, Walk, or Trail types in Mathlib

## Tractability Assessment

**Difficulty**: Medium (tractability 8/10)

**Justification**:
- Mathlib likely has Eulerian walk infrastructure via SimpleGraph.Walk
- The parent proof (Königsberg) already exists in the gallery
- Algorithm is classical and well-understood
- Lean 4 has good support for graph theory via Mathlib

**Estimated Effort**:
- Exploration (Mathlib survey): 1-2 days
- If Mathlib has pieces: 3-5 days to assemble
- Full from scratch: 2-3 weeks

## References

### Papers
- Hierholzer, C. (1873). "Uber die Moglichkeit, einen Linienzug ohne Wiederholung und ohne Unterbrechung zu umfahren." — original algorithm paper

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Walk — Walk, Trail, Path types
- Mathlib.Combinatorics.SimpleGraph.Connectivity — connectivity
- Search for Eulerian in Mathlib

## Metadata

```yaml
tags:
  - graph-theory
  - algorithms
  - eulerian-paths
related_proofs:
  - konigsberg
difficulty: medium
source: gallery-gap
created: 2026-02-23T14:21:20-08:00
```

**Significance**: 7/10
**Tractability**: 8/10
