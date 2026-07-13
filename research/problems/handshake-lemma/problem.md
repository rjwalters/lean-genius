# Problem: Handshake Lemma — Sum of Vertex Degrees Equals Twice the Edge Count

**Slug**: handshake-lemma
**Created**: 2026-07-05T00:06:20-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\sum_{v \in V} \deg(v) = 2\,|E|
$$

In Lean:

```lean
theorem handshake (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    (∑ v, G.degree v) = 2 * G.edgeFinset.card
```

### Plain Language

In any finite simple graph, adding up the degrees of all vertices counts every
edge exactly twice (once from each endpoint), so the total is twice the number of
edges. The classical corollary — the "handshaking lemma" proper — is that the
number of vertices with odd degree is always even.

### Why This Matters

- One of the first structural theorems in graph theory and the prototypical
  double-counting argument.
- The odd-degree corollary is the standard textbook consequence and a clean
  parity result worth formalizing alongside the identity.
- Fills a gap: the gallery's graph-theory entries lean toward extremal/Erdős
  problems and lack this elementary degree-sum foundation.

## Known Results

### What's Already Proven

- `SimpleGraph.sum_degrees_eq_twice_card_edges (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : (∑ v, G.degree v) = 2 * G.edgeFinset.card`
  — the identity is already in Mathlib.
- `SimpleGraph.even_card_odd_degree_vertices` — Mathlib's formalization of the
  odd-degree parity corollary.
- `SimpleGraph.degree`, `SimpleGraph.edgeFinset`, `SimpleGraph.dart` machinery
  (the identity is proved by counting darts / directed edges).

### What's Still Open

- Nothing mathematically open; goal is a clean, self-contained gallery entry that
  states the identity, derives the odd-degree-parity corollary, and optionally
  illustrates with a small concrete graph.

### Our Goal

A verified, sorry-free, axiom-free Lean file proving the degree-sum identity and
the even-number-of-odd-degree-vertices corollary, with clear annotations
explaining the double-counting argument.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| konigsberg | Uses degree parity to rule out an Euler walk | `SimpleGraph.degree`, parity |
| euler-polyhedral-formula | Finite graph combinatorics | edge/vertex counting |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib citation**: apply `SimpleGraph.sum_degrees_eq_twice_card_edges`
   and `SimpleGraph.even_card_odd_degree_vertices`.
   - Why it might work: both results already exist; effort is packaging + exposition.
   - Risk: essentially none.

2. **Dart double-counting from scratch**: sum over `G.dart`, use that each edge
   corresponds to two darts.
   - Why it might work: mirrors Mathlib's own proof and is pedagogically clean.
   - Risk: more work than the direct citation for no mathematical gain.

### Key Difficulties

- None substantial. Need the right `Fintype`/`DecidableRel` instances in scope so
  `degree` and `edgeFinset` are computable.

### What Would a Proof Need?

- `SimpleGraph.sum_degrees_eq_twice_card_edges`.
- `SimpleGraph.even_card_odd_degree_vertices` (or derive parity from the identity
  via `Finset.even_sum` / `Nat.even_add`).

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Both the identity and its parity corollary are already in Mathlib.
- The formalization is a citation-plus-exposition entry.

**Estimated Effort**:
- Exploration: < 1 hour
- If tractable: a few hours for packaging, a small worked example, and annotations

## References

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` —
  `SimpleGraph.sum_degrees_eq_twice_card_edges`,
  `SimpleGraph.even_card_odd_degree_vertices`.

## Metadata

```yaml
tags:
  - graph-theory
  - combinatorics
  - degree-sum
related_proofs:
  - konigsberg
difficulty: low
source: gallery-gap
created: 2026-07-05T00:06:20-07:00
```

**Significance**: 5/10
**Tractability**: 8/10
