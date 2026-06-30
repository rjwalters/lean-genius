# Problem: Erdős–Simonovits Stability for Triangle-Free Graphs

**Slug**: mantel-theorem-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
G \text{ triangle-free},\ |E(G)| \ge \left\lfloor n^2/4 \right\rfloor - o(n^2)
\implies G \text{ is } o(n^2)\text{-close to } K_{\lfloor n/2\rfloor,\lceil n/2\rceil}.
$$

### Plain Language

Mantel's theorem says a triangle-free graph on n vertices has at most ⌊n²/4⌋ edges, with equality only for the balanced complete bipartite graph. The stability strengthening (Erdős–Simonovits) says this extremal example is essentially unique even approximately: any triangle-free graph whose edge count is within o(n²) of the maximum can be turned into the balanced complete bipartite graph K_{⌊n/2⌋,⌈n/2⌉} by adding/deleting only o(n²) edges. The goal is to formalize this structural statement.

### Why This Matters

The gallery already contains the extremal count (`mantel-theorem`). Stability is the natural and important next layer: it upgrades a numerical bound to a structural characterization and is the prototype for the general Erdős–Simonovits stability method used throughout extremal graph theory. Formalizing it builds reusable infrastructure for "near-extremal configurations are near-extremal structures" arguments.

## Known Results

### What's Already Proven

- `mantel-theorem` — the extremal edge bound |E(G)| ≤ ⌊n²/4⌋ for triangle-free G, with the balanced complete bipartite extremizer.
- Mathlib's `SimpleGraph` library provides edge sets, cliques/triangle-freeness (`CliqueFree`), and complete bipartite graphs.

### What's Still Open

- A formal notion of "o(n²)-close" (edit distance between graphs on a common vertex set) suitable for stating stability.
- The stability theorem itself, not currently in Mathlib or the gallery.

### Our Goal

State and prove the stability theorem for the triangle-free (K₃-free) case: near-extremal triangle-free graphs are edit-close to a balanced complete bipartite graph. A first concrete target is the exact-stability corollary (within a constant number of edges of the max forces exact bipartite structure), then the asymptotic o(n²) form.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| mantel-theorem | Provides the extremal bound this result stabilizes | Triangle-freeness, edge counting, complete bipartite extremizer |

## Initial Thoughts

### Potential Approaches

1. **Exact stability first.** Prove that a triangle-free graph with ⌊n²/4⌋ − c edges differs from a complete bipartite graph by O(c) edges, then push to the asymptotic statement.
   - Why it might work: avoids defining limiting/asymptotic notions up front; gives a clean inductive/extremal argument.
   - Risk: the constant-bookkeeping can be fiddly to formalize.

2. **Max-degree vertex / neighborhood argument.** Take a maximum-degree vertex v; its neighborhood is an independent set in a triangle-free graph, giving a near-bipartition; bound the non-conforming edges.
   - Why it might work: classical short proof of Mantel adapts to give structure.
   - Risk: turning the counting slack into an explicit edit bound requires care.

### Key Difficulties

- Choosing a workable formal definition of approximate closeness (edit distance vs. a fixed bipartition) that keeps the proof tractable in Lean.
- Handling the asymptotic o(n²) quantifier cleanly; an exact/constant-slack version may be the right first milestone.

### What Would a Proof Need?

- Key lemma 1: in a triangle-free graph the neighborhood of any vertex is independent.
- Key lemma 2: a near-balanced bipartition captures all but o(n²) edges when the edge count is near-maximal.
- Technical requirement: a formal edit-distance / closeness predicate on `SimpleGraph` over a fixed `Fin n`.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The base theorem (`mantel-theorem`) is already formalized, supplying the extremal toolkit.
- Stability proofs are well understood on paper, but the asymptotic form needs new formal scaffolding (closeness/edit distance).
- An exact-stability milestone is genuinely tractable; the full o(n²) statement is harder.

**Estimated Effort**:
- Exploration: days (settle the right closeness definition).
- If tractable: weeks for exact stability.
- If hard: unknown for the full asymptotic statement.

## References

### Papers
- Erdős & Simonovits, "Supersaturated graphs and hypergraphs" and related stability works.
- Mantel (1907), original triangle-free edge bound.

### Online Resources
- Standard extremal-graph-theory lecture notes on the stability method.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Clique` — `CliqueFree`, triangle-freeness.
- `Mathlib.Combinatorics.SimpleGraph.Basic` / edge sets, complete bipartite graphs.

## Metadata

```yaml
tags:
  - combinatorics
  - extremal-graph-theory
  - mantel-theorem
  - stability
  - triangle-free
related_proofs:
  - mantel-theorem
difficulty: high
source: gallery-gap
created: 2026-06-16
```
