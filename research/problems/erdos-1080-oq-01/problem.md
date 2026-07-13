# Problem: Determine the exact exponent for f(n, ⌊n^(2/3)⌋)

**Slug**: erdos-1080-oq-01
**Created**: 2026-07-09T15:40:16-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Determine } \alpha \text{ such that } f(n, \lfloor n^{2/3} \rfloor) = \Theta(n^{\alpha}), \quad \text{where currently } \tfrac{16}{15} \le \alpha \le \tfrac{10}{9}.
$$

### Plain Language

Let $f(n, m)$ be the maximum number of edges in a bipartite graph on $n$ vertices, one part of size $m = \lfloor n^{2/3} \rfloor$, that contains neither a $C_4$ nor a $C_6$. De Caen–Székely showed this function grows superlinearly, with an upper bound of $O(n^{10/9})$ and Lazebnik–Ustimenko–Woldar improved the lower bound to $\Omega(n^{16/15})$. The exact growth exponent $\alpha$ is unknown, and this problem asks to pin it down.

### Why This Matters

Fixing the exponent would close a long-standing gap in extremal graph theory that has stood since the 1990s. It would sharpen our understanding of how forbidding short even cycles constrains edge density in imbalanced bipartite graphs, and it connects directly to algebraic constructions from finite geometry that realize the current best lower bounds.

## Known Results

### What's Already Proven

- De Caen–Székely (1992) upper bound $f(n, \lfloor n^{2/3}\rfloor) = O(n^{10/9})$ — Sets, Graphs and Numbers (Budapest, 1991), Colloq. Math. Soc. János Bolyai, Vol. 60
- Lazebnik–Ustimenko–Woldar (1994/1995) lower bound $\Omega(n^{16/15})$ via algebraic incidence-graph constructions — Bull. Amer. Math. Soc. 32(1), 73–79

### What's Still Open

- Whether the true exponent equals the upper bound $10/9$, the lower bound $16/15$, or some value strictly between them
- Whether a matching construction and matching counting argument can be produced to collapse the interval to a single value

### Our Goal

Formalize the current best-known bounds on $f(n, \lfloor n^{2/3}\rfloor)$ in Lean 4 and, where feasible, tighten either the upper or lower bound so the interval $[16/15, 10/9]$ shrinks toward a single exponent.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1080 | Parent problem; establishes the disproof and the superlinear bounds framing this open question | Bipartition predicates, cycle-free predicates, axiomatized LUW construction |
| erdos-1008 | Companion extremal question on $C_4$-free subgraphs | Forbidden-subgraph edge counting |
| erdos-113 | Extremal numbers and degeneracy of bipartite graphs | Turán-type density arguments |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Refine the De Caen–Székely counting argument to lower the $10/9$ upper exponent.
   - Why it might work: The upper bound relies on double-counting paths of length two and three; a tighter accounting of the imbalanced partition may sharpen the constant and possibly the exponent.
   - Risk: The $10/9$ bound may already be tight from above, making improvement impossible.

2. **Approach B**: Search for denser algebraic constructions than the LUW incidence graphs to raise the $16/15$ lower exponent.
   - Why it might work: New generalized polygon or projective-plane incidence structures could yield graphs with more edges while remaining $C_4,C_6$-free.
   - Risk: Known algebraic families appear to plateau near $16/15$, so a genuinely new construction may be required.

### Key Difficulties

- The gap between $16/15 \approx 1.0667$ and $10/9 \approx 1.1111$ is narrow, so both directions demand precise asymptotic control.
- Extremal constructions live in finite geometry, an area with limited Mathlib coverage.

### What Would a Proof Need?

- Key lemma 1: A clean Lean statement of $f(n,m)$ as a supremum of edge counts over $C_4,C_6$-free bipartite graphs.
- Key lemma 2: An asymptotic upper-bound lemma reproducing the $O(n^{10/9})$ counting argument.
- Technical requirements: Real-exponent asymptotics ($n^{\alpha}$) and incidence-graph combinatorics not yet in Mathlib.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Determining the exact exponent is a genuinely open research question that has resisted resolution since 1992.
- Similar extremal-Turán exponent problems (e.g., the Zarankiewicz function) remain open even for classical parameter ranges.
- Mathlib provides SimpleGraph, Walk, and cardinality infrastructure but no finite-geometry incidence graphs, so foundational scaffolding is required.

**Estimated Effort**:
- Exploration: several days
- If tractable: several weeks to formalize the known bounds
- If hard: unknown; closing the exponent gap is open research

## References

### Papers
- De Caen, D. and Székely, L. A., "The maximum size of 4- and 6-cycle-free bipartite graphs on n vertices", 1992 — establishes the $O(n^{10/9})$ upper and superlinear lower bounds
- Lazebnik, F., Ustimenko, V. A., and Woldar, A. J., "A new series of dense graphs of high girth", 1995 — improves the lower bound to $\Omega(n^{16/15})$

### Online Resources
- https://erdosproblems.com/1080 — canonical statement and status of Erdős Problem #1080

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Basic — simple graph structure for expressing bipartite graphs
- Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting — walks and cycles used to define $C_4,C_6$-freeness
- Mathlib.Data.Set.Card — set cardinality for defining the extremal function $f(n,m)$

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - extremal-graph-theory
  - bipartite-graphs
  - cycles
related_proofs:
  - erdos-1080
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:16-07:00
```
