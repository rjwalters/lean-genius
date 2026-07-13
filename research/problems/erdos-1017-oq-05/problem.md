# Problem: Hypergraph Extension of the Clique-Partition Number

**Slug**: erdos-1017-oq-05
**Created**: 2026-07-03
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{Define } f_r(H)\ =\ \min\ \{\, |\mathcal{C}| : \mathcal{C}\ \text{partitions the edge set of the } r\text{-uniform hypergraph } H\ \text{into complete sub-hypergraphs} \,\}.
$$

Determine the extremal function $f_r(n,k) = \max\{ f_r(H) : H\ \text{is } r\text{-uniform on } n\ \text{vertices with } k\ \text{edges} \}$, generalizing the graph case $r = 2$ (Erdős #1017).

### Plain Language

Erdős #1017 concerns partitioning the edges of a graph into cliques and studies $f(n,k) \le \lfloor n^2/4 \rfloor$. This sub-question asks whether the problem extends naturally to $r$-uniform hypergraphs: what is the minimum number of *complete sub-hypergraphs* needed to partition the edges of a $k$-uniform hypergraph, and what is the analogous extremal bound?

### Why This Matters

Clique-partition (Erdős–Goodman–Pósa) is a cornerstone of extremal graph theory. A hypergraph generalization tests whether the $\lfloor n^2/4 \rfloor$-type bounds and the Győri–Keszegh structural results are graph-specific or reflect a deeper extremal principle, and it opens a family of new extremal problems.

## Known Results

### What's Already Proven

- Graph clique-partition framework, partition number $f(n,k)$, and the EGP bound $f(n,k) \le \lfloor n^2/4 \rfloor$ — parent entry `erdos-1017`.
- Extremal example $K_{n/2,n/2}$ showing tightness; Győri–Keszegh theorem in the $K_4$-free case — parent entry.

### What's Still Open

- The correct definition and extremal value of $f_r(n,k)$ for $r \ge 3$.
- Whether an analogue of the $\lfloor n^2/4 \rfloor$ bound holds for hypergraphs.

### Our Goal

Formalize the $r$-uniform hypergraph clique-partition framework (complete sub-hypergraphs, the partition number $f_r$), prove basic bounds, and identify the first nontrivial extremal example for $r = 3$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1017 | Direct parent; supplies the graph clique-partition definitions and EGP bound | Extremal graph theory, `SimpleGraph` |

## Initial Thoughts

### Potential Approaches

1. **Direct generalization**: replace `SimpleGraph` cliques with complete $r$-uniform sub-hypergraphs and re-derive elementary bounds.
   - Why it might work: the definitional scaffolding mirrors the graph case.
   - Risk: Mathlib's hypergraph support is much thinner than `SimpleGraph`.

2. **Reduction / projection**: relate $f_3$ to $f_2$ via link graphs of vertices.
   - Why it might work: links convert hypergraph structure into graph structure.
   - Risk: partitions of links need not glue into a global hypergraph partition.

### Key Difficulties

- Mathlib lacks a mature $r$-uniform hypergraph API; much must be built.
- The right extremal example for $r = 3$ is not obvious.

### What Would a Proof Need?

- Key lemma 1: a formal `Hypergraph` / complete-sub-hypergraph definition and partition number.
- Key lemma 2: an elementary upper bound analogous to EGP.
- Technical requirements: `Finset`, set systems, extremal counting.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Substantial new infrastructure (hypergraph API) is required before extremal results.
- The parent graph framework provides a clear blueprint to generalize.
- A first milestone (definitions + basic bound) is realistic; sharp extremal values are hard.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- P. Erdős, A. Goodman, L. Pósa — representation of graphs by set intersections (EGP bound).
- E. Győri, B. Keszegh — clique partitions in $K_4$-free graphs.

### Online Resources
- Erdős Problems database, Problem #1017 — https://www.erdosproblems.com/1017

### Mathlib
- `SimpleGraph`, `SimpleGraph.IsClique` — starting point to generalize.
- `Finset` set-system infrastructure — for $r$-uniform edges.

## Metadata

```yaml
tags:
  - graph-theory
  - extremal-combinatorics
  - hypergraphs
  - erdos-problem
related_proofs:
  - erdos-1017
difficulty: high
source: proof-suggestion
created: 2026-07-03
```

**Significance**: 6/10
**Tractability**: 4/10
