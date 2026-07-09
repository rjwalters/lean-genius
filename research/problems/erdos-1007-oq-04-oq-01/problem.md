# Problem: Sharp maximum graph dimension as a function of (n, m)

**Slug**: erdos-1007-oq-04-oq-01
**Created**: 2026-07-09T16:03:13-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $\dim(G)$ denote the (Euclidean) dimension of a graph $G$: the least $d$ such that $G$ admits a unit-distance embedding $f : V(G) \to \mathbb{R}^d$ with $\lVert f(u) - f(v)\rVert = 1$ for every edge $uv$. For integers $n \ge 1$ and $0 \le m \le \binom{n}{2}$, define the extremal function

$$
D(n, m) \;=\; \max\bigl\{\, \dim(G) : |V(G)| = n,\ |E(G)| = m \,\bigr\}.
$$

Determine $D(n, m)$ exactly, together with the extremal graph families that attain it. The known brackets are

$$
D(n, m) \;\le\; \min\bigl(\, n - 1,\ 2m \,\bigr),
$$

with $D\!\left(n, \binom{n}{2}\right) = n - 1$ realized by the complete graph $K_n$ (regular simplex). The problem is to close the gap between these two upper bounds and the true value across the full parameter range, especially in the sparse regime $m = o(n^2)$ where neither bound is generally tight.

### Plain Language

Every graph can be drawn in some Euclidean space so that adjacent vertices land exactly one unit apart; the graph's *dimension* is the fewest coordinates you need to do this. A complete graph on $n$ vertices needs $n-1$ dimensions (the vertices of a regular simplex), and no $n$-vertex graph needs more. On the other hand, a graph with only $m$ edges never needs more than $2m$ dimensions. This problem asks for the *exact* largest dimension achievable once you fix both the number of vertices $n$ and the number of edges $m$, and which graphs achieve it — sharpening the two coarse bounds $n-1$ and $2m$ into a single precise extremal function.

### Why This Matters

- It is the concrete extremal core of Erdős Problem #1007 (open question OQ-04): the dependence of graph dimension on the *pair* $(n, m)$, not on $n$ alone.
- Answering it would unify and extend the sporadic exact results known only for small target dimensions (House 2013 for dimension 4; Chaffee–Noble 2016 for dimension 5) into a global formula.
- Unit-distance embeddings connect combinatorics to discrete/metric geometry (the Erdős unit-distance problem, rigidity theory, and the chromatic number of the plane); a sharp $D(n,m)$ would give a clean quantitative handle on how "geometrically complex" a sparse graph can be.

## Known Results

### What's Already Proven

- $\dim(K_n) = n - 1$ via the regular simplex — gallery proof `erdos-1007-oq-01` (fully verified in Lean 4).
- Subgraph monotonicity ($\dim$ never increases under edge deletion, so the max over $n$-vertex graphs is $K_n$, giving $n-1$) and the edge-count bound $\dim(G) \le 2\,|E(G)|$ (handshake lemma on the non-isolated support) — gallery proof `erdos-1007-oq-04` (verified).
- Chromatic bound $\dim(G) \le \chi(G) \le n$ (a proper coloring is a separating index map); in particular bipartite $\Rightarrow \dim \le 2$ — gallery proof `erdos-1007-oq-04`.
- Sharp small-dimension extremal thresholds: a $4$-dimensional graph has $\ge 9$ edges, with $K_{3,3}$ the unique minimizer (House 2013); the dimension-$5$ analogue (Chaffee–Noble 2016).

### What's Still Open

- The exact value of $D(n, m)$ for general $(n, m)$, i.e. a closed-form extremal function interpolating between the $n-1$ and $2m$ regimes.
- The extremal graph families attaining $D(n, m)$ in the sparse regime $m = o(n^2)$.
- The sharp constant in the edge-count direction: is $2m$ improvable to (roughly) the non-isolated support size $\le \sqrt{2m}\cdot(\text{const})$-type bounds for dense-locally graphs, and what is the truth for triangle-free / bipartite graphs?

### Our Goal

Rather than the full closed form (a genuine open problem), our attainable target is to *tighten and formalize the brackets*: (a) prove an improved upper bound in the sparse regime (e.g. replacing $2m$ with a bound in terms of the number of non-isolated vertices, or $O(\sqrt{m})$-type refinements where structure permits), and (b) formalize a concrete extremal *family* — such as complete bipartite $K_{s,t}$ or disjoint-simplex unions — that exhibits dimension provably above any constant while $m = o(n^2)$, thereby lower-bounding $D(n,m)$ and pinning down its order of magnitude in a nontrivial slice of the $(n,m)$ plane.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1007-oq-04 | Parent entry: proves the two framing bounds $\dim(G)\le n-1$ (via monotonicity + $K_n$) and $\dim(G)\le 2m$, plus $\dim(G)\le\chi(G)$ | scaled-basis index embedding, subgraph monotonicity, handshake lemma, proper colorings |
| erdos-1007-oq-01 | Establishes $\dim(K_n)=n-1$ (regular simplex), the tight upper corner $D(n,\binom{n}{2})$ | simplex geometry, affine independence, distance computation |
| erdos-1007-oq-05-oq-01 | Sibling: monotonicity and the edgeless base case of graph dimension | unit-distance embedding, base-case constructions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Support/coloring refinement of the $2m$ bound**: The current $2m$ bound comes from bounding the non-isolated support $S$ by $\sum \deg = 2m$. But $\dim(G) \le \min(|S|, \chi(G))$ already. Combine with structural extremal graph theory: for triangle-free or bipartite graphs $\chi \le 2$ collapses the bound dramatically, and for bounded-degeneracy graphs a smarter separating index map (greedy coloring using degeneracy) gives $\dim(G) \le \mathrm{col}(G)$.
   - Why it might work: the embedding engine only needs an edge-separating index map, and the least such is exactly $\chi(G)$; any coloring-type upper bound transfers directly.
   - Risk: $\chi(G)$ can be as large as $\Theta(\sqrt{m})$ for dense-locally graphs, so this refines but does not close the gap; the true $D(n,m)$ may lie below $\chi$.

2. **Approach B — Extremal lower-bound families**: Compute $\dim(K_{s,t})$ and unions of simplices to lower-bound $D(n,m)$. A disjoint union of $t$ copies of $K_{k+1}$ has $n=t(k+1)$, $m=t\binom{k+1}{2}$, and dimension $k$ (embed the copies in orthogonal blocks / or overlay — need the union dimension law). This yields families with $m=\Theta(n)$ and $\dim = \Theta(1)$ per component but growing with block size.
   - Why it might work: explicit constructions give unconditional lower bounds and can be matched against the upper bounds to detect tightness.
   - Risk: determining $\dim$ of a *union* or of $K_{s,t}$ exactly is itself nontrivial (there is no simple additivity; overlapping embeddings can save dimensions).

3. **Approach C — Rigidity / rank characterizations**: Relate $\dim(G)$ to the rank of an associated Gram/stress matrix or to the maximum over induced subgraph "simplex ranks", then optimize this rank quantity over $(n,m)$-graphs.
   - Why it might work: rank-based invariants are amenable to double-counting and eigenvalue bounds tying dimension to spectral/edge data.
   - Risk: the exact link between unit-distance dimension and any single algebraic rank is delicate (unit-distance is not affine).

### Key Difficulties

- Graph dimension is *not* additive, subadditive in an obvious way, nor monotone in $m$ at fixed $n$ in a form that pins the extremal function; it depends on fine structure (e.g. $K_{3,3}$ jumps to dimension 4 with only 9 edges).
- The extremal graphs in the sparse regime are irregular (House's minimizer is $K_{3,3}$, not a "generic" sparse graph), so guessing the extremal family is hard.
- No clean Mathlib API yet exists for the graph (Euclidean) dimension as an $\mathbb{N}$-valued invariant; everything is phrased via the `hasUnitEmbedding` predicate at a fixed ambient dimension.

### What Would a Proof Need?

- Key lemma 1: a union/join dimension law — bounds for $\dim(G_1 \sqcup G_2)$ and $\dim(G_1 \vee G_2)$ in terms of the pieces (to build and analyze extremal families).
- Key lemma 2: an exact or near-exact formula for $\dim(K_{s,t})$ (partially classical; $\dim(K_{2,2})=2$, $\dim(K_{3,3})=4$) generalized to a clean function of $s,t$.
- Technical requirements: a reusable `dim`/least-embedding-dimension definition on top of `hasUnitEmbedding`, monotonicity and $\min$-of-bounds infrastructure, and Mathlib's chromatic-number and degeneracy machinery for the coloring refinements.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full closed form $D(n,m)$ is a genuinely open Erdős-problem sub-question; only sporadic exact cases (target dimension 4, 5) are known after decades.
- However, *tightening the brackets* and *formalizing an extremal family* are self-contained, verifiable sub-goals well within reach of the existing gallery machinery (the scaled-basis embedding engine + Mathlib coloring/handshake lemmas already discharge related bounds in `erdos-1007-oq-04`).
- Mathlib provides `SimpleGraph.chromaticNumber`, `SimpleGraph.sum_degrees_eq_twice_card_edges`, and coloring/degeneracy tools that directly support Approach A.

**Estimated Effort**:
- Exploration: 3–5 days (survey House 2013 / Chaffee–Noble, decide on a tractable slice).
- If tractable (a refined bound or an extremal family): 2–4 weeks to formalize.
- If hard (the full closed form): unknown / open.

## References

### Papers
- Erdős, P.; Harary, F.; Tutte, W. T. — *On the dimension of a graph*, Mathematika 12 (1965), 118–122 — introduces the Euclidean dimension of a graph.
- House, J. — *A 4-dimensional graph has at least 9 edges*, Discrete Mathematics 313(18) (2013), 1783–1789 — sharp $(n,m)$ extremal result at target dimension 4; $K_{3,3}$ unique minimizer.
- Chaffee, J.; Noble, M. — dimension-5 extremal analogue (2016) — sharp edge threshold for dimension 5.

### Online Resources
- https://www.erdosproblems.com/1007 — Erdős Problem #1007 and its open questions (OQ-04 is this direction).

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` — `sum_degrees_eq_twice_card_edges` (handshake lemma) for support/edge-count bounds.
- `Mathlib.Combinatorics.SimpleGraph.Coloring` — `chromaticNumber`, proper colorings, giving the $\dim(G)\le\chi(G)$ refinement.
- `Mathlib.Analysis.InnerProductSpace.EuclideanDist` / `EuclideanSpace` — ambient $\mathbb{R}^d$ and unit-distance computations.

## Metadata

```yaml
tags:
  - graph-theory
  - metric-geometry
  - unit-distance
  - graph-dimension
  - euclidean-embedding
  - extremal-graph-theory
related_proofs:
  - erdos-1007-oq-04
  - erdos-1007-oq-01
  - erdos-1007-oq-05-oq-01
difficulty: high
source: user-request
created: 2026-07-09T16:03:13-07:00
```
