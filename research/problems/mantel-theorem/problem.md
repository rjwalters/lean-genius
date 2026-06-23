# Problem: Mantel's Theorem (Maximum Edges in Triangle-Free Graphs)

**Slug**: mantel-theorem
**Created**: 2026-06-15T12:01:04-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{If a simple graph } G \text{ on } n \text{ vertices contains no triangle } (K_3\text{-free}),
$$
$$
\text{then } |E(G)| \le \left\lfloor \frac{n^2}{4} \right\rfloor,
$$
$$
\text{with equality iff } G \cong K_{\lfloor n/2\rfloor,\, \lceil n/2\rceil}.
$$

### Plain Language

Among all graphs on $n$ vertices that contain no triangle, the one with the most edges is the
complete bipartite graph splitting the vertices into two halves as evenly as possible, and it
has $\lfloor n^2/4 \rfloor$ edges. You cannot do better without forcing a triangle.

### Why This Matters

Mantel's theorem (1907) is the founding result of extremal graph theory and the $r = 2$ base
case of Turán's theorem. Its proof techniques — vertex-weight shifting, the AM–GM bound on
$d(u)d(v)$, and Cauchy–Schwarz on degree sequences — recur throughout the field (Kővári–Sós–
Turán, the Erdős–Stone theorem, flag algebras). It is a clean, self-contained target that
exercises Mathlib's `SimpleGraph` extremal infrastructure.

## Known Results

### What's Already Proven

- Turán's theorem and `IsTuranMaximal` — `Mathlib.Combinatorics.SimpleGraph.Turan`.
- `SimpleGraph.cliqueFree`, edge counts via `SimpleGraph.edgeFinset` / `degree` — Mathlib.
- Complete multipartite / `turanGraph` constructions — Mathlib.

### What's Still Open

- A direct, citable Mantel statement ($K_3$-free $\Rightarrow |E| \le \lfloor n^2/4\rfloor$, with the bipartite equality case) as a standalone gallery theorem, rather than only as a corollary buried inside the general Turán development.

### Our Goal

Prove the edge bound $|E(G)| \le \lfloor n^2/4 \rfloor$ for triangle-free $G$ on `Fin n`, and
characterize equality as the balanced complete bipartite graph. Deriving it as a specialization
of Mathlib's `isTuranMaximal` (with $r = 2$) is an acceptable and likely the fastest route; a
self-contained AM–GM/degree-sum proof is the fallback.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| friendship-theorem | extremal/structural constraints on simple graphs | eigenvalue/counting arguments |
| erdos-565-incomplete-01 | Ramsey/extremal edge-coloring on graphs | edge colorings, counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — specialize Turán**: Instantiate Mathlib's `isTuranMaximal` / `turanGraph` at $r = 2$ and translate "$2$-colorable extremal graph" into the $\lfloor n^2/4\rfloor$ edge count.
   - Why it might work: reuses a fully formalized, verified theorem; minimal new mathematics.
   - Risk: bridging Turán's `cliqueFree (r+1)` formulation to "triangle-free = $K_3$-free" and extracting the explicit edge count and equality case may be more plumbing than expected.

2. **Approach B — degree-sum / AM–GM**: For each edge $uv$, neighborhoods of $u$ and $v$ are disjoint, so $d(u) + d(v) \le n$; sum over edges and apply Cauchy–Schwarz to $\sum d(v)^2$.
   - Why it might work: elementary, self-contained, classic.
   - Risk: formalizing the $\sum_{uv\in E}(d(u)+d(v)) = \sum_v d(v)^2$ identity and the Cauchy–Schwarz step in `Finset` form.

### Key Difficulties

- Extracting the explicit $\lfloor n^2/4 \rfloor$ value and the equality characterization from Mathlib's general Turán API.
- `Finset` degree-sum identities and floor arithmetic for odd vs even $n$.

### What Would a Proof Need?

- Key lemma 1: triangle-free $\Rightarrow$ for every edge $uv$, $N(u) \cap N(v) = \varnothing$, hence $d(u)+d(v)\le n$.
- Key lemma 2: $\sum_{uv \in E} (d(u)+d(v)) = \sum_v d(v)^2$ and Cauchy–Schwarz lower bound $\sum d(v)^2 \ge (\sum d(v))^2/n$.
- Technical requirements: `SimpleGraph.degree`, `edgeFinset`, `cliqueFree`, `Finset.inner_mul_le_norm` style Cauchy–Schwarz.

## Tractability Assessment

**Difficulty**: Medium (Low if the Turán specialization route works cleanly)

**Justification**:
- Mathlib already contains the harder Turán theorem; Mantel is its simplest instance.
- Both routes use standard, well-supported `SimpleGraph`/`Finset` APIs.
- The equality case is the most delicate part but is also covered structurally by `IsTuranMaximal` uniqueness.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3-7 days
- If hard: 2 weeks (mainly the equality characterization)

## References

### Papers
- Mantel, "Problem 28," *Wiskundige Opgaven* 10 (1907) — original.
- Turán, "On an extremal problem in graph theory" (1941) — the generalization.
- Aigner & Ziegler, *Proofs from THE BOOK* — multiple short proofs of Mantel.

### Online Resources
- Mathlib `Combinatorics.SimpleGraph.Turan` module docs — `IsTuranMaximal`, `turanGraph`.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Turan` — Turán's theorem, extremal graph, uniqueness.
- `Mathlib.Combinatorics.SimpleGraph.Clique` — `cliqueFree`, `CliqueFree`.
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` — handshake lemma, degree sums.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - extremal-combinatorics
related_proofs:
  - friendship-theorem
  - erdos-565-incomplete-01
difficulty: medium
source: gallery-gap
created: 2026-06-15T12:01:04-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
