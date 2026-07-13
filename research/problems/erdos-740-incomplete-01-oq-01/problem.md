# Problem: Rödl's Theorem (𝔪 = ℵ₀, r = 3) — Triangle-Free Subgraphs of Countably Infinite Chromatic Number

**Slug**: erdos-740-incomplete-01-oq-01
**Created**: 2026-07-09T15:40:17-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\,G,\ \chi(G) = \aleph_0 \implies \exists\, H \subseteq G,\ \big(\text{$H$ is triangle-free}\big) \wedge \chi(H) = \aleph_0 .
$$

Here $G$ ranges over (possibly infinite) simple graphs, $\chi$ denotes the chromatic number as a cardinal, "triangle-free" means $H$ contains no $K_3$ (no odd cycle of length $\le 3$), and $H \subseteq G$ is a subgraph of $G$.

### Plain Language

Erdős Problem #740 asks: if a graph has chromatic number equal to an infinite cardinal 𝔪, and we fix a bound r, must the graph contain a subgraph of the same chromatic number 𝔪 that avoids all short odd cycles (odd cycles of length at most r)? Rödl proved the first genuine positive instance: when the chromatic number is exactly ℵ₀ (countably infinite) and r = 3, such a subgraph always exists. In other words, every graph whose chromatic number is countably infinite contains a *triangle-free* subgraph whose chromatic number is still countably infinite. This is the smallest nontrivial case of the general Erdős–Hajnal question, and it is the positive counterpart to the (settled, negative) bipartite/r = ∞ boundary case handled by the parent gallery entry.

### Why This Matters

The parent gallery proof `erdos-740-incomplete-01` settles the *negative* extreme of #740: the bipartite (r = ∞) case fails, because a bipartite graph has χ ≤ 2 and so can never realize a large chromatic number. That leaves the substantive *positive* content of #740 — the finite-r regime where subgraphs of full chromatic number really do exist — completely unformalized. Rödl's 1977 theorem is exactly the base case of that positive theory (𝔪 = ℵ₀, r = 3). Formalizing it would: (1) turn the gallery's coverage of #740 from "boundary-only" into genuine engagement with the hard direction; (2) exercise Mathlib's infinite-graph and cardinal-valued chromatic-number machinery on a real combinatorial construction rather than an elementary bound; and (3) provide reusable infrastructure (triangle-freeness, chromatic number as a cardinal, subgraph extraction) for the wider Erdős–Hajnal program on chromatic numbers of subgraphs.

## Known Results

### What's Already Proven

- Bipartite (r = ∞) case of #740 fails — parent entry `erdos-740-incomplete-01` (`Proofs/Erdos740BipartiteIncomplete01.lean`): χ(bipartite) ≤ 2, so χ(G) > 2 admits no induced bipartite subgraph realizing χ(G).
- Rödl (1977): a graph of chromatic number ℵ₀ contains a triangle-free subgraph of chromatic number ℵ₀ — the target theorem, proved on paper but not in Lean.
- Monotonicity of χ under graph homomorphisms and `χ(G.induce s) ≤ χ(G)` — Mathlib `SimpleGraph.chromaticNumber_mono_of_hom` and the parent entry's `induce_chromaticNumber_le`.
- χ(Kₙ) = n and the finite complete-graph witnesses — Mathlib `SimpleGraph.chromaticNumber_top`, used by the parent entry.

### What's Still Open

- The general Erdős #740 for arbitrary infinite 𝔪 and arbitrary finite r ≥ 3 remains open (Erdős listed it among problems he most wished to see solved).
- No Lean formalization exists of Rödl's countable case, nor of the underlying construction extracting a triangle-free subgraph while preserving infinite chromatic number.

### Our Goal

Formalize, in Lean 4 over Mathlib, the single positive statement of Rödl's theorem for 𝔪 = ℵ₀ and r = 3: every simple graph G with chromatic number ℵ₀ admits a subgraph H that is triangle-free and still has chromatic number ℵ₀. We target this specific case only — not the general infinite-cardinal or larger-r versions, which stay open. A staged path (state the theorem, build the triangle-freeness and cardinal-χ scaffolding, then the extraction argument) is expected.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-740-incomplete-01 | Parent entry; settles the negative r = ∞ boundary case with real χ | χ monotone under homomorphisms, induced-subgraph bound, bipartite χ ≤ 2 |
| erdos-740 | Original #740 formalization using a placeholder chromatic number | Cardinal-valued χ scaffolding, odd-cycle avoidance framing |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Direct formalization of Rödl's original construction — iteratively remove/reroute edges of triangles while tracking a lower bound on chromatic number.
   - Why it might work: it follows the published proof and stays close to the combinatorial content.
   - Risk: infinite bookkeeping (transfinite/inductive edge removal) is delicate to formalize; preserving χ = ℵ₀ across the construction is the crux and may need careful cardinal arithmetic.

2. **Approach B**: Reduce to a Mathlib-friendly reformulation — express "χ = ℵ₀" via colorability failing for every finite palette, and extract the triangle-free subgraph as a suitable limit / subgraph selected by compactness-style reasoning.
   - Why it might work: Mathlib has colorability and cardinal infrastructure; phrasing χ = ℵ₀ as "not Colorable n for all finite n, but Colorable ℵ₀" may make the χ lower bound tractable.
   - Risk: the compactness/limit step for infinite graphs may not be directly available in Mathlib and could require substantial new supporting lemmas.

### Key Difficulties

- Preserving countably infinite chromatic number while deleting all triangles is the entire mathematical content; it is not an elementary bound.
- Mathlib's chromatic-number API is strongest for finite/ℕ∞-valued χ; working with χ as a genuine cardinal ℵ₀ on infinite vertex types may expose gaps.

### What Would a Proof Need?

- Key lemma 1: a workable predicate for "triangle-free" (no `K₃` subgraph / no 3-clique) with lemmas relating it to subgraph passage.
- Key lemma 2: a cardinal-valued chromatic-number lower bound that survives the triangle-removing construction (χ(H) ≥ ℵ₀).
- Technical requirements: infinite-graph subgraph selection, cardinal arithmetic at ℵ₀, and a faithful encoding of Rödl's extraction step in Mathlib.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The result is a genuine (non-elementary) combinatorial theorem about infinite graphs, unlike the parent entry's elementary χ ≤ 2 bound.
- Mathlib's infinite-graph and cardinal-χ tooling is thinner than its finite-graph coloring API, so supporting infrastructure will likely need to be built.
- Related finite chromatic-number results are formalizable, but the transfinite extraction preserving χ = ℵ₀ has no direct Mathlib analogue.

**Estimated Effort**:
- Exploration: several days
- If tractable: several weeks
- If hard: unknown

## References

### Papers
- Rödl, V., "On the chromatic number of subgraphs of a given graph", Proc. Amer. Math. Soc. 64 (1977), 370–371 — proves the 𝔪 = ℵ₀, r = 3 case (triangle-free subgraph of countable chromatic number).
- Erdős, P., "On the combinatorial problems which I would most like to see solved", Combinatorica 1 (1981), 25–42 — lists #740 among Erdős's most-wanted problems.
- Erdős, P. and Hajnal, A., "On chromatic number of graphs and set-systems", Acta Math. Acad. Sci. Hungar. 17 (1966), 61–99 — origin of the chromatic-subgraph question.

### Online Resources
- https://erdosproblems.com/740 — statement and status of Erdős Problem #740.

### Mathlib
- Mathlib.Combinatorics.SimpleGraph.Coloring — chromatic number, `chromaticNumber_mono_of_hom`, colorability.
- Mathlib.Combinatorics.SimpleGraph.Clique — cliques and triangle (`K₃`) predicates for triangle-freeness.
- Mathlib.SetTheory.Cardinal.Basic — cardinal arithmetic at ℵ₀ for the chromatic-number lower bound.

## Metadata

```yaml
tags:
  - erdos
  - graph-theory
  - chromatic-number
  - triangle-free
  - odd-cycles
  - induced-subgraph
  - research
related_proofs:
  - erdos-740-incomplete-01
  - erdos-740
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:17-07:00
```
