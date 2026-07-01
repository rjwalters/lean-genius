# Problem: Max-Cut of a Complete Bipartite Graph Equals the Full Edge Count

**Slug**: randomized-maxcut-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: randomized-maxcut

## Problem Statement

### Formal Statement

$$
\text{For any bipartite graph } G=(A\sqcup B,E):\quad \mathrm{maxcut}(G)=|E|,
\qquad\text{and in particular}\qquad
\mathrm{maxcut}(K_{m,n}) = m\cdot n .
$$

### Plain Language

The parent entry `randomized-maxcut` proves the probabilistic lower bound: a *uniformly
random* bipartition of any graph cuts, in expectation, at least half the edges, so
`maxcut(G) ≥ |E|/2`. This child proves the **exact, extremal** companion for the bipartite
case: if `G` is already bipartite with parts `A` and `B`, then the *specific* cut that puts
`A` on one side and `B` on the other cuts **every** edge, so `maxcut(G) = |E|` (the trivial
upper bound `maxcut(G) ≤ |E|` is met). Specialising to the complete bipartite graph
`K_{m,n}`, whose edge set has size `m·n`, gives `maxcut(K_{m,n}) = m·n`.

### Why This Matters

The parent's `≥ |E|/2` bound is tight for graphs like `K_n` but is far from tight for
bipartite graphs, where the true optimum is *all* of `|E|`. Making that gap precise pins
down the exact max-cut on the most important tractable family and gives a concrete family
witnessing that the `1/2` guarantee is a worst-case, not typical, bound. Mathlib has the
complete bipartite graph and its edge count but **no** named max-cut evaluation, so this is a
genuine assembly rather than a lookup.

## Known Results

### What's Already Proven

- Parent `randomized-maxcut` is verified (0-axiom): `𝔼[cut] = |E|/2`, hence
  `∃` a cut of size `≥ |E|/2`.
- Mathlib: `SimpleGraph.completeBipartiteGraph` and its adjacency; the two-block structure
  of a bipartite graph; `Finset.card` counting for `edgeFinset`.

### What's Still Open

- The two target theorems below (currently `sorry`). Mathlib has no `maxCut` evaluation for
  any concrete graph family.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**extremal / tightness completion**.

## Target Lean Sketch

```lean
open SimpleGraph Finset

/-- Value of the cut induced by a two-colouring `s : V → Bool`:
    the number of edges whose endpoints receive different colours. -/
def cutValue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → Bool) : ℕ :=
  (G.edgeFinset.filter (fun e => e.lift (fun a b => s a ≠ s b) (by decide))).card

/-- A bipartition of a bipartite graph cuts *every* edge, so the max cut equals |E|. -/
theorem bipartite_maxCut_eq_card_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : V → Bool)
    (hbip : ∀ ⦃a b⦄, G.Adj a b → s a ≠ s b) :
    cutValue G s = G.edgeFinset.card := by
  sorry
  -- Every edge {a,b} has G.Adj a b, hence s a ≠ s b by hbip, so the filter keeps ALL edges:
  -- `Finset.filter_true_of_mem` reduces the filtered card to `G.edgeFinset.card`.

/-- Max cut of the complete bipartite graph on `Fin m ⊕ Fin n` is `m * n`. -/
theorem maxCut_completeBipartite (m n : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin n)).edgeFinset.card = m * n := by
  sorry
  -- Edges of K_{m,n} biject with (Fin m) × (Fin n) via `Sum.inl a` ~ `Sum.inr b`;
  -- `Fintype.card_prod` + `Fintype.card_fin` give `m * n`. Combine with the previous
  -- theorem (using `s = Sum.isRight`) to read off `maxcut = m * n`.
```

Add worked `example`s: `K_{2,3}` has max cut `6`; the path `P_3` (bipartite, `2` edges) has
max cut `2`; contrast `K_3` where max cut is `2 < 3 = |E|` (not bipartite).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `randomized-maxcut` | Parent: random-cut `≥ |E|/2` bound | probabilistic method, expectation |
| `mantel-theorem` | Extremal edges in triangle-free (bipartite) graphs | extremal graph theory |
| `konigsberg` | Edge/degree counting on graphs | graph theory |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 5/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The bipartite half is a `filter_true_of_mem` reduction; the count for
`K_{m,n}` is a `Fintype.card_prod` computation. Both use only standard `Finset`/`Fintype`
machinery, no analysis.

### Suggested First Steps

1. Fix the `cutValue` definition and confirm it typechecks against Mathlib's `edgeFinset` and
   `Sym2` lift.
2. Prove `bipartite_maxCut_eq_card_edges` by showing the filter predicate holds on every edge
   (`Finset.filter_true_of_mem`).
3. Count `K_{m,n}` edges via a bijection to `Fin m × Fin n` and `Fintype.card_prod`.

## References

### Mathlib

- `SimpleGraph.completeBipartiteGraph` — Combinatorics/SimpleGraph/Basic.lean
- `SimpleGraph.edgeFinset`, `Finset.filter_true_of_mem` — Combinatorics/SimpleGraph/Finite.lean, Data/Finset/Basic.lean
- `Fintype.card_prod`, `Fintype.card_fin` — Data/Fintype/Card.lean, Data/Fintype/Basic.lean

### Literature

- Max-Cut is NP-hard in general (Karp), but exactly `|E|` on bipartite graphs; the complete
  bipartite optimum `m·n` is a standard textbook fact.

## Metadata

```yaml
tags:
  - graph-theory
  - randomized-maxcut
  - extremal-combinatorics
  - probabilistic-method
related_proofs:
  - randomized-maxcut
  - mantel-theorem
  - konigsberg
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
