# Problem: Improved Erdős–Pósa Bounds for Odd Cycles

**Slug**: erdos-73-oq-02
**Created**: 2026-07-09T15:22:58-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, C > 0 \;\; \forall\, G,\, k:\quad \nu_{\mathrm{odd}}(G) \le k \;\Longrightarrow\; \tau_{\mathrm{odd}}(G) \le C\, k \log k,
$$

where $\nu_{\mathrm{odd}}(G)$ is the maximum number of vertex-disjoint odd cycles in $G$ (the odd-cycle *packing* number) and $\tau_{\mathrm{odd}}(G)$ is the minimum size of an *odd cycle transversal* — a set of vertices meeting every odd cycle (equivalently, a set whose deletion makes $G$ bipartite). The Erdős–Pósa property for odd cycles asserts that $\tau_{\mathrm{odd}}(G) \le f(\nu_{\mathrm{odd}}(G))$ for some function $f$ independent of $G$; the goal is to formalize and sharpen the best known bounding function $f$.

### Plain Language

An *odd cycle* is a closed loop through a graph using an odd number of edges; a graph is bipartite (2-colorable) exactly when it has no odd cycle. Two natural quantities measure "how far from bipartite" a graph is:

- **Packing** $\nu_{\mathrm{odd}}$: how many odd cycles you can find that share no vertices.
- **Transversal** $\tau_{\mathrm{odd}}$: how few vertices you must delete to destroy *all* odd cycles at once.

Clearly $\nu_{\mathrm{odd}} \le \tau_{\mathrm{odd}}$ (each disjoint cycle needs its own deletion). The Erdős–Pósa property says the reverse inequality holds up to a function: if you cannot pack many disjoint odd cycles, then a small transversal suffices. The question is *how small* — what is the true growth of the smallest valid $f(k)$? We aim to formalize the packing–transversal duality and the currently best bound $f(k) = O(k \log k)$.

### Why This Matters

The gap between packing and covering is quantitatively the content of Reed's theorem behind Erdős Problem #73 (see [`erdos-73`](../erdos-73/)): the $k$-independence condition bounds $\nu_{\mathrm{odd}}(G)$, and the odd-cycle Erdős–Pósa bound converts this into a bounded odd cycle transversal, i.e. an "almost bipartite" graph with bipartite deficiency $\le f(k)$. Improving $f$ directly improves the deficiency bound $f(k) \le 2^k$ recorded for Erdős #73. Beyond that, odd-cycle Erdős–Pósa bounds control the constants in fixed-parameter algorithms for **Odd Cycle Transversal** and **Maximum Bipartite Subgraph**, and the odd/even distinction is a canonical example separating "well-behaved" cases (the classical Erdős–Pósa theorem for arbitrary cycles gives $f(k) = O(k \log k)$) from cases where no such bound exists at all (odd cycles fail Erdős–Pósa in non-planar / non-highly-connected settings).

## Known Results

### What's Already Proven

- **Erdős–Pósa theorem for cycles** (Erdős & Pósa 1965) — every graph either contains $k$ vertex-disjoint cycles or a set of $O(k \log k)$ vertices meeting all cycles; the $k\log k$ order is tight. Cited as `EP1965` in the parent proof.
- **Reed's theorem / Erdős #73** ([`erdos-73`](../erdos-73/), Reed 1999, "Mangoes and Blueberries") — graphs satisfying the $k$-independence condition are bipartite plus $O_k(1)$ vertices, giving $f(k) \le 2^k$ for the deficiency. Odd-cycle Erdős–Pósa duality is the engine of this proof.
- **Odd Erdős–Pósa in highly connected / planar graphs** (Reed 1999; Rautenbach–Reed 2001; Kawarabayashi–Nakamoto–Ota) — odd cycles *do* have the Erdős–Pósa property with $f(k) = O(k \log k)$ once one restricts to planar graphs or to graphs of large connectivity, or when a bounded "clique-sum" structure is imposed.
- **Failure without such hypotheses** (Reed 1999; Dejter–Neumann-Lara) — in general graphs odd cycles do *not* have the Erdős–Pósa property: there exist graphs with $\nu_{\mathrm{odd}} = 1$ but $\tau_{\mathrm{odd}}$ arbitrarily large (Escher-wall / projective-planar constructions).

### What's Still Open

- The optimal growth rate of $f(k)$ under the structural hypotheses where odd-cycle Erdős–Pósa holds: is $O(k \log k)$ tight, or does a linear $O(k)$ bound suffice?
- Whether the deficiency bound for Erdős #73 can be reduced from exponential $2^k$ toward polynomial or linear in $k$ by improving the effective odd-cycle transversal constant.

### Our Goal

Formalize, on top of the `erdos-73` framework, the **packing–transversal chain** for odd cycles:

1. The trivial direction $\nu_{\mathrm{odd}}(G) \le \tau_{\mathrm{odd}}(G)$ (a transversal hits each disjoint cycle).
2. The definition of an odd cycle transversal as exactly a set whose deletion yields a bipartite graph, tying $\tau_{\mathrm{odd}}(G)$ to `bipartiteDeficiency G` already defined in `Erdos73Problem.lean`.
3. A stated Erdős–Pósa bound $\tau_{\mathrm{odd}}(G) \le f(\nu_{\mathrm{odd}}(G))$ (axiomatized, mirroring `reed_bound`/`reed_theorem`) with the explicit $O(k \log k)$ growth under the structural hypothesis, and the corollary that this bounds `bipartiteDeficiency`.

This isolates a self-contained, formalizable slice — the duality inequality and the deficiency identity are provable; the quantitative bound is stated as a named axiom exactly as the parent proof treats Reed's theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-73 | Direct parent: Reed's almost-bipartite theorem uses odd-cycle Erdős–Pósa; defines `bipartiteDeficiency`, `isAlmostBipartite`, `hasNoOddCycle` reused here | Independence number, bipartite partitions, odd-cycle obstruction, axiomatized structural bound |
| erdos-106 | Chromatic-number / $\chi$-boundedness connection: an odd cycle transversal of size $t$ gives $\chi(G) \le t+2$ | Graph coloring, chromatic bounds |
| erdos-47 | Ramsey-type local-to-global structural results of similar flavor (bounded local obstruction forces global structure) | Extremal/Ramsey combinatorics, packing arguments |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Duality skeleton on the existing definitions**: Prove $\nu_{\mathrm{odd}}(G) \le \tau_{\mathrm{odd}}(G)$ and the identity `bipartiteDeficiency G = τ_odd(G)` directly in the `Erdos73` namespace, then state the Erdős–Pósa upper bound as an axiom `oddEP_bound : ℕ → ℕ` with `oddEP_theorem : ν_odd G ≤ k → bipartiteDeficiency G ≤ oddEP_bound k`.
   - Why it might work: The easy inequality and the deficiency identity are finite combinatorial statements over `Fintype V`, matching the existing formalization style; the hard analytic bound is quarantined into a single clearly-labeled axiom, exactly as `reed_theorem` is handled.
   - Risk: Defining "vertex-disjoint odd cycles" and the packing number `ν_odd` cleanly in Mathlib's `SimpleGraph.Walk`/`IsCycle` API is fiddly (odd length via `w.length` parity, vertex-disjointness of a family of walks).

2. **Approach B — Instantiate on planar/small cases to sanity-check the constant**: Formalize the tight lower-bound witness for the classical $k \log k$ (a disjoint union / blow-up of odd cycles giving $\nu_{\mathrm{odd}} = k$, $\tau_{\mathrm{odd}} = k$) and a small failure example ($\nu_{\mathrm{odd}} = 1$ but large $\tau_{\mathrm{odd}}$) to pin down that no bound holds without hypotheses.
   - Why it might work: Concrete small graphs ($K_3$ blow-ups) are already the modeling style of the parent proof (`triangleGraph`), so witnesses are within reach.
   - Risk: The genuine large-$\tau_{\mathrm{odd}}$, small-$\nu_{\mathrm{odd}}$ constructions (projective-planar Escher walls) are hard to encode; only the toy direction is realistically formalizable.

### Key Difficulties

- Expressing the **odd-cycle packing number** $\nu_{\mathrm{odd}}$ as a max over families of pairwise vertex-disjoint odd cycles in Mathlib's walk/cycle API.
- The tight $\Omega(k \log k)$ lower bound and the failure constructions are graph-theoretically intricate and not obviously reducible to `decide`-style tactics.
- Keeping axiom hygiene: the quantitative Erdős–Pósa bound must be an explicit named axiom (per the Axiom Integrity Policy), not silently smuggled into a structure field.

### What Would a Proof Need?

- Key lemma 1: `oddCycleTransversal` predicate and the identity `τ_odd(G) = bipartiteDeficiency G` (deleting a transversal ⇔ making bipartite via the existing `IsBipartite` / `hasNoOddCycle` definitions).
- Key lemma 2: the easy duality $\nu_{\mathrm{odd}}(G) \le \tau_{\mathrm{odd}}(G)$ via a pigeonhole/injection from a disjoint odd-cycle family into any transversal.
- Key lemma 3 (axiom): `ν_odd G ≤ k → τ_odd G ≤ C·k·log k` under the structural hypothesis, plus the corollary bounding `bipartiteDeficiency`.
- Technical requirements: a workable parity predicate on `SimpleGraph.Walk` length, `Finset`-based cardinality bookkeeping for the transversal, and interop with the parent file's `Fintype V` setup.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full optimal bound is a genuine open research question, so only the duality skeleton + axiomatized bound is realistically machine-checkable — but the true growth rate is unresolved in the literature.
- The parent proof (`erdos-73`) demonstrates the viable pattern: prove the easy structural facts, axiomatize the deep quantitative theorem. That template lowers risk for the formalizable slice.
- Mathlib provides `SimpleGraph.Walk.IsCycle`, walk length/parity, and `Finset.card` machinery, but has no built-in odd-cycle packing/transversal theory, so those definitions must be built from scratch.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–2 weeks (duality inequality + deficiency identity + axiomatized bound)
- If hard: unknown (the tight optimal constant is open research)

## References

### Papers
- Erdős, P. and Pósa, L., "On independent circuits contained in a graph", Canadian Journal of Mathematics 17 (1965), 347–352 — introduces the Erdős–Pósa property; $O(k\log k)$ bound for general cycles.
- Reed, B., "Mangoes and Blueberries", Combinatorica 19(2) (1999), 267–296 — odd-cycle Erdős–Pósa under connectivity/planarity; the almost-bipartite theorem of Erdős #73.
- Rautenbach, D. and Reed, B., "The Erdős–Pósa property for odd cycles in highly connected graphs", Combinatorica 21(2) (2001), 267–278 — $O(k\log k)$ transversal for odd cycles in sufficiently connected graphs.
- Kawarabayashi, K. and Nakamoto, A. and Ota, K., "Subgraphs of graphs on surfaces with high representativity", and related work on odd Erdős–Pósa on surfaces — structural cases where the property holds.
- Thomassen, C., "The Erdős–Pósa property for odd cycles in graphs of large connectivity", Combinatorica 21(2) (2001), 321–333 — connectivity threshold guaranteeing the odd-cycle bound.

### Online Resources
- https://erdosproblems.com/73 — Erdős Problem #73 statement and status (solved by Reed 1999).
- https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93P%C3%B3sa_theorem — overview of the Erdős–Pósa property, including the odd-cycle refinement and its failure in general graphs.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting` — `Walk`, `IsCycle`, walk length for defining odd cycles and their parity.
- `Mathlib.Combinatorics.SimpleGraph.Subgraph` — induced subgraphs and vertex deletion for defining transversals.
- `Mathlib.Combinatorics.SimpleGraph.Basic` — adjacency, `IsBipartite`-style partitions reused from the parent file.
- `Mathlib.Data.Finset.Card` — cardinality bookkeeping for packing/transversal sizes.

## Metadata

```yaml
tags:
  - graph-theory
  - structural-graph-theory
  - independent-sets
  - bipartite-graphs
  - erdos-posa
related_proofs:
  - erdos-73
  - erdos-106
  - erdos-47
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:58-07:00
```
