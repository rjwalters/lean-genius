# Problem: Property B Lower Bound m(k) ≥ 2^(k−1) via the First Moment

**Slug**: prob-method-applications-wip-01-oq-02
**Created**: 2026-07-04T19:56:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
m(k) \;\ge\; 2^{\,k-1}
$$

where $m(k)$ is the minimum number of edges in a $k$-uniform hypergraph that is
**not** 2-colorable (i.e. that fails Property B). Equivalently: any $k$-uniform
hypergraph with fewer than $2^{k-1}$ edges admits a proper 2-coloring (no
monochromatic edge).

### Plain Language

Property B asks whether the edges of a hypergraph can be 2-colored with no edge
monochromatic. Erdős's first-moment argument shows that if a $k$-uniform
hypergraph has fewer than $2^{k-1}$ edges, a uniformly random 2-coloring leaves,
in expectation, fewer than one monochromatic edge — so some coloring has none.
This gives the classical lower bound $m(k) \ge 2^{k-1}$. We want it formalized in
Lean 4, derived from the parent entry's existence engine.

### Why This Matters

This is the textbook first application of the probabilistic method and a direct
consumer of the parent gallery entry `prob-method-applications-wip-01`, whose
`exists_good_of_card_bound` lemma packages exactly the first-moment existence step
("if the expected number of bad events is $< 1$, a good outcome exists"). Deriving
$m(k) \ge 2^{k-1}$ from it demonstrates the engine on a canonical target and
yields a clean, fully verified combinatorics result — a rare *tractable* extension.

## Known Results

### What's Already Proven

- Parent entry `prob-method-applications-wip-01` — the first-moment existence
  engine, including `exists_good_of_card_bound`.
- Erdős (1963/1964): $m(k) \ge 2^{k-1}$ via the union bound / first moment.
- Upper bounds $m(k) = O(k^2 2^k)$ (Erdős) and refinements (Radhakrishnan–Srinivasan
  $\Omega(2^k\sqrt{k/\log k})$) — not needed here, context only.

### What's Still Open

- The exact value of $m(k)$ is unknown for $k \ge 4$ (only $m(2)=3$, $m(3)=7$ known).
- This task targets only the lower bound $2^{k-1}$, which is fully elementary.

### Our Goal

Formalize $m(k) \ge 2^{k-1}$: show any $k$-uniform hypergraph with $< 2^{k-1}$
edges is 2-colorable, by applying the parent entry's `exists_good_of_card_bound`
with the monochromatic-edge count as the bad-event count (each edge is
monochromatic under a random 2-coloring with probability $2 \cdot 2^{-k} =
2^{1-k}$, so expected bad edges $= |E| \cdot 2^{1-k} < 1$). Scope: the lower bound,
reusing the existing engine — no new probabilistic infrastructure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-applications-wip-01 | Parent: supplies `exists_good_of_card_bound` | First moment / union bound |
| prob-method-tournament | Sibling first-moment application | Expectation, counting |

## Initial Thoughts

### Potential Approaches

1. **Instantiate `exists_good_of_card_bound` directly**: Set the "bad events" to be
   "edge $e$ is monochromatic", each with a $2^{1-k}$ probability under uniform
   random coloring; the card bound $|E| < 2^{k-1}$ makes the expected count $< 1$.
   - Why it might work: the parent lemma is designed for exactly this shape.
   - Risk: matching the parent lemma's exact hypotheses (probability space model,
     counting vs. probability formulation) may need light adaptation.

2. **Self-contained counting argument**: Count colorings with a monochromatic edge
   directly ($\le |E| \cdot 2 \cdot 2^{n-k}$ out of $2^n$) and show it is $< 2^n$.
   - Why it might work: purely finite, avoids probability-space plumbing.
   - Risk: duplicates machinery the parent entry already provides.

### Key Difficulties

- Aligning the monochromatic-edge probability $2^{1-k}$ with the parent lemma's
  interface (whether it takes a probability or an expected count).
- Modeling a "$k$-uniform hypergraph" and "2-coloring" cleanly in Lean.

### What Would a Proof Need?

- Key lemma 1: Each edge is monochromatic under a uniform 2-coloring w.p. $2^{1-k}$.
- Key lemma 2: The parent `exists_good_of_card_bound` (expected bad $< 1 \Rightarrow$
  a good coloring exists).
- Technical requirements: `Finset.card`, uniform coloring counting, the parent API.

## Tractability Assessment

**Difficulty**: Medium (Low if the parent lemma slots in directly)

**Justification**:
- The whole argument is one application of an existing, verified lemma.
- No new probabilistic infrastructure is required — this is the intended use case
  of `exists_good_of_card_bound`.
- The remaining work is modeling hypergraph 2-colorings and the counting bound.

**Estimated Effort**:
- Exploration: hours
- If tractable: days
- If hard: weeks (only if the parent interface needs significant adaptation)

## References

### Papers
- Erdős, "On a combinatorial problem", *Nordisk Mat. Tidskr.* (1963) — the $2^{k-1}$ lower bound.
- Alon & Spencer, *The Probabilistic Method*, Ch. 1 — Property B as the opening example.

### Online Resources
- Wikipedia, "Property B" — statement, known bounds, and the first-moment proof.

### Mathlib
- `Mathlib.Combinatorics.*` — hypergraph / finset modeling.
- `Mathlib.Probability.*` or the parent entry's engine — first-moment existence.

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - property-b
  - hypergraph-coloring
related_proofs:
  - prob-method-applications-wip-01
difficulty: medium
source: proof-suggestion
created: 2026-07-04T19:56:31-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
