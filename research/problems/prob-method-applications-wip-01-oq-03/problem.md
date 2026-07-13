# Problem: Probabilistic Method — Tournament Domination Bound

**Slug**: prob-method-applications-wip-01-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

A *tournament* on $n$ vertices is an orientation of $K_n$ (equivalently a point of the
sample space $2^{\binom{n}{2}}$). A set $S$ of vertices is *dominating* if every vertex
$v \notin S$ loses to some member of $S$. Erdős's first-moment bound: if

$$
\binom{n}{k}\bigl(1 - 2^{-k}\bigr)^{\,n-k} < 1,
$$

then there exists a tournament on $n$ vertices with **no** dominating set of size $k$.

Concretely, bound the number of tournaments that *do* have a dominating $k$-set: for a
fixed $k$-set $S$, the number of tournaments in which $S$ dominates is at most
$\bigl(1-2^{-k}\bigr)^{\,n-k}\,2^{\binom{n}{2}}$, so summing over all $\binom{n}{k}$
choices of $S$ gives a count $< 2^{\binom{n}{2}}$ under the hypothesis — hence some
tournament avoids all of them.

### Plain Language

In a round-robin tournament, call a group of players "dominating" if every other player
loses to at least one of them. It is a classic surprise that for any target size $k$
there are tournaments in which *no* group of $k$ players dominates — someone always beats
all of them. We prove this by counting: tournaments with a dominating $k$-set are too few
to fill up the space of all tournaments, so a tournament with no small dominating set must
exist.

### Why This Matters

This is one of the canonical first-moment (counting) applications of the probabilistic
method (Erdős 1963), sitting beside the Ramsey lower bound already formalized in the
parent. It exercises the parent's *existence engine* on a genuinely different event
structure (per-vertex domination rather than monochromatic cliques), showing the engine is
reusable and turning yet another textbook "vacuous placeholder" into an honest,
fully-counted existence theorem.

## Known Results

### What's Already Proven

- `exists_good_of_card_bound` (parent `prob-method-applications-wip-01`) — if the total number of "bad" configurations is below the size of the sample space, a configuration avoiding all bad events exists. This is exactly the engine this problem instantiates.
- `card_supersets_le`, `card_disjoint_le`, `card_mono_le` (parent) — counting subsets of a sample space by a local constraint; the template for the "$S$ dominates" count.
- `ramsey_avoidance` (parent) — the sibling instantiation for Ramsey; a worked example of the same pattern.
- Mathlib: `Finset.card_powersetCard`, `Nat.choose`, `Finset.prod`/`card` of product sample spaces, `Finset.card_le_card`, `Finset.card_biUnion_le`.

### What's Still Open

- This problem: the tournament-domination instantiation.
- A quantitative version giving the smallest $n$ for each $k$ (follow-on).

### Our Goal

Formalize the sample space of tournaments on `Fin n` (functions assigning an orientation
to each unordered pair, i.e. `Finset` of the edge set as in the parent's colouring setup),
define the "$S$ dominates" event, bound its cardinality by
$(1-2^{-k})^{n-k} 2^{\binom n2}$, and feed the union bound into
`exists_good_of_card_bound` to conclude the existence of an undominated tournament under
the stated inequality.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-applications-wip-01 | Parent; provides the union-bound existence engine and counting lemmas | `exists_good_of_card_bound`, `card_mono_le` |
| prob-method-applications-wip-01-oq-01 | Sibling instantiation (Ramsey numeric bound) | first-moment counting |
| prob-method-lovasz-local | Alternative dependency-aware existence tool | Lovász Local Lemma |
| prob-method-expectation | First-moment/expectation framing | linearity of expectation |

## Initial Thoughts

### Potential Approaches

1. **Direct union bound via the parent engine**: Take the sample space to be tournaments (the parent's `Finset E` colouring model, with `E` = edges of $K_n$). For each $k$-set $S$, `A S` = tournaments in which $S$ dominates. Bound `(A S).card`, sum over $S$, apply `exists_good_of_card_bound`.
   - Why it might work: it is precisely the pattern the engine was built for; the Ramsey sibling is a template.
   - Risk: the per-$S$ count $(1-2^{-k})^{n-k}$ is a product over the $n-k$ outside vertices of "not all $k$ edges point out," which is fiddlier than the clique count.

2. **Vertex-wise complementary count**: For fixed $S$ and outside vertex $v$, $v$ is *undominated by $S$* iff $v$ beats all $k$ members of $S$ — exactly one pattern out of $2^k$ on those $k$ edges. Multiply independent per-$v$ factors to get $(1-2^{-k})^{n-k}$ for "$S$ dominates."
   - Why it might work: reduces the count to a clean product of independent per-vertex events.
   - Risk: formalizing the independence/product-of-counts step over the outside vertices.

### Key Difficulties

- Modeling tournaments and the domination event as `Finset` cardinalities in a way that matches the parent's counting API.
- The $(1-2^{-k})^{n-k}$ factor is a product bound; keeping it exact (or a clean upper bound) through the sum over $k$-sets.

### What Would a Proof Need?

- Key lemma 1: for a fixed $k$-set $S$, `card {tournaments : S dominates} ≤ (1-2^{-k})^{n-k} · 2^{C(n,2)}`.
- Key lemma 2: union bound `card {∃ dominating k-set} ≤ C(n,k) · (1-2^{-k})^{n-k} · 2^{C(n,2)}` (from Key lemma 1 + `Finset.card_biUnion_le`).
- Technical requirements: the hypothesis $\binom{n}{k}(1-2^{-k})^{n-k} < 1$ in a Lean-usable real/rational form; `exists_good_of_card_bound`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The existence engine and the analogous Ramsey counting are already in the gallery — this is a re-instantiation, not new machinery.
- The mathematical content is a standard textbook result (Alon & Spencer, *The Probabilistic Method*, §1.2; Erdős 1963).
- The one real cost is the domination-event cardinality bound, which is a per-vertex product count rather than the parent's simpler clique count.

**Estimated Effort**:
- Exploration: hours to set up the tournament sample space matching the parent's model.
- If tractable: 2–4 days for the counting lemma + union bound + engine application.
- If hard: longer if the product-of-per-vertex-counts step resists the existing counting API.

## References

### Papers
- Erdős, "On a problem in graph theory," *Math. Gazette* 47 (1963) — the original tournament domination example.
- Alon & Spencer, *The Probabilistic Method*, §1.2 (tournaments, property $S_k$).

### Online Resources
- Wikipedia, "Probabilistic method" — tournament/property $S_k$ worked example.

### Mathlib
- `Finset.card_biUnion_le` — the union bound.
- `Finset.card_powersetCard`, `Nat.choose` — counting $k$-sets.
- `Finset.prod`, `Finset.card` of function/product sample spaces — per-vertex product counts.

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - tournaments
  - first-moment
related_proofs:
  - prob-method-applications-wip-01
  - prob-method-applications-wip-01-oq-01
  - prob-method-lovasz-local
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```
