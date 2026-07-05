# Problem: Formalize the Strong (Alon–Fischer–Krivelevich–Szegedy) Regularity Lemma

**Slug**: szemeredi-regularity-oq-04
**Created**: 2026-07-04T19:56:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For every function $\mathcal{E} : \mathbb{N} \to (0,1]$ and every $\varepsilon > 0$
there is $M = M(\varepsilon, \mathcal{E})$ such that every graph $G$ admits a
partition $V = V_1 \cup \dots \cup V_k$ ($k \le M$) and a refinement
$V = W_1 \cup \dots \cup W_\ell$ with:

$$
\text{(i) } W \text{ refines } V,\quad
\text{(ii) } (V_i) \text{ is } \varepsilon\text{-regular},\quad
\text{(iii) all but } \varepsilon\binom{\ell}{2} \text{ pairs } (W_a,W_b)
\text{ are } \mathcal{E}(k)\text{-regular}.
$$

That is: a coarse $\varepsilon$-regular partition together with a refinement that is
regular *for almost all pairs* with an error tolerance depending on the coarse
partition's size — far stronger than the classical single-$\varepsilon$ lemma.

### Plain Language

Szemerédi's regularity lemma says any graph can be partitioned so that most pairs
of parts look "random-like" at a fixed tolerance $\varepsilon$. The Alon–Fischer–
Krivelevich–Szegedy strengthening (2000) gives a two-level partition where the
regularity of the fine parts can be made arbitrarily good (tolerance
$\mathcal{E}(k)$ chosen *after* seeing the coarse partition), at the cost of an
$\varepsilon$-fraction of exceptional pairs. This "almost-all-pairs, arbitrary
precision" version powers graph property testing. We want it formalized in Lean 4.

### Why This Matters

The strong regularity lemma is the engine behind the graph-removal lemma with
better bounds and behind property-testing results (Alon–Shapira). It directly
extends the parent gallery entry `szemeredi-regularity`, whose energy-increment
machinery and Mathlib bridge are exactly the tools needed. Formalizing it turns
the gallery's regularity infrastructure into a reusable strengthened lemma.

## Known Results

### What's Already Proven

- Parent entry `szemeredi-regularity` — the classical regularity lemma with the
  energy-increment argument and a Mathlib bridge.
- Mathlib `SzemerediRegularity` — `Finpartition.exists_equipartition_card_eq` and
  the energy/uniformity API for the classical statement.
- AFKS (2000) — the strong regularity lemma itself (iterated application of the
  classical lemma with a decreasing tolerance).

### What's Still Open

- No formalization of the strong/iterated version exists in Mathlib.
- Explicit tower-type bounds on $M$ are not needed for the qualitative statement
  but must be tracked carefully to make the iteration terminate.

### Our Goal

Formalize the strong regularity lemma by iterating the classical lemma: apply it
to get a coarse $\varepsilon$-regular partition, then re-apply with tolerance
$\mathcal{E}(k)$ on a refinement, using the energy bound $0 \le q \le 1$ to cap the
number of iterations. Scope: the qualitative existence statement (i)–(iii),
building directly on Mathlib's classical regularity API.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| szemeredi-regularity | Parent: classical lemma + energy machinery | Energy increment, Finpartition |
| szemeredi-theorem | Downstream consumer of regularity | Counting lemma, removal lemma |

## Initial Thoughts

### Potential Approaches

1. **Iterate the classical lemma with bounded energy**: Each refinement step that
   fails almost-all-pairs regularity increases the mean-square density (energy) by
   a fixed amount; since energy is capped at $1$, only finitely many steps occur.
   - Why it might work: this is the standard proof and reuses Mathlib's energy API.
   - Risk: threading the tolerance function $\mathcal{E}(k)$ through the iteration
     and getting the refinement bookkeeping right in `Finpartition`.

2. **Direct energy-increment on the two-level partition**: Prove the statement in
   one energy argument over refinements rather than an explicit loop.
   - Why it might work: fewer moving parts.
   - Risk: harder to make the "chosen after seeing $k$" dependency rigorous.

### Key Difficulties

- Managing the dependent tolerance $\mathcal{E}(k)$ in a terminating induction.
- Refinement bookkeeping and the exceptional-pair accounting in Mathlib's
  `Finpartition` / `SzemerediRegularity` API.

### What Would a Proof Need?

- Key lemma 1: Classical regularity lemma as a black box (Mathlib provides it).
- Key lemma 2: Energy is nondecreasing under refinement and bounded by $1$,
  bounding the iteration count.
- Technical requirements: `Finpartition` refinement, the uniformity/energy lemmas.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Mathlib already has the classical lemma and energy machinery — a big head start.
- The strengthening is "just" a controlled iteration, but the dependent tolerance
  and refinement accounting make it a substantial formalization.
- The parent gallery entry supplies the exact bridge lemmas.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown (if the iteration bookkeeping resists)

## References

### Papers
- Alon, Fischer, Krivelevich, Szegedy, "Efficient testing of large graphs", *Combinatorica* 20 (2000) — the strong regularity lemma.
- Szemerédi, "Regular partitions of graphs" (1978) — the classical lemma.

### Online Resources
- Conlon–Fox, "Graph removal lemmas" survey — the strong lemma and its uses.

### Mathlib
- `Mathlib.Combinatorics.SzemerediRegularity.*` — classical lemma, energy, uniformity.
- `Mathlib.Order.Partition.Finpartition` — partitions and refinements.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - regularity-lemma
  - szemeredi
related_proofs:
  - szemeredi-regularity
difficulty: high
source: proof-suggestion
created: 2026-07-04T19:56:31-07:00
```

**Significance**: 7/10
**Tractability**: 4/10
