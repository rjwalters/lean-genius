# Problem: Erdős–Gallai Characterisation of Graphical Degree Sequences

**Slug**: handshake-lemma-oq-02
**Created**: 2026-07-05T03:14:24-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

A non-increasing sequence $d_1 \ge d_2 \ge \cdots \ge d_n \ge 0$ of naturals is **graphical**
(realisable as the degree sequence of a simple graph on $n$ labelled vertices) **iff** the sum
$\sum_i d_i$ is even **and** for every $k \in \{1, \dots, n\}$

$$
\sum_{i=1}^{k} d_i \ \le\ k(k-1) \ +\ \sum_{i=k+1}^{n} \min(d_i,\, k).
$$

The handshake lemma (`handshake-lemma`) supplies the *necessity* of the parity condition
($\sum_i d_i = 2\lvert E\rvert$ is even). This problem asks for the **converse / full
characterisation**: the Erdős–Gallai inequalities are together necessary and sufficient, situating
the handshake parity as the first (and simplest) of the necessary conditions.

### Plain Language

The handshake lemma tells you the degrees of a graph always sum to an even number. But which lists
of target degrees can actually be *realised* by some graph? Erdős–Gallai gives the exact answer: the
even-sum condition plus a family of $n$ inequalities controlling how concentrated the large degrees
can be. This turns "the degrees sum to an even number" into a complete, checkable criterion.

### Why This Matters

Degree-sequence realisability is foundational in graph theory and network science (constructing
graphs with prescribed degrees). Formalising Erdős–Gallai places the handshake lemma inside its
natural theory and provides Mathlib with a reusable realisability criterion. Even the sufficiency
direction alone (via the Havel–Hakimi reduction) is a satisfying constructive result.

## Known Results

### What's Already Proven

- `handshake-lemma` (gallery) — $\sum_{v} \deg(v) = 2\lvert E\rvert$, hence the degree sum is even
  (the parity necessary condition).
- Mathlib `SimpleGraph.degree`, `SimpleGraph.sum_degrees_eq_twice_card_edges`.

### What's Still Open

- The Erdős–Gallai inequalities themselves (neither direction is in Mathlib as of this writing).
- A Lean formalisation of the Havel–Hakimi recursive realisability test.

### Our Goal

Start with the **sufficiency** direction via Havel–Hakimi (constructive, algorithmic) for a first
milestone, then the Erdős–Gallai inequalities as the necessity side. Milestone 1: formalise the
Havel–Hakimi reduction step and prove it preserves realisability. Target `0` sorries / `0` axioms on
each shipped lemma.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| handshake-lemma | Supplies the parity necessary condition | degree sum, double counting |
| erdos-gallai (if later spawned) | The full inequality family | double counting, extremal bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Havel–Hakimi for sufficiency (recommended first milestone).
   - Why it might work: The reduction "delete the top-degree vertex, subtract 1 from the next
     $d_1$ degrees" is finite and inductive; realisability of the reduced sequence lifts to the
     original. Constructive and well-suited to `SimpleGraph` on `Fin n`.
   - Risk: The lifting step (adding back edges without violating simplicity) requires a careful
     swapping/exchange argument.

2. **Approach B**: Direct Erdős–Gallai necessity via double counting.
   - Why it might work: For each $k$, count edges incident to the top $k$ vertices; the
     $k(k-1)$ term bounds internal edges and $\sum \min(d_i,k)$ bounds crossing edges.
   - Risk: Formalising the $\min$-split and the extremal edge count is index-heavy.

### Key Difficulties

- No existing Mathlib scaffolding for degree-sequence realisability; the recursion and the
  edge-exchange (2-switch) lemmas must be built from `SimpleGraph` primitives.
- Managing non-increasing-order bookkeeping and `Fin n` reindexing after each reduction step.

### What Would a Proof Need?

- Key lemma 1: Havel–Hakimi reduction preserves realisability (both directions of the recursion).
- Key lemma 2: the 2-switch / edge-exchange lemma to normalise a realisation.
- Technical requirements: `SimpleGraph`, `Finset` sums, sorted-sequence manipulation, strong
  induction on $n$.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The parity necessary condition is trivial (handshake), but the full characterisation is a genuine
  theorem with no Mathlib support — the realisability infrastructure must be built.
- Havel–Hakimi gives a concrete, testable first milestone that de-risks the larger goal.
- Similar `SimpleGraph` extremal arguments exist in the gallery, so the primitives are familiar.

**Estimated Effort**:
- Exploration: days
- If tractable (Havel–Hakimi milestone): 1–2 weeks
- If hard (full Erdős–Gallai both directions): several weeks

## References

### Papers
- P. Erdős, T. Gallai, *Gráfok előírt fokszámú pontokkal*, 1960 — the characterisation.
- V. Havel (1955) / S. Hakimi (1962) — the recursive realisability algorithm.

### Online Resources
- https://en.wikipedia.org/wiki/Erdős–Gallai_theorem — statement and proof sketch.
- https://en.wikipedia.org/wiki/Havel–Hakimi_algorithm — the constructive test.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` — `SimpleGraph`, `degree`, edge finsets.
- `Mathlib.Combinatorics.SimpleGraph.DegreeSum` — `sum_degrees_eq_twice_card_edges`.
- `Mathlib.Order.Monotone.Basic` — sorted-sequence lemmas for the non-increasing hypothesis.

## Metadata

```yaml
tags:
  - graph-theory
  - degree-sequence
  - erdos-gallai
related_proofs:
  - handshake-lemma
difficulty: high
source: proof-suggestion
created: 2026-07-05T03:14:24-07:00
```
