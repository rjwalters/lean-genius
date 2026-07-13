# Problem: Baire-Category Generalization of Uncountability

**Slug**: algebraic-numbers-countable-oq-02-oq-02-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
(X,d)\ \text{complete metric space},\ X \neq \emptyset,\ X\ \text{has no isolated points}\ \Longrightarrow\ X\ \text{is uncountable.}
$$

### Plain Language

The gallery's `algebraic-numbers-countable` entry shows $\mathbb{R}$ is uncountable
via a nested-intervals diagonal argument (given any enumeration $f:\mathbb{N}\to\mathbb{R}$,
build nested closed intervals each avoiding $f(n)$, and use completeness to find a
missed point). This task generalizes that argument to its natural home: the Baire
Category Theorem. Every nonempty complete metric space with no isolated points is
uncountable. The proof replaces nested intervals by nested closed balls of shrinking
radius, each avoiding $f(n)$; completeness delivers a limit point outside the range
of $f$.

### Why This Matters

The Baire-category statement subsumes both the algebraic-numbers/$\mathbb{R}$
uncountability entry and many other uncountability results (Cantor set, irrationals,
perfect sets) under one theorem, turning a bespoke real-line argument into a general
topological principle already central to functional analysis.

## Known Results

### What's Already Proven

- `algebraic-numbers-countable` (gallery) — nested-intervals uncountability of $\mathbb{R}$.
- Mathlib has `BaireSpace`, `dense_iUnion_interior_of_closed`, and complete-metric-space
  instances of `BaireSpace` (`baireSpace_of_completeSpace`).

### What's Still Open

- A packaged Lean statement "nonempty complete metric space with no isolated points is
  uncountable" and its reduction from the existing $\mathbb{R}$ argument. Mathlib may
  already contain `Perfect`/`perfect_setOf`-flavored results
  (e.g. `Perfect.uncountable`) — locating the precise statement is step one.

### Our Goal

Prove (or assemble from Mathlib) the uncountability of a nonempty complete metric
space without isolated points, and note how the $\mathbb{R}$ gallery entry instantiates it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-numbers-countable | Parent; the $\mathbb{R}$ special case | Nested intervals, diagonal argument |
| cantors-theorem | Cardinality/uncountability context | Diagonalization |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Mathlib `Perfect`/`BaireSpace` reuse**: Mathlib's
   `Perfect.uncountable` (a nonempty perfect set in a complete space is uncountable)
   is essentially this statement. Locate it and wrap.
   - Why it might work: the general result is standard descriptive set theory, present in Mathlib.
   - Risk: hypotheses phrased via `Perfect` / `PreconnectedSpace` mismatch; adapting "no isolated points" to `Perfect`.

2. **Approach B — direct nested-balls proof**: mirror the interval argument with
   `Metric.closedBall`, `IsComplete`, choosing radii $\to 0$ and centers avoiding $f(n)$.
   - Why it might work: a faithful lift of the existing gallery proof.
   - Risk: dependent choice / center-selection bookkeeping.

### Key Difficulties

- Choosing a shrinking ball inside the previous one that still excludes the next
  enumerated point — needs "no isolated point" to guarantee room.
- Matching Mathlib's `Perfect`/`BaireSpace` API to the informal statement.

### What Would a Proof Need?

- Key lemma 1: from "no isolated points", every open ball contains two distinct points,
  giving a strictly smaller sub-ball avoiding any fixed point.
- Key lemma 2: nested closed balls with radii $\to 0$ in a complete space have a common point.
- Technical requirements: `Mathlib.Topology.MetricSpace.Baire`, `Perfect` API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is standard and the Mathlib Baire/`Perfect` infrastructure exists.
- Uncertainty is in matching the exact Mathlib phrasing versus reproving directly.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 2–4 days
- If hard: unknown (if a direct nested-balls proof is required from scratch)

## References

### Papers
- Kechris, *Classical Descriptive Set Theory* — perfect sets in Polish spaces are uncountable.
- Oxtoby, *Measure and Category* — Baire category on complete metric spaces.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Perfect.html — `Perfect`, `Perfect.uncountable`.

### Mathlib
- `Mathlib.Topology.MetricSpace.Baire` — `BaireSpace`, complete-space instance.
- `Mathlib.Topology.Perfect` — perfect sets and their uncountability.

## Metadata

```yaml
tags:
  - set-theory
  - real-analysis
  - baire-category
  - uncountability
related_proofs:
  - algebraic-numbers-countable
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 6/10
