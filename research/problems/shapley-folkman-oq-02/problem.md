# Problem: Quantitative Shapley–Folkman–Starr Bound in Mathlib

**Slug**: shapley-folkman-oq-02
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `shapley-folkman`)

## Problem Statement

### Formal Statement

The Shapley–Folkman lemma (parent) says: a point in the convex hull of a Minkowski sum
$\sum_{i=1}^m S_i$ in $\mathbb{R}^n$ lies in $\sum_i S_i$ after convexifying at most $n$ of the
summands. The **Starr quantitative refinement** bounds how far the (non-convex) Minkowski sum is
from its convex hull, uniformly in $m$:

$$
d_H\!\left(\sum_{i=1}^m S_i,\ \operatorname{conv}\sum_{i=1}^m S_i\right) \le \sqrt{n}\cdot \max_i \operatorname{rad}(S_i),
$$

where $d_H$ is Hausdorff distance and $\operatorname{rad}(S_i)$ the circumradius of $S_i$. The bound
is independent of the number of summands $m$ — the engine behind "convexity emerges in large
aggregates" (used in mathematical economics). This problem asks to formalize Starr's bound using
Mathlib's metric-space and convexity infrastructure.

### Plain Language

Adding many sets together (Minkowski sum) makes the result look convex even if each piece is not.
The parent lemma is the qualitative version. Starr's theorem makes it *quantitative*: the gap
between the sum and its convex hull is bounded by $\sqrt n$ times the size of the *largest single*
set — crucially, the bound does **not** grow with the number of sets. The goal is to prove this
metric bound in Lean.

### Why This Matters

The $m$-independence is exactly why non-convexities "wash out" in large economies (Aumann, Starr)
and in non-convex optimization duality gaps. Mathlib has Carathéodory, convex hulls, Minkowski
sums, and Hausdorff/`EMetric` distance — but not the Shapley–Folkman–Starr quantitative bound.
Formalizing it gives the gallery a sharp, applications-rich convexity theorem on top of the
existing qualitative entry.

## Known Results

### What's Already Proven

- `shapley-folkman` — the qualitative Shapley–Folkman lemma (parent), built on Carathéodory.
- Mathlib: `convexHull`, `Convex`, Carathéodory (`convexHull_eq_union`), Minkowski sums (`Set.add`), `Metric.hausdorffDist`/`EMetric.hausdorffEdist`, circumradius via `Metric.diam`/`Bornology`.

### What's Still Open (in this gallery)

- The Starr metric bound $d_H(\sum S_i, \operatorname{conv}\sum S_i) \le \sqrt n \max_i \operatorname{rad}(S_i)$.
- A clean `rad`/circumradius definition compatible with the inner-product structure.

### Our Goal

Formalize Starr's bound: from the Shapley–Folkman decomposition (at most $n$ summands need
convexifying), bound the displacement of each convexified summand by its radius and aggregate via
the $\ell^2$/$\sqrt n$ estimate, expressed with `Metric.hausdorffDist`. Milestone: the per-point
bound first, then the Hausdorff-distance statement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shapley-folkman | Direct parent; qualitative lemma + Carathéodory setup | convex hulls, Minkowski sums |
| caratheodory (gallery) | Underlying $\le n+1$ representation | convex combinations |
| krein-milman / convexity entries | Convex-geometry toolkit | extreme points, hulls |

## Initial Thoughts

### Potential Approaches

1. **Shapley–Folkman decomposition + radius bound (recommended)**: a hull point of $\sum S_i$ is a
   sum where all but $\le n$ summands are non-convexified; bound the deviation of each of those $\le n$
   convexified summands by its circumradius and combine with the $\sqrt n$ $\ell^2$ aggregation.
   - Why it might work: directly upgrades the parent lemma; each step maps to existing Mathlib convexity/metric lemmas.
   - Risk: the $\sqrt n$ aggregation requires an inner-product (not just metric) structure and a careful Pythagorean estimate.

2. **Inner-bound via Cauchy–Schwarz on the $\le n$ deviations**: treat the $\le n$ deviation vectors and bound their sum's norm.
   - Why it might work: makes the $\sqrt n$ explicit.
   - Risk: bookkeeping of which summands are convexified across all hull points (uniformity for Hausdorff).

### Key Difficulties

- Getting a uniform-in-$m$ bound: the same $\le n$ bound must hold for *every* hull point to control the Hausdorff distance.
- Defining circumradius `rad(S)` compatibly and proving the per-summand displacement bound.

### What Would a Proof Need?

- Key lemma 1: Shapley–Folkman selection (at most $n$ summands convexified) — from the parent.
- Key lemma 2: $\ell^2$ aggregation of $\le n$ radius-bounded deviations $\Rightarrow \sqrt n \max_i \operatorname{rad}(S_i)$.
- Technical requirements: `EuclideanSpace`, `convexHull`, `Metric.hausdorffDist`, `Metric.diam`, Cauchy–Schwarz.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The qualitative lemma is in the gallery; this is a quantitative upgrade with all metric/convex tools present in Mathlib.
- The main novelty is the uniform Hausdorff bound and the $\sqrt n$ aggregation, both concrete.
- No external theory needed beyond inner-product geometry.

**Estimated Effort**:
- Exploration: days
- If tractable: 2–4 weeks
- If hard: 1–2 months (if uniformity across hull points is delicate)

## References

### Papers
- Starr (1969), "Quasi-equilibria in markets with non-convex preferences", Econometrica.
- Arrow & Hahn, *General Competitive Analysis* (1971) — Shapley–Folkman–Starr appendix.

### Online Resources
- Parent gallery entry `shapley-folkman`.

### Mathlib
- `Mathlib.Analysis.Convex.Combination` / `Caratheodory` — hull representations.
- `Mathlib.Topology.MetricSpace.HausdorffDistance` — Hausdorff distance.

## Metadata

```yaml
tags:
  - convex-geometry
  - shapley-folkman
  - hausdorff-distance
  - mathematical-economics
related_proofs:
  - shapley-folkman
  - caratheodory
difficulty: medium
source: proof-suggestion
created: 2026-06-14
```
