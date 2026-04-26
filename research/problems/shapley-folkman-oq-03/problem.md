# Problem: Shapley-Folkman Theorem: Economic Application Formalization

**Slug**: shapley-folkman-oq-03
**Created**: 2026-04-22T21:48:45+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For an exchange economy with } N \text{ agents and non-convex preferences,}
\text{ there exists an } \varepsilon\text{-equilibrium where } \varepsilon \to 0 \text{ as } N \to \infty.
$$

More precisely: if each agent $i$ has a feasible set $A_i \subset \mathbb{R}^d$, then any point
in $\operatorname{conv}(\sum_{i=1}^N A_i)$ is within Hausdorff distance $\varepsilon$ of
$\sum_{i=1}^N A_i$ itself, where $\varepsilon$ is controlled by $d$ (the ambient dimension)
rather than $N$ (the number of agents).

### Plain Language

The Shapley-Folkman lemma says that the Minkowski sum of many non-convex sets is "nearly convex":
the non-convexity of the sum is bounded by the ambient dimension, not by how many sets you sum.

The economic application: in an exchange economy with many agents, even if each agent has
non-convex preferences (indivisible goods, increasing returns), the *aggregate* economy behaves
as if preferences were convex. This allows proving existence of approximate competitive equilibria.

The goal is to formalize this economic application in Lean 4 — either:
1. The Shapley-Folkman-Starr theorem (quantitative bound on the Hausdorff distance), or
2. A clean theorem about approximate equilibrium existence in exchange economies.

### Why This Matters

The Shapley-Folkman lemma is the mathematical engine behind core convergence theorems in
mathematical economics. A formalization bridges convex analysis (already partially in Lean)
with economic theory, and provides a natural target for Mathlib extension in the economics
direction. The gallery proof already formalizes the core lemma — this extends it to its
primary application.

## Known Results

### What's Already Proven

- **Shapley-Folkman Lemma** (gallery: `shapley-folkman`) — core lemma: any point in
  `conv(∑ Sᵢ)` decomposes with at most `d` summands from `conv(Sᵢ)` rather than `Sᵢ`.
  *Status*: formalized with 1 sorry remaining (Carathéodory descent Case B).
- **Carathéodory's theorem** (Mathlib: `convexHull_eq_union`) — any point in `convexHull S`
  is a convex combination of at most `d+1` points.
- **Minkowski sum** (`Mathlib.Analysis.Convex.Combination`) — `convexHull (A + B) = convexHull A + convexHull B`.

### What's Still Open

- Shapley-Folkman-Starr bound: quantitative Hausdorff distance version (`‖x - y‖ ≤ d · sup_i diam(conv(Aᵢ) \ Aᵢ)`)
- Economic application theorem: existence of ε-equilibria in exchange economies with
  non-convex preferences

### Our Goal

Formalize one of:
1. The **Shapley-Folkman-Starr theorem** (quantitative bound) using Mathlib's metric space / Hausdorff distance infrastructure, OR
2. A **simplified economic equilibrium** theorem: in a large economy, the aggregate excess demand function is ε-convex.

Priority: start with the Starr bound since it is a cleaner mathematical statement and builds
directly on the existing gallery proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shapley-folkman` | Parent proof — provides core lemma | Carathéodory reduction, affine independence |
| `minkowski-fundamental-theorem` | Minkowski sum techniques | Lattice API, convex geometry |
| `caratheodory-theorem` | Underpins the Carathéodory descent | Affine dependence, dimension bounds |

## Initial Thoughts

### Potential Approaches

1. **Shapley-Folkman-Starr bound**
   - State: for $x \in \operatorname{conv}(\sum_i A_i)$, there exists $y \in \sum_i A_i$ with
     $\|x - y\| \leq \sqrt{d} \cdot \max_i \operatorname{diam}(\operatorname{conv}(A_i))$
   - Why it might work: follows directly from the core SF decomposition theorem
   - Mathlib has `EMetric.hausdorffDist` and `Metric.diam`
   - Risk: Hausdorff distance API may be thin; may need lemmas about diameter of convex hull

2. **Economic equilibrium (abstract)**
   - State: given $N$ agents with feasible sets $A_i$, and aggregate endowment $\omega$,
     an ε-equilibrium exists where ε → 0 as N → ∞
   - Risk: requires setting up exchange economy formalism (preferences, walrasian equilibrium)
     which may be scope-creep

### Key Difficulties

- Setting up Hausdorff distance / diameter in the right generality
- The `shapley-folkman` gallery proof still has 1 sorry — may need to resolve that first
  (or use `sorry` in the companion proof and note the dependency)
- Mathlib's convex geometry API may not have all needed diameter lemmas

### What Would a Proof Need?

- `ShapleyFolkman.decompose`: main decomposition theorem (in gallery, 1 sorry)
- `Metric.diam_convexHull_le`: bound on diameter of convex hull
- Statement of Starr bound: `‖x - y‖ ≤ C * max_i diam (convexHull (A i))`
- Or: reduce to a purely combinatorial statement about the number of non-convex summands

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The core mathematical machinery exists (gallery proof of SF lemma, Mathlib convex analysis)
- The Starr bound is a straightforward corollary once the decomposition is in hand
- Main challenge is Mathlib API navigation (Hausdorff distance, diameter)
- No genuinely new mathematics needed — this is formalizing a known corollary
- The 1 remaining sorry in the gallery proof is a risk but can be stubbed

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib Hausdorff/diameter API)
- If tractable: 1-2 weeks (state + prove Starr bound)
- If hard: fall back to stating the theorem with sorry and documenting blockers

## References

### Papers
- Shapley, L.S. & Shubik, M. (1966), "Quasi-cores in a monetary economy with nonconvex preferences" — original economic application
- Starr, R.M. (1969), "Quasi-equilibria in markets with non-convex preferences" — Hausdorff distance bound
- Anderson, R.M. (1988), "The second welfare theorem with nonconvex preferences" — modern treatment

### Mathlib
- `Mathlib.Analysis.Convex.Caratheodory` — Carathéodory theorem and related lemmas
- `Mathlib.Analysis.Convex.Combination` — convex combinations, Minkowski sums
- `Mathlib.Topology.MetricSpace.HausdorffDistance` — `EMetric.hausdorffDist`, `Metric.diam`
- `Mathlib.Analysis.InnerProductSpace.Basic` — norm bounds in inner product spaces

## Metadata

```yaml
tags:
  - convex-analysis
  - mathematical-economics
  - minkowski-sum
  - approximation
related_proofs:
  - shapley-folkman
  - minkowski-fundamental-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-22T21:48:45+02:00
```

**Significance**: 7/10
**Tractability**: 6/10
