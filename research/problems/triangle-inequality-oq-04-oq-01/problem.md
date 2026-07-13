# Problem: Triangle Inequality for Geodesic Distances on Riemannian Manifolds

**Slug**: triangle-inequality-oq-04-oq-01
**Created**: 2026-05-12T14:45:44-07:00
**Status**: Active (S1 OBSERVE complete)
**Source**: seeker-selected (parent: `triangle-inequality-oq-04`, openQuestions[0])
**Parent**: `triangle-inequality-oq-04` ("Triangle Inequality for Geodesic/Path Metrics") — COMPLETED for general metric spaces, OQ-01 asks to extend to Riemannian manifolds.

## Problem Statement

### Formal Statement

Let $(M, g)$ be a Riemannian manifold with Riemannian metric $g$, i.e. a smoothly-varying inner product $g_p : T_pM \times T_pM \to \mathbb{R}$ on the tangent space at each point $p \in M$. Define the **Riemannian arc length** of a piecewise-smooth path $\gamma : [a, b] \to M$ by

$$
L_g(\gamma) := \int_a^b \sqrt{g_{\gamma(t)}(\gamma'(t), \gamma'(t))} \, dt
$$

and the **geodesic distance** between $p, q \in M$ by

$$
d_g(p, q) := \inf \{ L_g(\gamma) \mid \gamma : [0, 1] \to M \text{ piecewise smooth, } \gamma(0) = p, \gamma(1) = q \}.
$$

The triangle inequality

$$
d_g(p, r) \leq d_g(p, q) + d_g(q, r)
$$

holds for all $p, q, r \in M$, because piecewise-smooth paths can be concatenated and Riemannian arc length is additive under concatenation.

### Plain Language

On a smooth manifold equipped with a Riemannian metric (a smoothly-varying way to measure
tangent-vector lengths), the geodesic distance between two points is the infimum of arc
lengths of smooth paths connecting them. This distance function satisfies the triangle
inequality, because paths can be glued together end-to-end and their lengths add.

The result for general metric spaces with intrinsic (path) distance is in
`Proofs.TriangleInequalityOQ04`. The Riemannian case is **strictly more refined**: it requires
the Riemannian metric (the inner-product structure on each tangent space), and the arc length
is defined as an integral of a square root of an inner product, not just the total variation
of a continuous curve.

### Why This Matters

- **Foundational for Riemannian geometry**: every theorem about geodesic completeness, the
  Hopf–Rinow theorem, comparison geometry, and metric-measure-space techniques
  (Cheeger–Colding, Lott–Sturm–Villani) starts from the fact that $(M, d_g)$ is a metric
  space — which requires the triangle inequality for $d_g$.
- **Distinct from the metric-space case**: the OQ-04 parent already covers the general
  metric-space intrinsic distance (`intrinsicDist_triangle`). The Riemannian extension is
  what makes the result usable for differential geometers (most of whom prefer the
  $g_{ij} \, dx^i dx^j$ formalism over the abstract path-variation formalism).
- **Mathlib gap of strategic value**: Mathlib v4.26.0 has **no** `RiemannianMetric`
  typeclass and no `Geodesic.lean`. Closing this gap (or laying the groundwork) is on the
  Mathlib community's stated wishlist (see `docs/100.yaml`'s entry for "Brouwer FPT" /
  general manifold theorems status).

## Known Results

### What's Already Proven

- **`Proofs.TriangleInequalityOQ04` (parent slug, COMPLETED)** — Triangle inequality for the
  intrinsic (path) metric `intrinsicDist` on any metric space, using `eVariationOn` (total
  variation) as the arc length proxy. 245 lines, 0 sorries, 0 axioms. The intrinsic metric
  agrees with the Riemannian distance **only** when the manifold's metric structure is
  ultimately derivable from a Riemannian metric, which is itself the open question here.
- **`Proofs.TriangleInequality` (great-grandparent)** — Standard metric-space triangle
  inequality from `Mathlib.Topology.MetricSpace.Basic`.
- **Mathlib v4.26.0 `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners`** — Charts,
  smooth manifolds with corners. The framework is in place for a future Riemannian metric.
- **Mathlib v4.26.0 `Mathlib.Geometry.Manifold.VectorBundle.Tangent`** —
  `def TangentSpace I x := E` (tangent space at `x` is definitionally the model vector
  space `E`). This is **the** hook for hanging a Riemannian metric: a `RiemannianMetric`
  typeclass would assign to each `x` a smoothly-varying inner product on `TangentSpace I x`.
- **Mathlib v4.26.0 `Mathlib.Geometry.Manifold.WhitneyEmbedding`** — Whitney embedding
  theorem (compact T2 manifolds embed smoothly into $\mathbb{R}^n$). The embedding is
  **smooth**, **not** isometric.
- **Mathlib v4.26.0 `Mathlib.Geometry.Manifold.Metrizable`** —
  `ManifoldWithCorners.metrizableSpace` makes every smooth manifold a metrizable space,
  but the metric is **not canonical** (any metrization works) and is **not** the
  Riemannian distance.

### What's Still Open

1. **Mathlib does not yet have a `RiemannianMetric` typeclass.** The natural definition is
   a smoothly-varying section of `Sym²(T*M)` that is positive-definite at each point.
   `Mathlib.Geometry.Manifold.VectorBundle.Tangent` provides `TangentSpace I`, but no
   inner product structure on it.
2. **No `arcLength_g`-style definition** of Riemannian arc length as an integral of a
   square root of an inner product.
3. **No `Geodesic.lean`** module with `geodesic_dist` or `intrinsic_dist_riemannian`.

### Our Goal

**S1 OBSERVE deliverable** (this iteration): map the Mathlib v4.26.0 status and identify
3–4 concrete intermediate targets that **do not** require waiting for upstream Mathlib to
land the Riemannian metric typeclass. See `sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md`
for the full survey; the executive summary:

- **Path A — chart-local Euclidean length**: define arc length of a piecewise-smooth path
  $\gamma : [0, 1] \to M$ as $\int_0^1 \|\mathrm{D}\gamma(t)\| \, dt$ using `MFDeriv` in
  charts, with the Euclidean norm on `TangentSpace I x = E`. The triangle inequality
  follows by concatenation, but the resulting distance is **chart-dependent** unless we
  pin a global Riemannian metric (which we don't yet have).
- **Path B — isometric embedding via Whitney**: embed $M$ into $\mathbb{R}^n$ via the
  Whitney theorem, pull back the Euclidean metric to a Riemannian metric on $M$. Gives a
  *concrete* (but embedding-dependent) Riemannian metric. The pulled-back path metric
  satisfies the triangle inequality by reduction to OQ-04 in $\mathbb{R}^n$.
- **Path C — abstract path metric on a smooth manifold via metrization**: use
  `ManifoldWithCorners.metrizableSpace` to view $M$ as a `PseudoMetricSpace`, then apply
  the existing `intrinsicDist_triangle` from OQ-04 directly. The resulting metric is the
  intrinsic metric of *some* metrization of $M$; it is **not** the Riemannian distance,
  but it does satisfy the triangle inequality.
- **Path D — wait for upstream Mathlib `RiemannianMetric`**: defer to a future Mathlib
  release (no current PR is visible at v4.26.0). Realistic timeline: not 2026.

The **recommended S2 target** is Path A: define a private `chartArcLength` and prove its
triangle inequality, with an explicit caveat that the result is **chart-local** (not
chart-invariant) and serves as a foundation for an eventual Riemannian extension.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `triangle-inequality-oq-04` | **Parent**: triangle inequality for intrinsic path metric on any metric space. Verbatim base for Path C; conceptual base for Paths A, B. | `eVariationOn`, `Path.trans`, `eVariationOn.Icc_add_Icc`, `eVariationOn.comp_eq_of_monotoneOn` |
| `triangle-inequality-oq-03` | Sibling: triangle inequality variant. Likely similar metric-space-level argument. | TBD |
| `triangle-inequality` | Grandparent: Mathlib's standard triangle inequality. | `dist_triangle` from `Mathlib.Topology.MetricSpace.Basic` |
| `isosceles-triangle-oq-01` | Family member; geometry not directly related. | Euclidean geometry |

## Initial Thoughts

### Potential Approaches

See "Our Goal" above for the four paths (A–D). The S1 OBSERVE survey
(`sessions/2026-05-12-s1-observe-riemannian-mathlib-survey.md`) provides full Mathlib API
references and LOC budgets.

### Likely Tools / Lemmas

- `Mathlib.Geometry.Manifold.SmoothManifoldWithCorners` (basic framework)
- `Mathlib.Geometry.Manifold.MFDeriv` (manifold derivatives, for $\gamma'(t)$)
- `Mathlib.Geometry.Manifold.IntegralCurve` (paths on manifolds)
- `Mathlib.Geometry.Manifold.VectorBundle.Tangent` (tangent space)
- `Mathlib.Geometry.Manifold.WhitneyEmbedding` (for Path B)
- `Mathlib.Geometry.Manifold.Metrizable` (for Path C)
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` (for the $\int_a^b$ in $L_g$)
- The existing `Proofs.TriangleInequalityOQ04` infrastructure (verbatim for Path C, by
  reduction for Paths A and B).

### Expected Difficulty

- **S1 OBSERVE** (this iteration): doc-only survey — easy, ~1 hour, 1 PR.
- **S2 ACT Path A** (chart-local length): ~150 LOC Lean, the existing `MFDeriv` API gives
  $\gamma'(t)$ in `TangentSpace I (γ t) = E`, integration via `intervalIntegral`. Medium.
- **S2 ACT Path B** (isometric embedding): ~80 LOC Lean by reduction to OQ-04 in ℝⁿ. Easy,
  but mathematically *cheating* (the metric is not intrinsic to $M$).
- **S2 ACT Path C** (metrization): ~30 LOC Lean by direct citation of OQ-04 +
  `Metrizable`. Trivial, but the result is essentially vacuous (any metrization gives a
  metric, no Riemannian content).
- **Full Riemannian formalization**: ~1500+ LOC, gated on `RiemannianMetric` upstream
  Mathlib infrastructure (D). Not in current scope.
