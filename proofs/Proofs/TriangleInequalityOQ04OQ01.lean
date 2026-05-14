/-
# Triangle Inequality for Geodesic Distances on Riemannian Manifolds (OQ-04-OQ-01)

S2a scaffolding: a **chart-local** Euclidean arc length, defined for paths
landing in a normed space `E`. The intended application: given a smooth manifold
`M`, a chart `(U, φ)` with `φ : U → E`, and a path `γ : ℝ → U`, the chart-local
arc length of `γ` is the integral of `‖(φ ∘ γ)'(t)‖` over the parameter interval.

For S2a we just expose `chartArcLength` on `ℝ → E` curves directly, prove the
trivial sanity lemmas (zero-length interval, constant path), and integral
nonnegativity. Subsequent iterations will add:

- S2b — additivity under path concatenation (`chartArcLength_trans`), via
  `intervalIntegral.integral_add_adjacent_intervals`.
- S2c — chart-local triangle inequality (`chartIntrinsicDist_triangle`),
  mirroring the parent `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle`.

## Honest scope

This is a **chart-local** triangle inequality. The result depends on the chart
`φ` and is **not** the Riemannian distance. Mathlib v4.26.0 has no
`RiemannianMetric` typeclass; the chart-local definition is a foundation that
will lift to a chart-invariant Riemannian arc length via partition-of-unity
gluing once upstream lands the typeclass.

See `research/problems/triangle-inequality-oq-04-oq-01/` for the S1 OBSERVE
Mathlib survey and the four-path roadmap.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory

namespace TriangleInequalityOQ04OQ01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **chart-local Euclidean arc length** of a curve `γ : ℝ → E` on the
interval `[a, b]` is the integral of `‖γ'(t)‖` over `t ∈ [a, b]`.

When `γ` is the composition `φ ∘ γ̃` of a chart map `φ : U → E` with a path
`γ̃ : ℝ → U` on a smooth manifold `M`, this measures the Euclidean length of
the path's image in the chart. The result depends on the chart and is
chart-local, not Riemannian. -/
noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

/-- The arc length over a degenerate interval `[a, a]` is zero. -/
@[simp]
theorem chartArcLength_self (γ : ℝ → E) (a : ℝ) : chartArcLength γ a a = 0 := by
  simp [chartArcLength, intervalIntegral.integral_same]

/-- A constant curve has zero arc length on any interval. -/
@[simp]
theorem chartArcLength_const (c : E) (a b : ℝ) :
    chartArcLength (fun _ : ℝ => c) a b = 0 := by
  simp [chartArcLength, deriv_const']

/-- The arc length is nonnegative for `a ≤ b`, because the norm is. -/
theorem chartArcLength_nonneg (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ chartArcLength γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)

end TriangleInequalityOQ04OQ01
