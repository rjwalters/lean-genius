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
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Real.Archimedean

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

/-- **Additivity under interval concatenation** (S2b): for any three parameter
points `a, b, c : ℝ` such that the speed `‖γ'(·)‖` is interval-integrable on
both `[a, b]` and `[b, c]`, the chart-local arc lengths over those two
intervals sum to the arc length over `[a, c]`.

The hypotheses are stated as `IntervalIntegrable` rather than the more
restrictive `a ≤ b ≤ c`, because `intervalIntegral.integral_add_adjacent_intervals`
handles the orientation-aware case (`∫_{a..b} + ∫_{b..c} = ∫_{a..c}` for any
ordering of `a, b, c`) via Mathlib's signed-interval-integral convention. This
matches the form needed for the S2c chart-local triangle inequality
(`chartIntrinsicDist_triangle`), where `b` is the intermediate endpoint of a
broken path. -/
theorem chartArcLength_trans (γ : ℝ → E) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume b c) :
    chartArcLength γ a b + chartArcLength γ b c = chartArcLength γ a c := by
  simp only [chartArcLength]
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The **chart-local intrinsic distance** between two points `p, q : E`: the
infimum of chart-local arc lengths over all continuous paths `γ : Path p q`
whose speed `‖deriv γ.extend (·)‖` is interval-integrable on `[0, 1]`.

The `IntervalIntegrable` side-hypothesis is essential: without restricting to
paths whose derivative is integrable, the value would collapse for pathological
reparametrisations whose speed is non-integrable (Mathlib's integral convention
returns `0` for non-strongly-measurable integrands). With it, every contributing
length is the genuine chart-local Euclidean arc length — non-negative by
`chartArcLength_nonneg` — and the infimum satisfies the triangle inequality
proved in the subsequent `chartIntrinsicDist_triangle`.

Mirrors `Proofs.TriangleInequalityOQ04.intrinsicDist`, but valued in `ℝ` (not
`ℝ≥0∞`) because `chartArcLength` is a Bochner `intervalIntegral`. The result
depends on the chart embedding and is **not** the Riemannian distance — see the
file header for the honest-scope disclaimer. -/
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1),
    chartArcLength γ.extend 0 1

/-- The chart-local intrinsic distance is non-negative: every contributing
`chartArcLength γ.extend 0 1` is non-negative (by `chartArcLength_nonneg` at
`0 ≤ 1`), and `Real.iInf_nonneg` lifts this through both layers of the
conditional infimum. The lemma holds unconditionally — in particular, even
when no `Path p q` satisfies the `IntervalIntegrable` side-hypothesis (in which
case the relevant `iInf` collapses to `0` via Mathlib's real-valued `sInf` of
the empty set). -/
theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  unfold chartIntrinsicDist
  refine Real.iInf_nonneg (fun γ => ?_)
  refine Real.iInf_nonneg (fun _ => ?_)
  exact chartArcLength_nonneg γ.extend zero_le_one

end TriangleInequalityOQ04OQ01
