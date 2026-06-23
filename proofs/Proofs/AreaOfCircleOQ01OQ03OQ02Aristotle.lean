/-
  Aristotle targets for Lipschitz Isoperimetric Inequality (area-of-circle-oq-01-oq-03-oq-02)
  Routine supporting lemmas for automated proof search.
  See AreaOfCircleOQ01OQ03OQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms

  These lemmas are the standard analytic facts underlying the technical (non-axiomatic)
  sorries in the parent file: the a.e. boundedness, measurability, and interval
  integrability of derivatives of Lipschitz functions. Together they discharge the
  `hdx_int`/`hdy_int` integrability obligations in `wirtinger_sum_sq_bound_lip` and the
  `hf_int` integrability obligation in `lipschitz_isoperimetric`.
-/
import Mathlib

open MeasureTheory

open scoped NNReal

noncomputable section

namespace LipschitzIsoperimetricAristotle

/-
PROBLEM
The pointwise derivative of a Lipschitz function is bounded by its Lipschitz constant:
for `LipschitzWith K f`, `‖deriv f t‖ ≤ K` at every point.

PROVIDED SOLUTION
At points where `f` is differentiable, `hasDerivAt_deriv_iff.mpr` gives `HasDerivAt f (deriv f t) t`,
and a Lipschitz-with-`K` function has every derivative bounded by `K` (the difference quotients
are bounded by `K`, so the limit is too). At points where `f` is not differentiable, `deriv f t = 0`
by Lean's convention, and `0 ≤ (K : ℝ)`. Mathlib relevant lemmas: `LipschitzWith.norm_deriv_le`,
or derive from `HasDerivAt` and the difference-quotient bound.
-/
lemma lipschitz_norm_deriv_le (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) (t : ℝ) :
    ‖deriv f t‖ ≤ (K : ℝ) := by sorry

/-
PROBLEM
The squared derivative of a Lipschitz function is pointwise bounded by `K²`:
for `LipschitzWith K f`, `deriv f t ^ 2 ≤ (K : ℝ) ^ 2`.

PROVIDED SOLUTION
From `lipschitz_norm_deriv_le`, `|deriv f t| ≤ K`. Squaring a real with `sq_le_sq'` (or
`abs_le_abs` then `pow_le_pow_left`) and using `Real.norm_eq_abs` gives `deriv f t ^ 2 ≤ K ^ 2`.
Both sides are nonneg so the inequality is preserved.
-/
lemma lipschitz_deriv_sq_le (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f) (t : ℝ) :
    deriv f t ^ 2 ≤ (K : ℝ) ^ 2 := by sorry

/-
PROBLEM
The squared derivative of a Lipschitz function is interval integrable on any `[a, b]`:
for `LipschitzWith K f`, `IntervalIntegrable (fun t => deriv f t ^ 2) volume a b`.

PROVIDED SOLUTION
`deriv f` is measurable (`measurable_deriv`), so `fun t => deriv f t ^ 2` is measurable, hence
a.e. strongly measurable. By `lipschitz_deriv_sq_le` it is bounded above by the constant `K ^ 2`
(and below by `0`), so it is a.e. bounded on the finite-measure interval `[a, b]`. A bounded,
a.e. strongly measurable function on a set of finite measure is interval integrable
(`IntervalIntegrable` via `MeasureTheory.Integrable` of a bounded measurable function on a finite
measure restriction; e.g. `IntervalIntegrable.mono` against the constant `K ^ 2`, or
`intervalIntegrable_of_bound`).
-/
lemma lipschitz_deriv_sq_intervalIntegrable (f : ℝ → ℝ) (K : ℝ≥0) (hf : LipschitzWith K f)
    (a b : ℝ) :
    IntervalIntegrable (fun t => deriv f t ^ 2) volume a b := by sorry

/-
PROBLEM
The product of a continuous function and the derivative of a Lipschitz function is interval
integrable on any `[a, b]`: for continuous `f` and `LipschitzWith Kg g`,
`IntervalIntegrable (fun t => f t * deriv g t) volume a b`.

PROVIDED SOLUTION
`f` is continuous, hence a.e. strongly measurable and bounded on the compact `[a, b]`. `deriv g`
is measurable (`measurable_deriv`) and a.e. bounded by `Kg` (`lipschitz_norm_deriv_le`). The product
is therefore a.e. strongly measurable and a.e. bounded on the finite-measure interval, so it is
interval integrable. Combine `Continuous.boundedOn`/`IsCompact.bddAbove` for `f` with the
derivative bound for `g`, then apply `intervalIntegrable_of_bound` (or bound `|f t * deriv g t|`
by a constant and use `IntervalIntegrable.mono_fun`).
-/
lemma continuous_mul_lipschitz_deriv_intervalIntegrable
    (f g : ℝ → ℝ) (Kg : ℝ≥0) (hf : Continuous f) (hg : LipschitzWith Kg g) (a b : ℝ) :
    IntervalIntegrable (fun t => f t * deriv g t) volume a b := by sorry

end LipschitzIsoperimetricAristotle

end
