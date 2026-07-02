/-
# Area of Circle OQ-05 (incomplete-01) → OQ-01 — Moments of the standard normal

The parent `AreaOfCircleOQ05Incomplete01.lean` derives the normalization
constants of the normal distribution from the Gaussian integral
`∫ exp(-x²) dx = √π`, obtaining in particular the standard-normal density
`(1/√(2π))·exp(-x²/2)` that integrates to `1`.  Its open question OQ-01 asks
to formalize the **moments** of the standard normal:

    E[X^{2k}] = (2k-1)!!   (double factorial),   E[X^{2k+1}] = 0.

This file settles the first (and structurally most important) moments and
records the moment-generating function, working with Mathlib's standard-normal
measure `gaussianReal 0 1` and bridging back to the parent's *concrete*
density integral.

Main results (0 axioms, 0 sorries):

* `stdNormal_mean`            — E[X]   = 0
* `stdNormal_variance`        — Var[X] = 1
* `stdNormal_second_moment`   — E[X²]  = 1
* `stdNormal_second_moment_concrete`
      — `∫ x², (1/√(2π))·exp(-x²/2) = 1`   (parent's density idiom)
* `stdNormal_mgf`             — the MGF is `t ↦ exp(t²/2)`, whose Taylor
      coefficients `[t^{2k}] = 1/(2^k k!)` encode `E[X^{2k}] = (2k-1)!!`.

Every result is checked by the kernel with no axioms and no `native_decide`.
The general even-moment formula `E[X^{2k}] = (2k-1)!!` for all `k` (by
differentiating the MGF, or by an integration-by-parts recursion) is left as
the remaining strand of OQ-01.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

open MeasureTheory Real
open scoped ProbabilityTheory

namespace AreaOfCircleOQ05Incomplete01OQ01

/-- The standard normal distribution `N(0,1)` as Mathlib's Gaussian measure
    with mean `0` and variance `1`. -/
noncomputable def stdNormal : Measure ℝ := ProbabilityTheory.gaussianReal 0 1

instance : IsProbabilityMeasure stdNormal := by
  unfold stdNormal; infer_instance

/-- **Mean (first moment).**  `E[X] = 0` for the standard normal. -/
theorem stdNormal_mean : ∫ x, x ∂stdNormal = 0 := by
  unfold stdNormal
  rw [ProbabilityTheory.integral_id_gaussianReal]

/-- **Variance.**  `Var[X] = 1` for the standard normal. -/
theorem stdNormal_variance : Var[id ; stdNormal] = 1 := by
  unfold stdNormal
  rw [ProbabilityTheory.variance_id_gaussianReal]
  simp

/-- **Second moment.**  `E[X²] = 1` for the standard normal.  Since the mean
    is `0`, the variance `∫ (x - E[X])²` collapses to the raw second moment
    `∫ x²`. -/
theorem stdNormal_second_moment : ∫ x, x ^ 2 ∂stdNormal = 1 := by
  have hvar : Var[id ; stdNormal] = 1 := stdNormal_variance
  rw [ProbabilityTheory.variance_eq_integral measurable_id.aemeasurable] at hvar
  simp only [id_eq] at hvar
  rw [stdNormal_mean] at hvar
  simpa using hvar

/-- The Mathlib standard-normal density `gaussianPDFReal 0 1` is exactly the
    parent file's density `(1/√(2π))·exp(-x²/2)`. -/
theorem gaussianPDFReal_std (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 1 x = (1 / Real.sqrt (2 * π)) * Real.exp (-x ^ 2 / 2) := by
  rw [ProbabilityTheory.gaussianPDFReal]
  push_cast
  rw [one_div]
  ring_nf

/-- **Second moment, concrete form.**  In the parent's density idiom,
    `∫ x²·(1/√(2π))·exp(-x²/2) dx = 1`. -/
theorem stdNormal_second_moment_concrete :
    ∫ x : ℝ, x ^ 2 * ((1 / Real.sqrt (2 * π)) * Real.exp (-x ^ 2 / 2)) = 1 := by
  have h1 : (∫ x, ProbabilityTheory.gaussianPDFReal 0 1 x • (x ^ 2 : ℝ)) = 1 := by
    rw [← ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
    exact stdNormal_second_moment
  have hcongr :
      (∫ x : ℝ, x ^ 2 * ((1 / Real.sqrt (2 * π)) * Real.exp (-x ^ 2 / 2)))
        = ∫ x, ProbabilityTheory.gaussianPDFReal 0 1 x • (x ^ 2 : ℝ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [gaussianPDFReal_std, smul_eq_mul]
    ring
  rw [hcongr, h1]

/-- **Moment-generating function.**  `M_X(t) = exp(t²/2)`.  Its Taylor
    coefficients `[t^{2k}] M_X = 1/(2^k k!)` give the even moments
    `E[X^{2k}] = (2k)!/(2^k k!) = (2k-1)!!` and the vanishing of the odd
    moments. -/
theorem stdNormal_mgf : ProbabilityTheory.mgf id stdNormal = fun t => Real.exp (t ^ 2 / 2) := by
  unfold stdNormal
  rw [ProbabilityTheory.mgf_id_gaussianReal]
  funext t
  push_cast
  ring_nf

end AreaOfCircleOQ05Incomplete01OQ01
