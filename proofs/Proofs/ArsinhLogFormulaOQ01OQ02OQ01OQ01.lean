/-
# The improper integral `∫_1^b 1/√(t² − 1) dt = arcosh b`

Research: arsinh-log-formula-oq-01-oq-02-oq-01-oq-01
Parent:   arsinh-log-formula-oq-01-oq-02-oq-01 (the `arcosh` antiderivative / FTC capstone)

The parent entry proved the *proper* Fundamental Theorem of Calculus evaluation

    ∫_a^b 1/√(t² − 1) dt = arcosh b − arcosh a      (1 < a, 1 < b),

valid on any closed interval `[a, b] ⊂ (1, ∞)` where the integrand is continuous.
It left open the natural endpoint question: the integrand has a singularity at
`t = 1` (the radicand `t² − 1` vanishes), yet the area underneath remains finite.
Can the FTC evaluation be pushed *down to the singularity* to obtain the improper
integral `∫_1^b 1/√(t² − 1) dt = arcosh b`?

This file answers that question two complementary ways.

* **Genuine (Lebesgue) improper integral.**  The singularity at `t = 1` is
  *integrable*: near `t = 1` we have `1/√(t² − 1) ≤ 1/√(t − 1)`, an inverse
  square-root singularity, which is integrable.  We prove
  `intervalIntegrable_one` — interval-integrability of `t ↦ 1/√(t² − 1)` on the
  *closed* interval `[1, b]` across the singular endpoint — by domination against
  the integrable model `t ↦ (t − 1)^(−1/2)`.  The FTC variant
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, which only requires
  continuity at the endpoints plus differentiability on the open interior, then
  yields `improper_integral_eq_arcosh`:

      ∫_1^b 1/√(t² − 1) dt = arcosh b      (1 < b),

  using `arcosh 1 = 0`.

* **Improper integral as a limit.**  We also record the classical
  limit form `integral_tendsto_arcosh`:

      ∫_a^b 1/√(t² − 1) dt → arcosh b   as   a → 1⁺,

  obtained directly from the parent closed form `arcosh b − arcosh a` and the
  right-continuity of `arcosh` at `1`.  This is the precise sense in which the
  lower limit is "taken to the singularity".

Supporting infrastructure (`hasDerivAt_arcosh`, the proper FTC, …) is reproved
here so the file is self-contained.  The new content over the parent is:
right-continuity of `arcosh` at `1`, the integrability of the singular integrand
across the endpoint, and the two improper-integral statements.  All results are
`0`-axiom and machine-checked.
-/
import Mathlib

namespace ArsinhLogFormulaOQ01OQ02OQ01OQ01

open Real intervalIntegral MeasureTheory Filter Set

/-! ### Reproved parent infrastructure -/

/-- For `t > 1` the radicand `t² − 1` is strictly positive, hence `√(t² − 1) > 0`. -/
theorem sqrt_sq_sub_one_pos {x : ℝ} (hx : 1 < x) : 0 < Real.sqrt (x ^ 2 - 1) :=
  Real.sqrt_pos.mpr (by nlinarith)

/-- **Antiderivative fact.** `arcosh` is an antiderivative of `1/√(t² − 1)` on
`(1, ∞)`: `HasDerivAt Real.arcosh (1/√(t² − 1)) t` for `t > 1`.  Built from the
logarithmic form `arcosh t = log(t + √(t² − 1))` by the chain rule. -/
theorem hasDerivAt_arcosh {x : ℝ} (hx : 1 < x) :
    HasDerivAt Real.arcosh (1 / Real.sqrt (x ^ 2 - 1)) x := by
  have hpos : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.mpr hpos
  have hg : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by linarith [hs]
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 - 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).sub_const 1
  have h2 : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 1))
      (2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := h1.sqrt hpos.ne'
  have h3 : HasDerivAt (fun y : ℝ => y + Real.sqrt (y ^ 2 - 1))
      (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) x := (hasDerivAt_id x).add h2
  have h4 : HasDerivAt (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 - 1)))
      ((1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) / (x + Real.sqrt (x ^ 2 - 1))) x :=
    h3.log hg.ne'
  have hval : (1 + 2 * x / (2 * Real.sqrt (x ^ 2 - 1))) / (x + Real.sqrt (x ^ 2 - 1))
      = 1 / Real.sqrt (x ^ 2 - 1) := by
    field_simp
    ring
  rw [hval] at h4
  exact h4

/-- On any interval `[a, b] ⊂ (1, ∞)` the integrand `t ↦ 1/√(t² − 1)` is
continuous (the denominator stays strictly positive). -/
theorem continuousOn_integrand {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ContinuousOn (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1)) (Set.uIcc a b) := by
  apply ContinuousOn.div continuousOn_const
  · exact (Real.continuous_sqrt.comp (by continuity)).continuousOn
  · intro t ht
    have h1t : 1 < t := by
      rcases Set.mem_uIcc.mp ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact (sqrt_sq_sub_one_pos h1t).ne'

/-- Consequently the integrand is interval-integrable on `[a, b] ⊂ (1, ∞)`. -/
theorem intervalIntegrable_integrand {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1)) volume a b :=
  (continuousOn_integrand ha hb).intervalIntegrable

/-- **Proper FTC (parent result).** `∫_a^b 1/√(t² − 1) dt = arcosh b − arcosh a`
for `1 < a, b`. -/
theorem integral_one_div_sqrt_sq_sub_one {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, 1 / Real.sqrt (t ^ 2 - 1) = Real.arcosh b - Real.arcosh a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h1x : 1 < x := by
      rcases Set.mem_uIcc.mp hx with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
    exact hasDerivAt_arcosh h1x
  · exact intervalIntegrable_integrand ha hb

/-! ### New content: continuity of `arcosh` at the singular endpoint -/

/-- `arcosh` is continuous on the closed ray `[1, ∞)`, including the endpoint `1`
where the derivative blows up.  Since `arcosh x = log(x + √(x² − 1))` and the
argument `x + √(x² − 1) ≥ 1 > 0` on `[1, ∞)`, the logarithm composes
continuously. -/
theorem continuousOn_arcosh : ContinuousOn Real.arcosh (Set.Ici 1) := by
  have hcont : ContinuousOn (fun x : ℝ => Real.log (x + Real.sqrt (x ^ 2 - 1)))
      (Set.Ici 1) := by
    apply ContinuousOn.log
    · exact (continuous_id.add (Real.continuous_sqrt.comp (by continuity))).continuousOn
    · intro x hx
      have hx1 : (1 : ℝ) ≤ x := hx
      have hs : 0 ≤ Real.sqrt (x ^ 2 - 1) := Real.sqrt_nonneg _
      have : (0 : ℝ) < x + Real.sqrt (x ^ 2 - 1) := by linarith
      exact this.ne'
  exact hcont

/-! ### New content: integrability across the singularity -/

/-- The model singular function `t ↦ (t − 1)^(−1/2)` is interval-integrable on
`[1, b]`: it is the shift by `1` of `x ↦ x^(−1/2)`, integrable across `0` because
the exponent `−1/2 > −1`. -/
theorem intervalIntegrable_model (b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 / (2 : ℝ)))) volume 1 b := by
  have h : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / (2 : ℝ)))) volume 0 (b - 1) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hshift := h.comp_sub_right 1
  simpa using hshift

/-- **Integrability across the singular endpoint.**  The integrand `t ↦ 1/√(t² − 1)`
is interval-integrable on the *closed* interval `[1, b]` (for `1 < b`), even though
it is unbounded near `t = 1`.  Proof: dominate by the integrable model
`t ↦ (t − 1)^(−1/2)`, using `1/√(t² − 1) ≤ 1/√(t − 1) = (t − 1)^(−1/2)` on `(1, b]`. -/
theorem intervalIntegrable_one {b : ℝ} (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1)) volume 1 b := by
  -- the dominating model function is integrable
  have hmodel := intervalIntegrable_model b
  -- the integrand is a.e.-strongly-measurable on the restricted measure
  have hmeas : AEStronglyMeasurable (fun t : ℝ => 1 / Real.sqrt (t ^ 2 - 1))
      (volume.restrict (Set.uIoc 1 b)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
    apply ContinuousOn.div continuousOn_const
    · exact (Real.continuous_sqrt.comp (by continuity)).continuousOn
    · intro t ht
      have h1t : 1 < t := (Set.mem_uIoc.mp ht).elim (fun h => h.1) (fun h => by
        rw [uIoc_of_le hb.le] at ht; exact (Set.mem_Ioc.mp ht).1)
      exact (sqrt_sq_sub_one_pos h1t).ne'
  -- the pointwise domination, holding on all of `Ι 1 b = Ioc 1 b`
  refine hmodel.mono_fun' hmeas ?_
  rw [uIoc_of_le hb.le]
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall ?_)
  intro t ht
  have h1t : 1 < t := (Set.mem_Ioc.mp ht).1
  have hu : (0 : ℝ) < t - 1 := by linarith
  -- rewrite the model value as `1/√(t − 1)`
  have hmodel_eq : (t - 1) ^ (-(1 / (2 : ℝ))) = 1 / Real.sqrt (t - 1) := by
    rw [Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow, one_div]
  show ‖1 / Real.sqrt (t ^ 2 - 1)‖ ≤ (t - 1) ^ (-(1 / (2 : ℝ)))
  rw [hmodel_eq]
  -- `‖1/√(t²−1)‖ = 1/√(t²−1)` (it is nonnegative)
  have hpos2 : 0 < Real.sqrt (t ^ 2 - 1) := sqrt_sq_sub_one_pos h1t
  have hnn : (0 : ℝ) ≤ 1 / Real.sqrt (t ^ 2 - 1) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  -- `√(t−1) ≤ √(t²−1)`, hence `1/√(t²−1) ≤ 1/√(t−1)`
  have hposu : 0 < Real.sqrt (t - 1) := Real.sqrt_pos.mpr hu
  have hle : Real.sqrt (t - 1) ≤ Real.sqrt (t ^ 2 - 1) :=
    Real.sqrt_le_sqrt (by nlinarith)
  exact one_div_le_one_div_of_le hposu hle

/-! ### Main results: the improper integral -/

/-- **The improper integral.**  `∫_1^b 1/√(t² − 1) dt = arcosh b` for `1 < b`.

The integrand is integrable across the singularity at the lower endpoint `t = 1`
(`intervalIntegrable_one`); `arcosh` is continuous on `[1, b]`
(`continuousOn_arcosh`) and differentiable on `(1, b)` with derivative the
integrand (`hasDerivAt_arcosh`).  The endpoint-aware FTC
`integral_eq_sub_of_hasDeriv_right_of_le` then evaluates the integral to
`arcosh b − arcosh 1 = arcosh b`, using `arcosh 1 = 0`. -/
theorem improper_integral_eq_arcosh {b : ℝ} (hb : 1 < b) :
    ∫ t in (1 : ℝ)..b, 1 / Real.sqrt (t ^ 2 - 1) = Real.arcosh b := by
  have key : ∫ t in (1 : ℝ)..b, 1 / Real.sqrt (t ^ 2 - 1)
      = Real.arcosh b - Real.arcosh 1 := by
    apply integral_eq_sub_of_hasDeriv_right_of_le hb.le
    · exact continuousOn_arcosh.mono (by
        intro x hx; exact (Set.mem_Icc.mp hx).1)
    · intro x hx
      have h1x : 1 < x := (Set.mem_Ioo.mp hx).1
      exact (hasDerivAt_arcosh h1x).hasDerivWithinAt
    · exact intervalIntegrable_one hb
  rw [key, Real.arcosh_zero, sub_zero]

/-- **The improper integral as a limit.**  `∫_a^b 1/√(t² − 1) dt → arcosh b` as
`a → 1⁺`.  This is the classical "improper integral" reading: the lower limit is
driven to the singularity.  It follows from the proper FTC closed form
`arcosh b − arcosh a` and the right-continuity of `arcosh` at `1`. -/
theorem integral_tendsto_arcosh {b : ℝ} (hb : 1 < b) :
    Tendsto (fun a => ∫ t in a..b, 1 / Real.sqrt (t ^ 2 - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.arcosh b)) := by
  -- eventually (for `a > 1`) the integral equals `arcosh b − arcosh a`
  have hev : (fun a => ∫ t in a..b, 1 / Real.sqrt (t ^ 2 - 1))
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)] (fun a => Real.arcosh b - Real.arcosh a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact integral_one_div_sqrt_sq_sub_one (Set.mem_Ioi.mp ha) hb
  rw [tendsto_congr' hev]
  -- `arcosh a → arcosh 1 = 0` as `a → 1⁺`
  have harc : Tendsto Real.arcosh (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.arcosh 1)) :=
    (continuousOn_arcosh.continuousWithinAt Set.left_mem_Ici).mono_left
      (nhdsWithin_mono 1 Set.Ioi_subset_Ici_self)
  have hlim := harc.const_sub (Real.arcosh b)
  rw [Real.arcosh_zero] at hlim
  simpa using hlim

/-! ### Concrete corollary -/

/-- **Concrete improper evaluation.**  `∫_1^{5/3} 1/√(t² − 1) dt = log 3`, since
`arcosh (5/3) = log 3` (the radicand at `5/3` is `(4/3)²`). -/
theorem improper_integral_one_to_five_thirds :
    ∫ t in (1 : ℝ)..(5 / 3), 1 / Real.sqrt (t ^ 2 - 1) = Real.log 3 := by
  rw [improper_integral_eq_arcosh (by norm_num)]
  have h : Real.sqrt ((5 / 3 : ℝ) ^ 2 - 1) = 4 / 3 := by
    rw [show ((5 / 3 : ℝ) ^ 2 - 1) = (4 / 3) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  show Real.log ((5 / 3 : ℝ) + Real.sqrt ((5 / 3) ^ 2 - 1)) = Real.log 3
  rw [h, show (5 / 3 + 4 / 3 : ℝ) = 3 by norm_num]

end ArsinhLogFormulaOQ01OQ02OQ01OQ01
