import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# Half-Line Gaussian Moments

## Open Question (area-of-circle-oq-07-oq-02-oq-02)
"Evaluate the first absolute moment `∫_{(0,∞)} x · e^{-b x²} dx = 1/(2b)` and the
second moment `∫_{(0,∞)} x² · e^{-b x²} dx = √(π/b)/(4b)`, connecting the half-line
Gaussian to the variance of the half-normal distribution."

The parent entry `area-of-circle-oq-07-oq-02` evaluates the **zeroth** moment
`∫_{(0,∞)} e^{-b x²} dx = √(π/b)/2`.  Here we climb the moment ladder one and two
rungs higher.

## Results

* `first_half_moment`  : `∫_{(0,∞)} x  · e^{-b x²} dx = 1/(2b)`     (`b > 0`)
* `second_half_moment` : `∫_{(0,∞)} x² · e^{-b x²} dx = √(π/b)/(4b)` (`b > 0`)

The **first** moment is elementary: `x · e^{-b x²}` has the explicit primitive
`-(2b)⁻¹ · e^{-b x²}`, so the half-line integral is just the boundary value
`(2b)⁻¹`.  Unlike the *full*-line first moment (which vanishes by odd symmetry),
the half-line first moment is genuinely non-trivial.

The **second** moment is one integration by parts away.  The function
`g(x) = -(2b)⁻¹ · x · e^{-b x²}` has derivative
`g'(x) = x² e^{-b x²} - (2b)⁻¹ e^{-b x²}`, and `g` vanishes at both `0` and `∞`.
Hence `∫_{(0,∞)} (x² - (2b)⁻¹) e^{-b x²} dx = 0`, i.e. the second moment is
`(2b)⁻¹` times the zeroth moment `√(π/b)/2`, giving `√(π/b)/(4b)`.

These are exactly the (unnormalised) first and second moments of the half-normal
distribution: dividing by the total mass `√(π/b)/2` recovers its mean
`1/√(πb)` and second moment `1/(2b)`.

No new axioms: every step is a routine consequence of existing Mathlib results.
-/

open Real MeasureTheory Filter Topology
open scoped Topology

/-- Auxiliary: `x ↦ -b · x²` tends to `-∞` along `atTop` when `b > 0`. -/
private theorem neg_b_sq_tendsto_atBot {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => -b * x ^ 2) atTop atBot :=
  (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb)

/-- Auxiliary: `e^{-b x²} → 0` along `atTop` when `b > 0`. -/
private theorem exp_neg_b_sq_tendsto_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => Real.exp (-b * x ^ 2)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp (neg_b_sq_tendsto_atBot hb)

/-- Auxiliary: `x · e^{-b x²} → 0` along `atTop` when `b > 0`.

Obtained from the linear-exponent decay `xˢ · e^{-b x}` (with `s = 1/2`) precomposed
with `x ↦ x²`, since `(x²)^{1/2} = x` for `x ≥ 0`. -/
private theorem mul_exp_neg_b_sq_tendsto_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => x * Real.exp (-b * x ^ 2)) atTop (𝓝 0) := by
  have hcomp :
      Tendsto (fun x : ℝ => (x ^ 2) ^ (1 / 2 : ℝ) * Real.exp (-b * x ^ 2)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) b hb).comp
      (tendsto_pow_atTop two_ne_zero)
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  norm_num

/-- **First half-line Gaussian moment.** For `b > 0`,
`∫_{(0,∞)} x · e^{-b x²} dx = 1/(2b)`.

The integrand has the explicit primitive `-(2b)⁻¹ · e^{-b x²}`, so the value is the
boundary term `(2b)⁻¹` (the primitive vanishes at `+∞` and equals `-(2b)⁻¹` at `0`). -/
theorem first_half_moment (b : ℝ) (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = 1 / (2 * b) := by
  have hb2 : (2 * b) ≠ 0 := by positivity
  -- primitive and its derivative
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun x => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2))
        (x * Real.exp (-b * x ^ 2)) x := by
    intro x _
    convert (((hasDerivAt_pow 2 x).const_mul (-b)).exp).const_mul (-(2 * b)⁻¹) using 1
    field_simp
    ring
  -- boundary behaviour: primitive → 0
  have htendsto :
      Tendsto (fun x : ℝ => -(2 * b)⁻¹ * Real.exp (-b * x ^ 2)) atTop (𝓝 (-(2 * b)⁻¹ * 0)) :=
    (exp_neg_b_sq_tendsto_zero hb).const_mul _
  rw [mul_zero] at htendsto
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
        (integrable_mul_exp_neg_mul_sq hb).integrableOn htendsto]
  norm_num

/-- **Second half-line Gaussian moment.** For `b > 0`,
`∫_{(0,∞)} x² · e^{-b x²} dx = √(π/b)/(4b)`.

Integration by parts against the primitive `g(x) = -(2b)⁻¹ · x · e^{-b x²}` (which
vanishes at `0` and `+∞`) reduces the second moment to `(2b)⁻¹` times the zeroth
moment `√(π/b)/2`, evaluated by the parent's `integral_gaussian_Ioi`. -/
theorem second_half_moment (b : ℝ) (hb : 0 < b) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) = Real.sqrt (π / b) / (4 * b) := by
  have hb2 : (2 * b) ≠ 0 := by positivity
  -- primitive g and its derivative g' = x² e^{-bx²} - (2b)⁻¹ e^{-bx²}
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun x => -(2 * b)⁻¹ * x * Real.exp (-b * x ^ 2))
        (x ^ 2 * Real.exp (-b * x ^ 2) - (2 * b)⁻¹ * Real.exp (-b * x ^ 2)) x := by
    intro x _
    have h := (((hasDerivAt_id x).const_mul (-(2 * b)⁻¹))).mul
      (((hasDerivAt_pow 2 x).const_mul (-b)).exp)
    convert h using 1
    simp only [id_eq]
    field_simp
    ring
  -- g → 0 at +∞
  have htendsto :
      Tendsto (fun x : ℝ => -(2 * b)⁻¹ * x * Real.exp (-b * x ^ 2)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -(2 * b)⁻¹ * (x * Real.exp (-b * x ^ 2))) atTop
        (𝓝 (-(2 * b)⁻¹ * 0)) := (mul_exp_neg_b_sq_tendsto_zero hb).const_mul _
    rw [mul_zero] at this
    refine this.congr (fun x => ?_)
    ring
  -- integrability of the two pieces on Ioi
  have hI_zero : IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hI_two : IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) (Set.Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 2 by norm_num)).congr_fun
      ?_ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [← Real.rpow_natCast x 2, Nat.cast_ofNat]
  -- g' integrates to g(+∞) - g(0) = 0
  have hint : ∫ x in Set.Ioi (0 : ℝ),
      (x ^ 2 * Real.exp (-b * x ^ 2) - (2 * b)⁻¹ * Real.exp (-b * x ^ 2)) = 0 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv ?_ htendsto]
    · simp
    · exact hI_two.sub (hI_zero.const_mul _)
  -- split the integral and solve
  rw [integral_sub hI_two (hI_zero.const_mul _), integral_const_mul,
    integral_gaussian_Ioi] at hint
  -- hint : (∫ x², ...) - (2b)⁻¹ * (√(π/b)/2) = 0
  rw [sub_eq_zero] at hint
  rw [hint]
  field_simp
  ring

/-- **Both half-line moments, packaged.** For `b > 0` the first moment is `1/(2b)`
and the second is `√(π/b)/(4b)`. -/
theorem half_line_moments (b : ℝ) (hb : 0 < b) :
    (∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = 1 / (2 * b)) ∧
      (∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x ^ 2) = Real.sqrt (π / b) / (4 * b)) :=
  ⟨first_half_moment b hb, second_half_moment b hb⟩

/-- **First moment at `b = 1`.** `∫_{(0,∞)} x · e^{-x²} dx = 1/2`. -/
theorem first_half_moment_one :
    ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-x ^ 2) = 1 / 2 := by
  have h := first_half_moment 1 one_pos
  simpa only [neg_one_mul, mul_one] using h

/-- **Mean of the half-normal distribution.** Dividing the first moment by the total
mass `√(π/b)/2` of `e^{-b x²}` over `(0,∞)` gives the half-normal mean `1/√(π b)`.
Stated as the clean cross-multiplied identity that avoids division. -/
theorem half_normal_mean_relation (b : ℝ) (hb : 0 < b) :
    (∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2)) * Real.sqrt (π / b)
      = (1 / (2 * b)) * Real.sqrt (π / b) := by
  rw [first_half_moment b hb]
