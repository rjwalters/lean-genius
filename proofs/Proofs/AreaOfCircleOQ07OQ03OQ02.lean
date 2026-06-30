import Mathlib

/-
# `Γ(1/2)² = π` via the Beta value `B(1/2,1/2) = π` and the arcsine density

## What This Proves

This file evaluates `Γ(1/2)` through the Euler Beta function rather than through the
Gaussian integral. The two ingredients are:

* **Beta–Gamma reflection at the centre.**  `Mathlib`'s
  `Complex.Gamma_mul_Gamma_eq_betaIntegral` gives
  `Γ(1/2)·Γ(1/2) = Γ(1)·B(1/2,1/2)`, and `Γ(1) = 1`, so `Γ(1/2)² = B(1/2,1/2)`.

* **The arcsine integral.**  The Beta value is the total mass of the (unnormalised)
  arcsine density,
  `B(1/2,1/2) = ∫₀¹ x^{-1/2}(1-x)^{-1/2} dx = ∫₀¹ dx/√(x(1-x)) = π`,
  evaluated by the fundamental theorem of calculus with antiderivative
  `arcsin(2x-1)` (whose derivative is exactly the integrand on `(0,1)`).

Combining them gives `Γ(1/2)² = π`, hence `Γ(1/2) = √π`, **without ever invoking the
Gaussian integral** (which is how `Mathlib`'s own `Real.Gamma_one_half_eq` is proved).
The proof is therefore an independent, genuinely Beta-function-based derivation, and it
exhibits the classical fact that the arcsine probability density
`1/(π√(x(1-x)))` integrates to one.

## The Arithmetic of the Antiderivative

On `(0,1)` we have `1-(2x-1)² = 4x(1-x)`, so

  `d/dx arcsin(2x-1) = 2/√(1-(2x-1)²) = 2/√(4x(1-x)) = 1/√(x(1-x))
                     = x^{-1/2}(1-x)^{-1/2}`,

which is precisely the Beta integrand at `(1/2,1/2)`. The endpoint values
`arcsin(±1) = ±π/2` give total integral `π/2-(-π/2) = π`. Singularities at the two
endpoints are harmless: the FTC variant `integral_eq_sub_of_hasDeriv_right_of_le` only
needs the derivative on the open interval together with continuity of the
antiderivative and integrability of the integrand (the latter from
`Complex.betaIntegral_convergent`).

## Status: 0 sorries, 0 axioms
-/

open Real Complex MeasureTheory intervalIntegral Set

namespace AreaOfCircleOQ07OQ03OQ02

/-- The unnormalised arcsine density `x ↦ x^{-1/2}(1-x)^{-1/2}` on `[0,1]`. -/
noncomputable def arcsineDensity (x : ℝ) : ℝ :=
  x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (-(1 / 2) : ℝ)

/-! ## The antiderivative and its derivative -/

/-- On the open interval `(0,1)`, `arcsin(2x-1)` has derivative equal to the arcsine
density `x^{-1/2}(1-x)^{-1/2}`. This is the analytic heart: `1-(2x-1)² = 4x(1-x)`. -/
theorem hasDerivAt_arcsin_affine {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.arcsin (2 * y - 1)) (arcsineDensity x) x := by
  have hne1 : 2 * x - 1 ≠ -1 := by nlinarith
  have hne2 : 2 * x - 1 ≠ 1 := by nlinarith
  -- derivative of the inner affine map `2x-1`
  have hinner : HasDerivAt (fun y : ℝ => 2 * y - 1) 2 x := by
    simpa using ((hasDerivAt_id x).const_mul 2).sub_const 1
  -- chain rule with `arcsin`
  have hchain : HasDerivAt (fun y => Real.arcsin (2 * y - 1))
      (1 / Real.sqrt (1 - (2 * x - 1) ^ 2) * 2) x := by
    have h := (Real.hasDerivAt_arcsin hne1 hne2).comp x hinner
    simpa [Function.comp] using h
  -- identify the derivative with the arcsine density
  have hpos : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hkey : 1 / Real.sqrt (1 - (2 * x - 1) ^ 2) * 2 = arcsineDensity x := by
    have h4 : 1 - (2 * x - 1) ^ 2 = 4 * (x * (1 - x)) := by ring
    have hsqrt4 : Real.sqrt (1 - (2 * x - 1) ^ 2)
        = 2 * (Real.sqrt x * Real.sqrt (1 - x)) := by
      rw [h4, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num), Real.sqrt_mul hx0.le]
    rw [hsqrt4]
    have hsx : Real.sqrt x = x ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow x
    have hs1x : Real.sqrt (1 - x) = (1 - x) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (1 - x)
    have hsxpos : (0:ℝ) < x ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hx0 _
    have hs1xpos : (0:ℝ) < (1 - x) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos (by linarith) _
    rw [arcsineDensity, hsx, hs1x,
      Real.rpow_neg hx0.le, Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - x)]
    field_simp
    ring
  rw [← hkey]; exact hchain

/-! ## Integrability of the integrand -/

/-- The arcsine density is interval-integrable on `[0,1]`: its norm agrees with the
norm of the convergent complex Beta integrand. -/
theorem intervalIntegrable_arcsineDensity :
    IntervalIntegrable arcsineDensity volume 0 1 := by
  have hconv := Complex.betaIntegral_convergent (u := (1/2 : ℂ)) (v := (1/2 : ℂ))
    (by norm_num) (by norm_num)
  have hnorm := hconv.norm
  refine hnorm.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr (ae_of_all _ ?_))
  intro x hx
  rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  obtain ⟨hx0, hx1⟩ := hx
  have hx0' : (0:ℝ) ≤ x := hx0.le
  have hx1' : (0:ℝ) ≤ 1 - x := by linarith
  -- both complex cpow factors are `ofReal` of nonnegative real rpows
  have e1 : (x : ℂ) ^ ((1/2 : ℂ) - 1) = ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx0']; congr 1; push_cast; ring
  have e2 : (1 - (x : ℂ)) ^ ((1/2 : ℂ) - 1) = (((1 - x) ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_cpow hx1']
    congr 1; push_cast; ring
  rw [e1, e2, ← Complex.ofReal_mul, Complex.norm_real, arcsineDensity]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0' _) (Real.rpow_nonneg hx1' _))]

/-! ## The arcsine integral equals `π` -/

/-- **The arcsine integral.** `∫₀¹ x^{-1/2}(1-x)^{-1/2} dx = π`, by the FTC with
antiderivative `arcsin(2x-1)`. -/
theorem integral_arcsineDensity : ∫ x in (0:ℝ)..1, arcsineDensity x = π := by
  have hcont : ContinuousOn (fun y => Real.arcsin (2 * y - 1)) (Icc 0 1) :=
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
  have hderiv : ∀ x ∈ Ioo (0:ℝ) 1,
      HasDerivWithinAt (fun y => Real.arcsin (2 * y - 1)) (arcsineDensity x) (Ioi x) x := by
    intro x hx
    exact (hasDerivAt_arcsin_affine hx.1 hx.2).hasDerivWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (by norm_num : (0:ℝ) ≤ 1) hcont hderiv intervalIntegrable_arcsineDensity
  rw [hFTC, show (2 : ℝ) * 1 - 1 = 1 by norm_num, show (2 : ℝ) * 0 - 1 = -1 by norm_num,
    Real.arcsin_one, Real.arcsin_neg_one]
  ring

/-! ## The Beta value and `Γ(1/2)² = π` -/

/-- **The central Beta value.** `B(1/2,1/2) = π`. -/
theorem betaIntegral_half_half : Complex.betaIntegral (1/2) (1/2) = (π : ℂ) := by
  rw [Complex.betaIntegral]
  have heq : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0:ℝ) 1 →
      (x : ℂ) ^ ((1/2 : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1/2 : ℂ) - 1)
        = ((arcsineDensity x : ℝ) : ℂ) := by
    refine ae_of_all _ (fun x hx => ?_)
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx0' : (0:ℝ) ≤ x := hx0.le
    have hx1' : (0:ℝ) ≤ 1 - x := by linarith
    have e1 : (x : ℂ) ^ ((1/2 : ℂ) - 1) = ((x ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0']; congr 1; push_cast; ring
    have e2 : (1 - (x : ℂ)) ^ ((1/2 : ℂ) - 1) = (((1 - x) ^ (-(1/2) : ℝ) : ℝ) : ℂ) := by
      rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_cpow hx1']
      congr 1; push_cast; ring
    rw [e1, e2, ← Complex.ofReal_mul, arcsineDensity]
  rw [intervalIntegral.integral_congr_ae heq, intervalIntegral.integral_ofReal,
    integral_arcsineDensity]

/-- **`Γ(1/2)² = π` (complex).** Proved through the Beta value, not the Gaussian
integral. -/
theorem complex_Gamma_half_sq : Complex.Gamma (1/2) ^ 2 = (π : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (1/2 : ℂ)) (t := (1/2 : ℂ))
    (by norm_num) (by norm_num)
  rw [show (1/2 : ℂ) + 1/2 = 1 by norm_num, Complex.Gamma_one, one_mul,
    betaIntegral_half_half] at h
  rw [sq]; exact h

/-- **`Γ(1/2)² = π` (real).** -/
theorem real_Gamma_half_sq : Real.Gamma (1/2) ^ 2 = π := by
  have h := complex_Gamma_half_sq
  rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.Gamma_ofReal] at h
  have : ((Real.Gamma (1/2) ^ 2 : ℝ) : ℂ) = ((π : ℝ) : ℂ) := by push_cast at h ⊢; linear_combination h
  exact_mod_cast this

/-- **`Γ(1/2) = √π`**, recovered through the Beta route. (`Mathlib`'s
`Real.Gamma_one_half_eq` proves the same equality via the Gaussian integral; here it is
a corollary of `B(1/2,1/2) = π`.) -/
theorem real_Gamma_half : Real.Gamma (1/2) = Real.sqrt π := by
  have hsq : Real.Gamma (1/2) ^ 2 = π := real_Gamma_half_sq
  have hpos : 0 < Real.Gamma (1/2) := Real.Gamma_pos_of_pos (by norm_num)
  rw [← hsq, Real.sqrt_sq hpos.le]

/-- **Arcsine probability density normalisation.** The arcsine density
`1/(π√(x(1-x)))` integrates to `1` over `[0,1]`. -/
theorem arcsine_density_normalised :
    ∫ x in (0:ℝ)..1, (π)⁻¹ * arcsineDensity x = 1 := by
  rw [intervalIntegral.integral_const_mul, integral_arcsineDensity]
  field_simp [Real.pi_ne_zero]

end AreaOfCircleOQ07OQ03OQ02
