/-
  The Gaussian is its own Fourier Transform
  (area-of-circle-oq-05-oq-03)

  Open question from the `area-of-circle-oq-05` lineage (the Gaussian integral
  ∫ e^{-x²} = √π) and a flagged gap in `CentralLimitTheorem.lean`, which
  *axiomatizes* the Fourier self-duality of the Gaussian.  Here we prove that
  identity from Mathlib, axiom-free, in explicit Lebesgue-integral form:

      ∫_ℝ e^{i t x} · e^{-x²/2} dx = e^{-t²/2} · √(2π)        (un-normalized)

  and its probability-normalized companion

      ∫_ℝ e^{i t x} · (e^{-x²/2} / √(2π)) dx = e^{-t²/2}.      (normalized)

  The right-hand side of the normalized identity is exactly `e^{-t²/2}`, the
  characteristic function of the standard normal distribution: the standard
  Gaussian density is, up to the unitary normalization, its own Fourier transform.

  METHOD (the classical "complete the square"):
      i t x - x²/2 = -½(x - i t)² - t²/2,
  so the integrand factors as e^{-½(x - it)²} · e^{-t²/2}; the constant e^{-t²/2}
  pulls out of the integral, and the remaining contour integral
  ∫ e^{-½(x - it)²} dx = √(2π) is Mathlib's
  `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I` (a Cauchy / vertical-
  strip shift of the real Gaussian integral) specialised at b = 1/2, c = -t.

  Everything is proved with 0 sorries and 0 axioms.

  HONEST SCOPE: `CentralLimitTheorem.lean` states its Gaussian Fourier identity
  against an *abstract* `stdGaussian` measure that is itself introduced by `axiom`;
  discharging that particular axiom requires first replacing the abstract measure
  by the concrete `ProbabilityTheory.gaussianReal 0 1` and is a separate
  integration step.  What is delivered here is the full mathematical content — the
  concrete Lebesgue-integral Fourier identity — with no axioms.

  References:
  - The Gaussian integral and its Fourier self-duality, e.g. Stein–Shakarchi,
    Fourier Analysis (2003), Ch. 5.
  - Mathlib: Analysis.SpecialFunctions.Gaussian.FourierTransform
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real Complex MeasureTheory
open scoped Real

namespace GaussianFourierTransform

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  COMPLETING THE SQUARE (POINTWISE)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Completing the square, at the level of the integrand.**  For every real `x`,

      e^{i t x} · e^{-x²/2} = e^{-(1/2)(x + (-t)·i)²} · e^{-t²/2}.

    This is the identity `i t x - x²/2 = -½(x - i t)² - t²/2` exponentiated; the
    second factor on the right is the constant that will pull out of the integral. -/
theorem gaussian_integrand_complete_square (t x : ℝ) :
    Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(((1 : ℝ) / 2 : ℝ) : ℂ) * ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ^ 2)
        * Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (t : ℂ) ^ 2 / 2 * Complex.I_sq

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  THE CONSTANT √(2π) FROM THE CONTOUR INTEGRAL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Mathlib contour-integral constant `(π / (1/2))^(1/2)` is the complex
    coercion of the real `√(2π)`. -/
theorem cpow_half_eq_sqrt_two_pi :
    ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [show ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
  norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE GAUSSIAN FOURIER IDENTITY (LEBESGUE FORM)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Gaussian is its own Fourier transform (un-normalized).**

      ∫_ℝ e^{i t x} · e^{-x²/2} dx = e^{-t²/2} · √(2π). -/
theorem gaussian_fourier_real (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simp_rw [gaussian_integrand_complete_square t]
  rw [MeasureTheory.integral_mul_const]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
        (b := (((1 : ℝ) / 2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num) (-t)]
  rw [cpow_half_eq_sqrt_two_pi]
  ring

/-- **The standard Gaussian density is its own Fourier transform (normalized).**

      ∫_ℝ e^{i t x} · (e^{-x²/2} / √(2π)) dx = e^{-t²/2}.

    The right-hand side is the characteristic function of the standard normal
    distribution `N(0,1)`. -/
theorem gaussian_fourier_normalized (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * (Complex.exp (-(x : ℂ) ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ))
      = Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  have hC : ((Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
    exact ne_of_gt this
  simp_rw [← mul_div_assoc]
  rw [MeasureTheory.integral_div, gaussian_fourier_real]
  rw [mul_div_assoc, div_self hC, mul_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Total mass / `t = 0` specialisation:** the standard Gaussian density
    integrates to `1`. -/
theorem gaussian_density_total_mass :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ) = 1 := by
  simpa using gaussian_fourier_normalized 0

/-- **The un-normalized Gaussian integral over ℝ:** `∫ e^{-x²/2} dx = √(2π)`
    (the `t = 0` shadow of the Fourier identity). -/
theorem integral_gaussian_half :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2 / 2) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simpa using gaussian_fourier_real 0

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The Gaussian is its own Fourier transform  (oq-05-oq-03)

### What's proved (0 sorries, 0 axioms):
- `gaussian_integrand_complete_square`: the pointwise factoring
  e^{itx}·e^{-x²/2} = e^{-½(x-it)²}·e^{-t²/2} (completing the square, via I² = -1).
- `cpow_half_eq_sqrt_two_pi`: the Mathlib contour constant (π/(1/2))^(1/2) = √(2π).
- `gaussian_fourier_real`: **∫ e^{itx} e^{-x²/2} dx = e^{-t²/2}·√(2π)** — the
  Gaussian Fourier self-duality in Lebesgue form.
- `gaussian_fourier_normalized`: **∫ e^{itx}·(e^{-x²/2}/√(2π)) dx = e^{-t²/2}** —
  the characteristic function of the standard normal.
- `gaussian_density_total_mass`: the standard density integrates to 1.
- `integral_gaussian_half`: ∫ e^{-x²/2} dx = √(2π).

### Honest scope:
The Fourier identity is proved here as a concrete Lebesgue integral.  The
`CentralLimitTheorem.lean` axiom of the same name is phrased against an abstract
`stdGaussian` measure introduced by `axiom`; discharging *that* axiom additionally
requires replacing the abstract measure by `ProbabilityTheory.gaussianReal 0 1`,
a separate bridge not attempted here.
-/

#check @gaussian_fourier_real
#check @gaussian_fourier_normalized
#check @gaussian_density_total_mass
#check @integral_gaussian_half

end GaussianFourierTransform
