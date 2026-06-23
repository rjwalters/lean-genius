/-
Area of Circle OQ-05: The Gaussian Integral ∫ e^{-x²} dx = √π

The Gaussian integral is intimately connected to the area of a circle:
the standard proof squares the integral and evaluates via polar coordinates,
converting the double integral into a circular area computation.

(∫ e^{-x²} dx)² = ∫∫ e^{-(x²+y²)} dx dy
                 = ∫₀²π ∫₀∞ e^{-r²} r dr dθ
                 = 2π · (1/2) = π

Hence ∫ e^{-x²} dx = √π.

This file uses Mathlib's `integral_gaussian` which provides the result directly.
We connect it to the area-of-circle context and derive standard corollaries.

## Status
- [x] Gaussian integral stated and proved via Mathlib
- [x] Connection to circle area via polar coordinates (documented)
- [x] Standard normal normalization (proved via scaled_gaussian)
- [x] Radial integral component (proved via FTC for improper integrals)

Parent: AreaOfCircle.lean
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

namespace GaussianIntegralCircle

open MeasureTheory Real Filter

/-! ## Part 1: The Gaussian Integral via Mathlib -/

/-- **The Gaussian Integral**: ∫_{-∞}^{∞} e^{-x²} dx = √π.

    Mathlib proves this in `integral_gaussian`. We present it here
    as the answer to OQ-05, connecting it to the area-of-circle context.

    The connection to circles: the proof technique squares the integral
    to get ∫∫ e^{-(x²+y²)} dx dy, then uses polar coordinates.
    The factor 2π (circumference) × 1/2 (radial integral) = π.
    So (∫ e^{-x²} dx)² = π, giving ∫ e^{-x²} dx = √π.

    This is why π appears: the Gaussian integral secretly computes
    the area of a circle in disguise. -/
theorem gaussian_integral_eq_sqrt_pi :
    ∫ x : ℝ, rexp (-(x ^ 2)) = √π := by
  -- Mathlib's integral_gaussian gives ∫ x, exp (-b * x²) = √(π/b)
  -- Setting b = 1 gives ∫ x, exp (-x²) = √π
  have h := integral_gaussian (1 : ℝ)
  simp only [div_one] at h
  -- Rewrite -(x²) as -1 * x² to match integral_gaussian's integrand
  simp_rw [show ∀ x : ℝ, -(x ^ 2) = -(1 : ℝ) * x ^ 2 from fun x => by ring]
  exact h

/-! ## Part 2: Scaled Gaussian -/

/-- **Scaled Gaussian**: For a > 0, ∫ e^{-ax²} dx = √(π/a). -/
theorem scaled_gaussian (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, rexp (-(a * x ^ 2)) = √(π / a) := by
  -- integral_gaussian a gives ∫ x, exp (-a * x²) = √(π/a)
  -- Rewrite -(a * x²) as -a * x² to match
  simp_rw [show ∀ x : ℝ, -(a * x ^ 2) = -a * x ^ 2 from fun x => by ring]
  exact integral_gaussian a

/-! ## Part 3: Standard Normal Distribution

The standard Gaussian density φ(x) = (1/√(2π)) e^{-x²/2}
integrates to 1 over ℝ. This follows from the scaled
Gaussian integral with a = 1/2. -/

/-- The standard normal density integrates to 1.
    ∫ (1/√(2π)) e^{-x²/2} dx = 1. -/
theorem standard_normal_normalization :
    ∫ x : ℝ, (1 / √(2 * π)) * rexp (-(x ^ 2 / 2)) = 1 := by
  -- Pull constant out of integral
  rw [integral_const_mul]
  -- Evaluate ∫ e^{-x²/2} dx via scaled_gaussian with a = 1/2
  have h := scaled_gaussian (1 / 2) (by positivity)
  have h1 : ∫ x : ℝ, rexp (-(x ^ 2 / 2)) = √(2 * π) := by
    have heq : (fun x : ℝ => rexp (-(x ^ 2 / 2))) = (fun x : ℝ => rexp (-(1 / 2 * x ^ 2))) :=
      funext fun x => by congr 1; ring
    rw [heq, h]
    congr 1; field_simp
  rw [h1]
  -- (1/√(2π)) * √(2π) = 1
  rw [one_div, inv_mul_cancel₀]
  exact Real.sqrt_ne_zero'.mpr (by positivity)

/-! ## Part 4: Connection to Circle Area

**Why π appears in the Gaussian integral**

The proof of ∫ e^{-x²} dx = √π proceeds by:
1. Let I = ∫ e^{-x²} dx
2. I² = (∫ e^{-x²} dx)(∫ e^{-y²} dy) = ∫∫ e^{-(x²+y²)} dx dy  (Fubini)
3. In polar: x²+y² = r², dx dy = r dr dθ
4. I² = ∫₀²π ∫₀∞ r·e^{-r²} dr dθ = 2π · (1/2) = π
5. Hence I = √π

Step 4 contains both factors:
- 2π = circumference of unit circle (angular integral)
- 1/2 = ∫₀∞ r·e^{-r²} dr (radial integral, by substitution u = r²)

So the Gaussian integral is fundamentally a circle area computation. -/

/-- The radial component: ∫₀∞ r·e^{-r²} dr = 1/2.
    Proof by substitution u = r², du = 2r dr:
    ∫₀∞ r·e^{-r²} dr = (1/2) ∫₀∞ e^{-u} du = 1/2. -/
theorem radial_integral :
    ∫ r in Set.Ioi (0 : ℝ), r * rexp (-(r ^ 2)) = 1 / 2 := by
  -- Antiderivative F(r) = -(1/2) * exp(-r²), F'(r) = r * exp(-r²)
  -- F(0) = -1/2, lim_{r→∞} F(r) = 0
  -- By FTC for improper integrals: ∫₀^∞ r*exp(-r²) dr = 0 - (-1/2) = 1/2
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun r => -(1 / 2 : ℝ) * rexp (-(r ^ 2))) (x * rexp (-(x ^ 2))) x := by
    intro x _
    exact (((hasDerivAt_pow 2 x).neg.exp).const_mul (-(1 / 2 : ℝ))).congr_deriv
      (by simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
  have hexp_tend : Tendsto (fun r : ℝ => rexp (-(r ^ 2))) atTop (nhds 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  have htend : Tendsto (fun r : ℝ => -(1 / 2 : ℝ) * rexp (-(r ^ 2))) atTop (nhds 0) := by
    simpa using hexp_tend.const_mul (-(1 / 2 : ℝ))
  have hint : IntegrableOn (fun r => r * rexp (-(r ^ 2))) (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv
      (fun r hr => mul_nonneg (le_of_lt hr) (exp_pos _).le) htend
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  norm_num [Real.exp_zero] at h
  exact h

end GaussianIntegralCircle
