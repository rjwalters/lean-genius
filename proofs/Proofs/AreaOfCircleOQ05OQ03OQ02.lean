/-
  Gaussians form a convolution semigroup
  (area-of-circle-oq-05-oq-03-oq-02)

  A follow-up to `area-of-circle-oq-05-oq-03` ("The Gaussian is its own Fourier
  transform").  That entry, and its sibling `…-oq-01` (the dilation / uncertainty
  law), live entirely on the *Fourier* side.  Here we prove the complementary
  *density-side* statement: the family of centred Gaussian densities is closed
  under convolution, and the variances add.  Writing

      φ_σ(x) = e^{-x²/(2σ²)} / (σ·√(2π))        (σ > 0)

  for the centred normal density of standard deviation σ, the **convolution
  semigroup law** is

      ∫_ℝ φ_{σ₁}(y) · φ_{σ₂}(x − y) dy = φ_{√(σ₁²+σ₂²)}(x).        (★)

  This is the analytic heart of "the sum of two independent normals is normal,
  with variances adding" — i.e. the Gaussian / heat-kernel semigroup
  (Chapman–Kolmogorov for Brownian motion).

  HONEST SCOPE / NOVELTY.  Mathlib *does* contain the abstract,
  measure-theoretic versions of this fact
  (`ProbabilityTheory.gaussianReal_conv_gaussianReal` for `Measure.conv`, and
  `gaussianReal_add_gaussianReal_of_indepFun` for sums of independent variables).
  What is delivered here is the explicit Lebesgue-integral identity (★) in terms
  of the elementary density `φ_σ`, computed directly by completing the square and
  Mathlib's real Gaussian integral `integral_gaussian`.  This matches the
  deliberate "concrete integral, no abstract measure" register of the parent
  entries (the parent gives the concrete Fourier integral; here is the concrete
  convolution integral).  Everything is proved with 0 sorries and 0 axioms.

  METHOD ("complete the square in y").  With s = σ₁²+σ₂²,

      y²/(2σ₁²) + (x−y)²/(2σ₂²)
        = (s/(2σ₁²σ₂²))·(y − σ₁²x/s)²  +  x²/(2s),

  so the integrand factors as a constant (the last, y-free term) times a single
  shifted Gaussian in y; translation-invariance of Lebesgue measure removes the
  shift, `integral_gaussian` evaluates the remaining integral to √(π/A), and the
  prefactors collapse to exactly φ_{√s}(x).

  We also record the Fourier-side shadow of (★): the product of the two
  characteristic functions is the characteristic function of the convolution,
  e^{-σ₁²t²/2}·e^{-σ₂²t²/2} = e^{-(σ₁²+σ₂²)t²/2}, and that convolution preserves
  total mass (each φ_σ integrates to 1).

  References:
  - Stein–Shakarchi, *Fourier Analysis* (2003), Ch. 5 (the Gaussian / heat kernel).
  - Mathlib: `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
    (`integral_gaussian`), `Mathlib.Probability.Distributions.Gaussian.Real`.
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real MeasureTheory
open scoped Real

namespace GaussianConvolutionSemigroup

/-- The centred Gaussian (normal) density of standard deviation `σ`:
`φ_σ(x) = e^{-x²/(2σ²)} / (σ·√(2π))`, written here as a leading reciprocal times
an exponential `e^{-(1/(2σ²))·x²}` to line up with `integral_gaussian`. -/
noncomputable def φ (σ x : ℝ) : ℝ :=
  (σ * Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / (2 * σ ^ 2)) * x ^ 2)

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  COMPLETING THE SQUARE (POINTWISE ALGEBRA)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Completing the square.**  The combined quadratic exponent of the two
factors of the convolution integrand splits as a `y`-free constant plus a single
centred square in `y`.  Here `s = σ₁²+σ₂²`, the curvature is `A = s/(2σ₁²σ₂²)`,
the centre is `m = σ₁²x/s`, and the constant term is `B = x²/(2s)`. -/
theorem complete_the_square (σ₁ σ₂ x y : ℝ)
    (h₁ : σ₁ ≠ 0) (h₂ : σ₂ ≠ 0) (hs : σ₁ ^ 2 + σ₂ ^ 2 ≠ 0) :
    -(1 / (2 * σ₁ ^ 2)) * y ^ 2 + -(1 / (2 * σ₂ ^ 2)) * (x - y) ^ 2
      = -(x ^ 2 / (2 * (σ₁ ^ 2 + σ₂ ^ 2)))
        + -((σ₁ ^ 2 + σ₂ ^ 2) / (2 * σ₁ ^ 2 * σ₂ ^ 2))
          * (y - σ₁ ^ 2 * x / (σ₁ ^ 2 + σ₂ ^ 2)) ^ 2 := by
  field_simp
  ring

/-- The two leading reciprocals of `φ_{σ₁}·φ_{σ₂}` collapse:
`(σ₁√(2π))⁻¹·(σ₂√(2π))⁻¹ = 1/(σ₁σ₂·2π)` (using `√(2π)·√(2π) = 2π`). -/
theorem prefactor_collapse (σ₁ σ₂ : ℝ) :
    (σ₁ * Real.sqrt (2 * Real.pi))⁻¹ * (σ₂ * Real.sqrt (2 * Real.pi))⁻¹
      = 1 / (σ₁ * σ₂ * (2 * Real.pi)) := by
  rw [← mul_inv,
      show σ₁ * Real.sqrt (2 * Real.pi) * (σ₂ * Real.sqrt (2 * Real.pi))
        = σ₁ * σ₂ * (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) from by ring,
      Real.mul_self_sqrt (by positivity), one_div]

/-- Closed form for the residual Gaussian integral's value:
`√(π / A) = σ₁σ₂·√(2π) / √(σ₁²+σ₂²)` where `A = (σ₁²+σ₂²)/(2σ₁²σ₂²)`. -/
theorem sqrt_pi_div_A (σ₁ σ₂ : ℝ) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) :
    Real.sqrt (Real.pi / ((σ₁ ^ 2 + σ₂ ^ 2) / (2 * σ₁ ^ 2 * σ₂ ^ 2)))
      = σ₁ * σ₂ * Real.sqrt (2 * Real.pi) / Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2) := by
  have hπA : Real.pi / ((σ₁ ^ 2 + σ₂ ^ 2) / (2 * σ₁ ^ 2 * σ₂ ^ 2))
      = (σ₁ * σ₂) ^ 2 * (2 * Real.pi) / (σ₁ ^ 2 + σ₂ ^ 2) := by
    have : σ₁ ^ 2 + σ₂ ^ 2 ≠ 0 := by positivity
    field_simp
  rw [hπA, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  THE CONVOLUTION SEMIGROUP LAW
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Gaussian convolution semigroup law (★).**  The convolution of two
centred Gaussian densities is again a centred Gaussian density, with the
variances adding:

  `∫_ℝ φ_{σ₁}(y) · φ_{σ₂}(x − y) dy = φ_{√(σ₁²+σ₂²)}(x)`. -/
theorem gaussian_convolution (σ₁ σ₂ : ℝ) (h₁ : 0 < σ₁) (h₂ : 0 < σ₂) (x : ℝ) :
    (∫ y : ℝ, φ σ₁ y * φ σ₂ (x - y)) = φ (Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) x := by
  -- Abbreviations matching `complete_the_square`.
  set s : ℝ := σ₁ ^ 2 + σ₂ ^ 2 with hs_def
  have hspos : 0 < s := by rw [hs_def]; positivity
  set A : ℝ := s / (2 * σ₁ ^ 2 * σ₂ ^ 2) with hA_def
  have hApos : 0 < A := by rw [hA_def]; positivity
  set m : ℝ := σ₁ ^ 2 * x / s with hm_def
  set B : ℝ := x ^ 2 / (2 * s) with hB_def
  -- Constant prefactor of the integrand.
  set C : ℝ := 1 / (σ₁ * σ₂ * (2 * Real.pi)) with hC_def
  -- Pointwise: the integrand is `C·e^{-B}` times a single shifted Gaussian in `y`.
  have hpt : ∀ y : ℝ,
      φ σ₁ y * φ σ₂ (x - y)
        = C * Real.exp (-B) * Real.exp (-A * (y - m) ^ 2) := by
    intro y
    have hexp : -(1 / (2 * σ₁ ^ 2)) * y ^ 2 + -(1 / (2 * σ₂ ^ 2)) * (x - y) ^ 2
        = -B + -A * (y - m) ^ 2 := by
      rw [hB_def, hA_def, hm_def, hs_def]
      exact complete_the_square σ₁ σ₂ x y h₁.ne' h₂.ne' (by positivity)
    calc
      φ σ₁ y * φ σ₂ (x - y)
          = ((σ₁ * Real.sqrt (2 * Real.pi))⁻¹ * (σ₂ * Real.sqrt (2 * Real.pi))⁻¹)
              * (Real.exp (-(1 / (2 * σ₁ ^ 2)) * y ^ 2)
                  * Real.exp (-(1 / (2 * σ₂ ^ 2)) * (x - y) ^ 2)) := by
            simp only [φ]; ring
      _ = C * Real.exp (-(1 / (2 * σ₁ ^ 2)) * y ^ 2 + -(1 / (2 * σ₂ ^ 2)) * (x - y) ^ 2) := by
            rw [prefactor_collapse, ← Real.exp_add, ← hC_def]
      _ = C * Real.exp (-B + -A * (y - m) ^ 2) := by rw [hexp]
      _ = C * Real.exp (-B) * Real.exp (-A * (y - m) ^ 2) := by
            rw [Real.exp_add]; ring
  -- Evaluate the integral.
  calc
    (∫ y : ℝ, φ σ₁ y * φ σ₂ (x - y))
        = ∫ y : ℝ, (C * Real.exp (-B)) * Real.exp (-A * (y - m) ^ 2) := by
          simp_rw [hpt]
    _ = (C * Real.exp (-B)) * ∫ y : ℝ, Real.exp (-A * (y - m) ^ 2) := by
          rw [integral_const_mul]
    _ = (C * Real.exp (-B)) * ∫ u : ℝ, Real.exp (-A * u ^ 2) := by
          rw [show (∫ y : ℝ, Real.exp (-A * (y - m) ^ 2))
                = ∫ u : ℝ, Real.exp (-A * u ^ 2)
              from integral_sub_right_eq_self (fun u => Real.exp (-A * u ^ 2)) m]
    _ = (C * Real.exp (-B)) * Real.sqrt (Real.pi / A) := by
          rw [integral_gaussian]
    _ = φ (Real.sqrt s) x := by
          -- Unfold the target density and reduce `(√s)² = s`.
          simp only [φ]
          rw [Real.sq_sqrt hspos.le]
          -- The two exponentials agree: `-(1/(2s))·x² = -B`.
          rw [show -(1 / (2 * s)) * x ^ 2 = -B from by rw [hB_def]; ring]
          -- Closed form for `√(π/A)` and the scalar collapse.
          rw [hC_def, hA_def, sqrt_pi_div_A σ₁ σ₂ h₁ h₂, ← hs_def]
          rw [eq_comm]
          have hsq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
            Real.mul_self_sqrt (by positivity)
          have hsne : Real.sqrt s ≠ 0 := Real.sqrt_ne_zero'.mpr hspos
          have h2pne : Real.sqrt (2 * Real.pi) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
          field_simp
          nlinarith [hsq, Real.exp_pos (-B), Real.sqrt_nonneg s,
            Real.sqrt_nonneg (2 * Real.pi)]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  COROLLARIES — MASS PRESERVATION AND THE FOURIER SHADOW
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Each centred Gaussian density integrates to `1`: convolution of probability
densities is again a probability density.  (The total-mass invariant behind (★).) -/
theorem gaussian_density_integral_eq_one (σ : ℝ) (hσ : 0 < σ) :
    (∫ x : ℝ, φ σ x) = 1 := by
  simp only [φ]
  rw [integral_const_mul, integral_gaussian (1 / (2 * σ ^ 2))]
  have h1 : Real.pi / (1 / (2 * σ ^ 2)) = (σ * Real.sqrt (2 * Real.pi)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [h1, Real.sqrt_sq (by positivity)]
  exact inv_mul_cancel₀ (by positivity)

/-- The (real) characteristic function of the centred normal `N(0,σ²)`:
`χ_σ(t) = e^{-σ²t²/2}` — the value proved on the Fourier side in
`area-of-circle-oq-05-oq-03` (σ = 1) and `…-oq-01` (general σ). -/
noncomputable def χ (σ t : ℝ) : ℝ := Real.exp (-(σ ^ 2) * t ^ 2 / 2)

/-- **Fourier shadow of (★).**  The product of the two characteristic functions
is the characteristic function of the convolution: the variances add.  This is
exactly "Fourier transform turns convolution into multiplication" specialised to
Gaussians, dual to the integral identity `gaussian_convolution`. -/
theorem charFun_mul (σ₁ σ₂ t : ℝ) :
    χ σ₁ t * χ σ₂ t = χ (Real.sqrt (σ₁ ^ 2 + σ₂ ^ 2)) t := by
  simp only [χ]
  rw [← Real.exp_add, Real.sq_sqrt (by positivity)]
  ring_nf

/-- Sanity check / normalisation: at `t = 0` every characteristic function is `1`. -/
theorem charFun_zero (σ : ℝ) : χ σ 0 = 1 := by simp [χ]

end GaussianConvolutionSemigroup
