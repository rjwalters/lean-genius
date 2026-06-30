/-
  The Moment & Cumulant Generating Function of the Gaussian
  (area-of-circle-oq-05-oq-03-oq-04)

  The parent `area-of-circle-oq-05-oq-03` ("the Gaussian is its own Fourier
  transform") evaluates the Gaussian's transform only along the *imaginary*
  frequency axis:

      ∫_ℝ e^{i t x} e^{-x²/2} dx = e^{-t²/2} √(2π)     (characteristic function).

  Here we evaluate the *bilateral two-sided transform* of the Gaussian at an
  arbitrary COMPLEX frequency `z`, exhibiting it as a single entire function:

      ∫_ℝ e^{z x} e^{-x²/2} dx = e^{z²/2} √(2π)        (∀ z ∈ ℂ).            (★)

  Two real slices of (★) are the two classical "generating functions" of the
  standard normal distribution N(0,1):

    • z = s ∈ ℝ  →  the MOMENT generating function
          ∫_ℝ e^{s x} (e^{-x²/2}/√(2π)) dx = e^{s²/2},
    • z = i t    →  the CHARACTERISTIC function (the parent), recovered from (★)
          by analytic continuation, with z² = (i t)² = -t².

  Taking the logarithm of the normalized MGF gives the CUMULANT generating
  function

      K(s) = log E[e^{s X}] = s²/2,                                         (★★)

  which is *exactly quadratic*.  Vanishing of all cumulants above order two is
  the algebraic fingerprint of the Gaussian (Marcinkiewicz): no other
  distribution has a polynomial cumulant generating function.  Here we prove the
  quadratic identity (★★) outright.

  METHOD.  The master identity (★) is Mathlib's `integral_cexp_quadratic`
  (the analytic Gaussian integral over a vertical strip) at b = -1/2, c = z,
  d = 0.  The real MGF is proved independently and elementarily by *real*
  completion of the square — `s x - x²/2 = -(x-s)²/2 + s²/2` — followed by
  translation invariance of Lebesgue measure (`integral_sub_right_eq_self`) and
  the real Gaussian integral `integral_gaussian`; no contour shift is needed on
  the real axis.

  Everything is proved with 0 sorries and 0 axioms.

  References:
  - Moment / cumulant generating functions of the normal law: Billingsley,
    Probability and Measure, §21; Feller, Vol. II, Ch. XV.
  - Marcinkiewicz's theorem (polynomial cumulant ⟹ degree ≤ 2 ⟹ Gaussian).
  - Mathlib: Analysis.SpecialFunctions.Gaussian.FourierTransform / GaussianIntegral
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real Complex MeasureTheory
open scoped Real

namespace GaussianMGF

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  THE √(2π) CONSTANT FROM THE CONTOUR INTEGRAL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Mathlib contour constant `(π / -(-1/2))^(1/2)` is the complex coercion of
    the real `√(2π)`. -/
theorem cpow_half_two_pi :
    ((π : ℂ) / -(-1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [show ((π : ℂ) / -(-1 / 2 : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
  norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  THE MASTER IDENTITY — THE ENTIRE BILATERAL TRANSFORM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Gaussian's two-sided transform is itself Gaussian, as an entire
    function of the complex frequency `z`:**

      ∫_ℝ e^{z x} · e^{-x²/2} dx = e^{z²/2} · √(2π).

    This single identity unifies the characteristic function (`z` imaginary) and
    the moment generating function (`z` real) of the standard normal. -/
theorem gaussian_bilateral_transform (z : ℂ) :
    ∫ x : ℝ, Complex.exp (z * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (z ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have key : (fun x : ℝ => Complex.exp (z * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = (fun x : ℝ => Complex.exp ((-1 / 2 : ℂ) * (x : ℂ) ^ 2 + z * (x : ℂ) + 0)) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [show (∫ x : ℝ, Complex.exp (z * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
        = ∫ x : ℝ, Complex.exp ((-1 / 2 : ℂ) * (x : ℂ) ^ 2 + z * (x : ℂ) + 0) by rw [key]]
  rw [integral_cexp_quadratic (by norm_num : ((-1 / 2 : ℂ)).re < 0) z 0]
  rw [cpow_half_two_pi]
  rw [show ((0 : ℂ) - z ^ 2 / (4 * (-1 / 2 : ℂ))) = z ^ 2 / 2 by ring]
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE CHARACTERISTIC FUNCTION (PARENT) AS THE IMAGINARY SLICE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Recovery of the parent characteristic function by analytic continuation.**
    Setting `z = i t` in the master identity and using `(i t)² = -t²` recovers

      ∫_ℝ e^{i t x} e^{-x²/2} dx = e^{-t²/2} √(2π). -/
theorem gaussian_characteristic_recovered (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h := gaussian_bilateral_transform (Complex.I * t)
  rw [show (Complex.I * (t : ℂ)) ^ 2 / 2 = -(t : ℂ) ^ 2 / 2 by
    rw [mul_pow, Complex.I_sq]; ring] at h
  exact h

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  THE REAL MOMENT GENERATING FUNCTION (ELEMENTARY)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The real Gaussian integral in the normalization used here:
    `∫_ℝ e^{-x²/2} dx = √(2π)`. -/
theorem integral_rexp_neg_half_sq :
    ∫ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * π) := by
  have h := integral_gaussian (1 / 2)
  rw [show (Real.sqrt (π / (1 / 2))) = Real.sqrt (2 * π) by ring_nf] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  ring

/-- **The moment generating function of the standard normal (un-normalized).**
    By *real* completion of the square `s x - x²/2 = -(x-s)²/2 + s²/2` and the
    translation invariance of Lebesgue measure:

      ∫_ℝ e^{s x} e^{-x²/2} dx = e^{s²/2} √(2π).

    No contour shift is needed — this lives entirely on the real axis. -/
theorem gaussian_mgf_real (s : ℝ) :
    ∫ x : ℝ, Real.exp (s * x) * Real.exp (-x ^ 2 / 2)
      = Real.exp (s ^ 2 / 2) * Real.sqrt (2 * π) := by
  have key : (fun x : ℝ => Real.exp (s * x) * Real.exp (-x ^ 2 / 2))
      = (fun x : ℝ => Real.exp (-(x - s) ^ 2 / 2) * Real.exp (s ^ 2 / 2)) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [show (∫ x : ℝ, Real.exp (s * x) * Real.exp (-x ^ 2 / 2))
        = ∫ x : ℝ, Real.exp (-(x - s) ^ 2 / 2) * Real.exp (s ^ 2 / 2) by rw [key]]
  rw [MeasureTheory.integral_mul_const]
  rw [show (fun x : ℝ => Real.exp (-(x - s) ^ 2 / 2))
        = (fun x : ℝ => Real.exp (-x ^ 2 / 2)) ∘ (fun x => x - s) by funext x; simp]
  rw [show (∫ x : ℝ, ((fun x : ℝ => Real.exp (-x ^ 2 / 2)) ∘ (fun x => x - s)) x)
        = ∫ x : ℝ, Real.exp (-(x - s) ^ 2 / 2) by rfl]
  rw [MeasureTheory.integral_sub_right_eq_self (fun x : ℝ => Real.exp (-x ^ 2 / 2)) s]
  rw [integral_rexp_neg_half_sq]
  ring

/-- **The MGF of N(0,1) (normalized).**

      ∫_ℝ e^{s x} (e^{-x²/2}/√(2π)) dx = e^{s²/2}.

    The standard normal's moment generating function is `e^{s²/2}`. -/
theorem gaussian_mgf_normalized (s : ℝ) :
    ∫ x : ℝ, Real.exp (s * x) * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π))
      = Real.exp (s ^ 2 / 2) := by
  have hpos : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  simp_rw [← mul_div_assoc]
  rw [MeasureTheory.integral_div, gaussian_mgf_real]
  rw [mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V:  THE CUMULANT GENERATING FUNCTION IS EXACTLY QUADRATIC
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The cumulant generating function of the standard normal is `s²/2`.**

      K(s) = log E[e^{s X}] = log ( ∫ e^{s x} (e^{-x²/2}/√(2π)) dx ) = s²/2.

    A *polynomial* cumulant generating function characterizes the Gaussian among
    all probability distributions (Marcinkiewicz's theorem); here `K` is exactly
    the degree-2 polynomial `s²/2`, so every cumulant of order ≥ 3 vanishes. -/
theorem gaussian_cumulant_quadratic (s : ℝ) :
    Real.log (∫ x : ℝ, Real.exp (s * x) * (Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π)))
      = s ^ 2 / 2 := by
  rw [gaussian_mgf_normalized, Real.log_exp]

/-- **Mean zero / total mass.**  Setting `s = 0` in the normalized MGF gives the
    fact that the standard density integrates to `1`. -/
theorem gaussian_density_total_mass :
    ∫ x : ℝ, Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * π) = 1 := by
  have h := gaussian_mgf_normalized 0
  simpa using h

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI:  STRUCTURE OF THE ENTIRE TRANSFORM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Evenness of the transform.**  Because the master right-hand side depends on
    `z` only through `z²`, the bilateral transform is an even function of the
    frequency: `T(-z) = T(z)`.  This mirrors the evenness of the Gaussian itself. -/
theorem gaussian_transform_even (z : ℂ) :
    (∫ x : ℝ, Complex.exp ((-z) * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = ∫ x : ℝ, Complex.exp (z * x) * Complex.exp (-(x : ℂ) ^ 2 / 2) := by
  rw [gaussian_bilateral_transform, gaussian_bilateral_transform]
  rw [show (-z) ^ 2 = z ^ 2 by ring]

/-- **The master identity at `z = 0`:** `∫_ℝ e^{-x²/2} dx = √(2π)` (complex form),
    the common normalizing constant of both generating functions. -/
theorem gaussian_transform_zero :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2 / 2) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h := gaussian_bilateral_transform 0
  simpa using h

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The Moment & Cumulant Generating Function of the Gaussian  (oq-05-oq-03-oq-04)

### What's proved (0 sorries, 0 axioms):
- `gaussian_bilateral_transform`: **∫ e^{zx} e^{-x²/2} dx = e^{z²/2} √(2π)** for
  every complex `z` — the entire two-sided transform unifying the characteristic
  function and the moment generating function.
- `gaussian_characteristic_recovered`: the parent characteristic function is the
  imaginary slice `z = i t`, recovered by analytic continuation (`(it)² = -t²`).
- `gaussian_mgf_real` / `gaussian_mgf_normalized`: the **moment generating
  function** `∫ e^{sx}(e^{-x²/2}/√(2π)) = e^{s²/2}`, proved elementarily on the
  real axis by real completion of the square + translation invariance.
- `gaussian_cumulant_quadratic`: the **cumulant generating function `K(s)=s²/2`**
  is exactly quadratic — the algebraic fingerprint of the Gaussian
  (all cumulants of order ≥ 3 vanish; cf. Marcinkiewicz).
- `gaussian_density_total_mass`: the standard density integrates to 1 (`s=0`).
- `gaussian_transform_even`, `gaussian_transform_zero`: the transform is even in
  the frequency and reduces at `z=0` to the normalizing constant `√(2π)`.

### Honest scope:
The master identity reuses Mathlib's analytic Gaussian integral
`integral_cexp_quadratic`; the real MGF is an independent elementary proof.  The
characterization direction of Marcinkiewicz's theorem (polynomial cumulant ⟹
Gaussian) is cited for context, not formalized — what is proved here is the
forward computation `K(s) = s²/2`.
-/

#check @gaussian_bilateral_transform
#check @gaussian_characteristic_recovered
#check @gaussian_mgf_real
#check @gaussian_mgf_normalized
#check @gaussian_cumulant_quadratic

end GaussianMGF
