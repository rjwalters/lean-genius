/-
  The Gaussian Dilation Law and the Uncertainty Duality of the Fourier Transform
  (area-of-circle-oq-05-oq-03-oq-01)

  A follow-up to `area-of-circle-oq-05-oq-03` ("the Gaussian is its own Fourier
  transform"), which proved the SELF-dual case (variance 1):

      ∫_ℝ e^{i t x} · e^{-x²/2} dx = e^{-t²/2} · √(2π).

  Here we prove the full **one-parameter dilation law**: for every width σ > 0,

      ∫_ℝ e^{i t x} · e^{-x²/(2σ²)} dx = σ·√(2π) · e^{-σ² t²/2},          (★)

  together with its probability-normalized companion

      ∫_ℝ e^{i t x} · (e^{-x²/(2σ²)} / (σ√(2π))) dx = e^{-σ² t²/2}.        (★★)

  The right-hand side of (★★) is the characteristic function of the centered
  normal distribution N(0, σ²).

  STRUCTURAL PAYOFF — THE UNCERTAINTY DUALITY.  The input density on the left of
  (★★) is a Gaussian of spatial width σ; the output on the right is, up to the
  unitary normalization, a Gaussian of *frequency* width 1/σ:

      e^{-σ² t²/2} = e^{-t² / (2·(1/σ)²)}.

  Thus the Fourier transform INVERTS the width: a narrow bump (small σ) transforms
  to a wide bump (large 1/σ), and the product of the two scales is constant,

      (input width) · (output width) = σ · (1/σ) = 1,

  which is the elementary heart of the Heisenberg uncertainty principle.  The
  self-dual σ = 1 case of the parent is exactly the fixed point of this duality.

  METHOD.  Completing the square in the form  i t x − b x² = −b(x + c i)² − b c²
  with  b = 1/(2σ²)  and  c = −t/(2b) = −t σ²  (so 2 b c = −t), then evaluating
  the resulting vertical-strip-shifted Gaussian by Mathlib's
  `GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I`.  The completing-the-
  square step is proved division-free (parametrized by the relation 2 b c = −t),
  so the only `field_simp`/`I² = −1` work is the final algebraic bookkeeping.

  Everything is proved with 0 sorries and 0 axioms.

  References:
  - Stein–Shakarchi, *Fourier Analysis* (2003), Ch. 5 (the Gaussian and its
    dilation/uncertainty behaviour).
  - Mathlib: Analysis.SpecialFunctions.Gaussian.FourierTransform
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real Complex MeasureTheory
open scoped Real

namespace GaussianDilation

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  COMPLETING THE SQUARE (DIVISION-FREE, POINTWISE)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Completing the square, parametrized by the relation `2 b c = -t`.**
    For real `b, c, t, x` with `2 b c = -t`,

      e^{i t x} · e^{-b x²} = e^{-b (x + c i)²} · e^{-b c²}.

    Keeping `c` abstract (with the single algebraic constraint `2 b c = -t`) makes
    the identity hold with no division, so it follows by `linear_combination`
    using only `i² = -1`. -/
theorem complete_square_param (b c t : ℝ) (h : 2 * b * c = -t) (x : ℝ) :
    Complex.exp (Complex.I * t * x) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)
      = Complex.exp (-(b : ℂ) * ((x : ℂ) + (c : ℂ) * Complex.I) ^ 2)
        * Complex.exp (-((b : ℂ) * (c : ℂ) ^ 2)) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc : (2 : ℂ) * (b : ℂ) * (c : ℂ) = -(t : ℂ) := by exact_mod_cast h
  linear_combination (Complex.I * (x : ℂ)) * hc + ((b : ℂ) * (c : ℂ) ^ 2) * Complex.I_sq

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  THE CONSTANT √(π/b) FROM THE CONTOUR INTEGRAL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Mathlib contour-integral constant `(π / b)^(1/2)` is the complex coercion
    of the real `√(π/b)` (for `b > 0`). -/
theorem cpow_half_eq_sqrt (b : ℝ) (hb : 0 < b) :
    ((π : ℂ) / (b : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / b) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ≤ π / b := by positivity
  rw [show ((π : ℂ) / (b : ℂ)) = ((π / b : ℝ) : ℂ) by push_cast; ring]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
  norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE GENERAL GAUSSIAN FOURIER INTEGRAL (COEFFICIENT FORM)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Fourier integral of a coefficient-`b` Gaussian.**  For `b > 0`,

      ∫_ℝ e^{i t x} · e^{-b x²} dx = e^{-b c²} · √(π/b),   where  c = -t/(2b).

    (The `t`-dependence sits in `c`; rewriting `b = 1/(2σ²)` gives the width form.) -/
theorem gaussian_fourier_param (b t : ℝ) (hb : 0 < b) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(b : ℂ) * (x : ℂ) ^ 2)
      = Complex.exp (-((b : ℂ) * ((-t / (2 * b) : ℝ) : ℂ) ^ 2))
        * ((Real.sqrt (π / b) : ℝ) : ℂ) := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hrel : 2 * b * (-t / (2 * b)) = -t := by field_simp
  simp_rw [complete_square_param b (-t / (2 * b)) t hrel]
  rw [MeasureTheory.integral_mul_const]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
        (b := (b : ℂ)) (by rw [Complex.ofReal_re]; exact hb) (-t / (2 * b))]
  rw [cpow_half_eq_sqrt b hb]
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  THE DILATION LAW (WIDTH FORM) AND ITS NORMALIZATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Gaussian dilation law (un-normalized).**  For every width `σ > 0`,

      ∫_ℝ e^{i t x} · e^{-x²/(2σ²)} dx = e^{-σ² t²/2} · σ·√(2π). -/
theorem gaussian_fourier_dilated (σ t : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2))
      = Complex.exp (-((σ : ℂ) ^ 2 * (t : ℂ) ^ 2 / 2)) * ((σ * Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0
  have hb : 0 < (1 / (2 * σ ^ 2)) := by positivity
  -- rewrite the density into coefficient form  e^{-(1/(2σ²)) x²}
  have hpt : ∀ x : ℝ,
      (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2)) = (-((1 / (2 * σ ^ 2) : ℝ) : ℂ)) * (x : ℂ) ^ 2 := by
    intro x; push_cast; ring
  simp_rw [hpt]
  rw [gaussian_fourier_param (1 / (2 * σ ^ 2)) t hb]
  congr 1
  · -- the exponent:  -(b c²) = -(σ² t²/2)
    congr 1
    push_cast
    field_simp
  · -- the constant:  √(π / (1/(2σ²))) = σ·√(2π)
    congr 1
    rw [show (π / (1 / (2 * σ ^ 2))) = σ ^ 2 * (2 * π) by field_simp]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ σ ^ 2), Real.sqrt_sq hσ.le]

/-- **The centered normal density is its own Fourier transform, up to width
    inversion (normalized).**  For `σ > 0`,

      ∫_ℝ e^{i t x} · (e^{-x²/(2σ²)} / (σ√(2π))) dx = e^{-σ² t²/2}.

    The right-hand side is the characteristic function of `N(0, σ²)`. -/
theorem gaussian_fourier_dilated_normalized (σ t : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * (Complex.exp (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2)) / ((σ * Real.sqrt (2 * π) : ℝ) : ℂ))
      = Complex.exp (-((σ : ℂ) ^ 2 * (t : ℂ) ^ 2 / 2)) := by
  have hC : ((σ * Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    have : 0 < σ * Real.sqrt (2 * π) :=
      mul_pos hσ (Real.sqrt_pos.mpr (by positivity))
    exact ne_of_gt this
  simp_rw [← mul_div_assoc]
  rw [MeasureTheory.integral_div, gaussian_fourier_dilated σ t hσ]
  rw [mul_div_assoc, div_self hC, mul_one]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V:  THE UNCERTAINTY DUALITY AND CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The uncertainty duality (explicit width inversion).**  The Fourier transform
    of the centered normal density of width `σ` is the Gaussian of width `1/σ`:

      ∫_ℝ e^{i t x} · (e^{-x²/(2σ²)} / (σ√(2π))) dx = e^{-t² / (2·(1/σ)²)}.

    Read against `gaussian_fourier_dilated_normalized`, this is the statement that
    Fourier transformation sends width `σ` to width `1/σ`. -/
theorem dilation_duality (σ t : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * (Complex.exp (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2)) / ((σ * Real.sqrt (2 * π) : ℝ) : ℂ))
      = Complex.exp (-(t : ℂ) ^ 2 / (2 * ((1 / σ : ℝ) : ℂ) ^ 2)) := by
  have hσC : (σ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hσ)
  rw [gaussian_fourier_dilated_normalized σ t hσ]
  congr 1
  push_cast
  field_simp

/-- **The product of input and output widths is `1`** — the elementary uncertainty
    relation underlying the duality.  Input density width `σ`, transform width `1/σ`. -/
theorem dilation_width_product (σ : ℝ) (hσ : 0 < σ) :
    σ * (1 / σ) = 1 := by
  rw [mul_one_div, div_self (ne_of_gt hσ)]

/-- **Total mass / `t = 0`:** the centered normal density of width `σ` integrates
    to `1`. -/
theorem gaussian_density_total_mass (σ : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2)) / ((σ * Real.sqrt (2 * π) : ℝ) : ℂ)
      = 1 := by
  simpa using gaussian_fourier_dilated_normalized σ 0 hσ

/-- **The un-normalized width-`σ` Gaussian integral:** `∫ e^{-x²/(2σ²)} dx = σ√(2π)`
    (the `t = 0` shadow of the dilation law). -/
theorem integral_gaussian_dilated (σ : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2 / (2 * (σ : ℂ) ^ 2)) = ((σ * Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simpa using gaussian_fourier_dilated σ 0 hσ

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The Gaussian dilation law and the uncertainty duality  (oq-05-oq-03-oq-01)

### What's proved (0 sorries, 0 axioms):
- `complete_square_param`: division-free completing-the-square
  e^{itx}e^{-bx²} = e^{-b(x+ci)²}e^{-bc²} under `2bc = -t` (via i² = -1).
- `cpow_half_eq_sqrt`: the Mathlib contour constant (π/b)^(1/2) = √(π/b), b > 0.
- `gaussian_fourier_param`: ∫ e^{itx} e^{-bx²} dx = e^{-bc²}·√(π/b), c = -t/(2b).
- `gaussian_fourier_dilated`: **∫ e^{itx} e^{-x²/(2σ²)} dx = e^{-σ²t²/2}·σ√(2π)** —
  the full one-parameter dilation law (the parent is the σ = 1 fixed point).
- `gaussian_fourier_dilated_normalized`: **∫ e^{itx}(e^{-x²/(2σ²)}/(σ√(2π))) dx
  = e^{-σ²t²/2}** — the characteristic function of N(0, σ²).
- `dilation_duality`: the transform of a width-σ density is the width-(1/σ)
  Gaussian e^{-t²/(2(1/σ)²)} — Fourier inverts the width.
- `dilation_width_product`: σ·(1/σ) = 1, the elementary uncertainty relation.
- `gaussian_density_total_mass`, `integral_gaussian_dilated`: the t = 0 shadows.

### Relation to the parent:
The parent (`area-of-circle-oq-05-oq-03`) proved the self-dual case σ = 1.  This
entry promotes that single identity to the full dilation group and isolates the
structural phenomenon — Fourier transformation inverts Gaussian width — that the
σ = 1 case hides by being its own fixed point.
-/

#check @gaussian_fourier_dilated
#check @gaussian_fourier_dilated_normalized
#check @dilation_duality
#check @dilation_width_product

end GaussianDilation
