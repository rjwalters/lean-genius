/-
  The first Hermite function is a Fourier eigenfunction
  (area-of-circle-oq-05-oq-03-oq-05)

  A follow-up open question from `area-of-circle-oq-05-oq-03` ("The Gaussian is
  its own Fourier transform").  The parent proves that the Gaussian density
  e^{-x²/2} is fixed by the Fourier transform — it is the *ground state*, the
  eigenfunction with eigenvalue 1.  Here we climb one rung of the Hermite ladder
  and prove that the **first Hermite function**

      ψ₁(x) = x · e^{-x²/2}

  is again a Fourier eigenfunction, now with eigenvalue `i` (the first excited
  state of the harmonic oscillator).  Concretely, in explicit Lebesgue-integral
  form,

      ∫_ℝ e^{i t x} · x · e^{-x²/2} dx = i · t · e^{-t²/2} · √(2π)
                                       = (i · √(2π)) · ψ₁(t).

  Since ψ₁(t) = t·e^{-t²/2}, the right-hand side is `i·√(2π)·ψ₁(t)`, i.e. ψ₁ is
  carried to a constant (i·√(2π)) times itself: it is an eigenfunction of the
  (un-normalized) Fourier transform with eigenvalue `i·√(2π)`, equivalently
  eigenvalue `i` under the unitary normalization.  Together with the parent
  (Gaussian ↦ eigenvalue 1 = i⁰) this exhibits the first two rungs of the
  classical Fourier eigenvalue ladder `iⁿ`.

  METHOD.  Differentiate the parent Gaussian Fourier identity
      F(t) := ∫ e^{i t x} e^{-x²/2} dx = e^{-t²/2}·√(2π)
  with respect to the frequency `t`.  Differentiating under the integral sign
  pulls down a factor `i x`:
      F'(t) = ∫ (i x) e^{i t x} e^{-x²/2} dx,
  while differentiating the closed form gives F'(t) = -t·e^{-t²/2}·√(2π).
  Equating and dividing by `i` yields the stated value.  The differentiation
  under the integral is justified by `hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  with the `t`-independent dominating function `|x|·e^{-x²/2}` (the derivative in
  `t` has modulus `|x|·e^{-x²/2}` because `|e^{i t x}| = 1`).

  Everything is proved with 0 sorries and 0 axioms.

  References:
  - Hermite functions as eigenfunctions of the Fourier transform, e.g.
    Stein–Shakarchi, Fourier Analysis (2003), Ch. 5–6; Folland, Harmonic
    Analysis in Phase Space.
  - Mathlib: Analysis.SpecialFunctions.Gaussian.FourierTransform,
    Analysis.Calculus.ParametricIntegral.
-/
import Mathlib

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Real Complex MeasureTheory
open scoped Real

namespace GaussianHermiteFourier

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  THE PARENT GAUSSIAN FOURIER IDENTITY (reproved, self-contained)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Completing the square at the level of the integrand:
    e^{i t x} · e^{-x²/2} = e^{-(1/2)(x + (-t)·i)²} · e^{-t²/2}. -/
theorem integrand_complete_square (t x : ℝ) :
    Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(((1 : ℝ) / 2 : ℝ) : ℂ) * ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) ^ 2)
        * Complex.exp (-(t : ℂ) ^ 2 / 2) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  linear_combination (t : ℂ) ^ 2 / 2 * Complex.I_sq

/-- The Mathlib contour constant `(π/(1/2))^(1/2)` is the coercion of `√(2π)`. -/
theorem cpow_half_eq_sqrt_two_pi :
    ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  have h0 : (0 : ℝ) ≤ 2 * π := by positivity
  rw [show ((π : ℂ) / (((1 : ℝ) / 2 : ℝ) : ℂ)) = ((2 * π : ℝ) : ℂ) by push_cast; ring]
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow h0]
  norm_num

/-- **The Gaussian is its own Fourier transform** (parent result, reproved):
    ∫ e^{i t x} e^{-x²/2} dx = e^{-t²/2}·√(2π). -/
theorem gaussian_fourier_real (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
      = Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  simp_rw [integrand_complete_square t]
  rw [MeasureTheory.integral_mul_const]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
        (b := (((1 : ℝ) / 2 : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; norm_num) (-t)]
  rw [cpow_half_eq_sqrt_two_pi]
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  ANALYTIC INGREDIENTS FOR DIFFERENTIATION UNDER THE INTEGRAL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The norm of the integrand `e^{i t x}·e^{-x²/2}` is the real Gaussian
    `e^{-(1/2)x²}` (the phase has modulus one). -/
theorem norm_integrand (t x : ℝ) :
    ‖Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)‖
      = Real.exp (-(1 / 2) * x ^ 2) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  have h1 : (Complex.I * (t : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have h2 : (-(x : ℂ) ^ 2 / 2).re = -(1 / 2) * x ^ 2 := by
    have : (-(x : ℂ) ^ 2 / 2) = (((-(1 / 2) * x ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [h1, h2, Real.exp_zero, one_mul]

/-- Integrability of the Gaussian Fourier integrand for each frequency `t`. -/
theorem integrable_integrand (t : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)) := by
  refine Integrable.mono' (g := fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2))
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Filter.Eventually.of_forall (fun x => le_of_eq (norm_integrand t x))

/-- The pointwise `t`-derivative of the integrand brings down a factor `i x`. -/
theorem hasDerivAt_integrand (t x : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      (Complex.I * x * Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)) t := by
  have hbase :
      HasDerivAt (fun z : ℂ => Complex.exp (Complex.I * z * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
        (Complex.exp (Complex.I * (t : ℂ) * x) * (Complex.I * 1 * x)
          * Complex.exp (-(x : ℂ) ^ 2 / 2)) (t : ℂ) := by
    have hlin : HasDerivAt (fun z : ℂ => Complex.I * z * (x : ℂ)) (Complex.I * 1 * (x : ℂ)) (t : ℂ) :=
      ((hasDerivAt_id (t : ℂ)).const_mul Complex.I).mul_const (x : ℂ)
    exact (hlin.cexp).mul_const (Complex.exp (-(x : ℂ) ^ 2 / 2))
  have := hbase.comp_ofReal (z := t)
  convert this using 1
  ring

/-- The dominating function `‖x · e^{-(1/2)x²}‖ = |x|·e^{-(1/2)x²}` is integrable. -/
theorem integrable_bound :
    Integrable (fun x : ℝ => ‖(x : ℝ) * Real.exp (-(1 / 2) * x ^ 2)‖) :=
  (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).norm

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE FIRST HERMITE FOURIER EIGENFUNCTION
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The first Hermite function is a Fourier eigenfunction.**

      ∫_ℝ e^{i t x} · x · e^{-x²/2} dx = i · t · e^{-t²/2} · √(2π). -/
theorem gaussian_fourier_first_hermite (t : ℝ) :
    (∫ x : ℝ, (x : ℂ) * Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = Complex.I * t * Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
  -- Differentiate F(s) = ∫ e^{i s x} e^{-x²/2} dx under the integral sign at s = t.
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ε := 1)
    (bound := fun x : ℝ => ‖(x : ℝ) * Real.exp (-(1 / 2) * x ^ 2)‖)
    (F := fun s x : ℝ => Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
    (F' := fun s x : ℝ =>
      Complex.I * x * Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
    (x₀ := t)
    one_pos
    (Filter.Eventually.of_forall (fun s => (integrable_integrand s).aestronglyMeasurable))
    (integrable_integrand t)
    (by
      apply Continuous.aestronglyMeasurable
      fun_prop)
    (by
      refine Filter.Eventually.of_forall (fun x s _ => ?_)
      refine le_of_eq ?_
      show ‖Complex.I * (x : ℂ) * Complex.exp (Complex.I * (s : ℝ) * x)
            * Complex.exp (-(x : ℂ) ^ 2 / 2)‖ = ‖(x : ℝ) * Real.exp (-(1 / 2) * x ^ 2)‖
      rw [show Complex.I * (x : ℂ) * Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2)
            = Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2) * (Complex.I * (x : ℂ))
          by ring]
      rw [norm_mul, norm_integrand, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_comm _ _)
    integrable_bound
    (Filter.Eventually.of_forall (fun x s _ => hasDerivAt_integrand s x))
  -- Replace the integral by the parent closed form, then differentiate it.
  have hclosed : (fun s : ℝ =>
        ∫ x : ℝ, Complex.exp (Complex.I * s * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ)) :=
    funext gaussian_fourier_real
  rw [hclosed] at hderiv
  -- Derivative of the closed form e^{-s²/2}·√(2π) is -s·e^{-s²/2}·√(2π).
  have hderiv2 :
      HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ))
        (-(t : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ)) t := by
    have hbase :
        HasDerivAt (fun z : ℂ => Complex.exp (-z ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ))
          (Complex.exp (-(t : ℂ) ^ 2 / 2) * (-(t : ℂ))
            * ((Real.sqrt (2 * π) : ℝ) : ℂ)) (t : ℂ) := by
      have hquad : HasDerivAt (fun z : ℂ => -z ^ 2 / 2) (-(t : ℂ)) (t : ℂ) := by
        have h : HasDerivAt (fun z : ℂ => z ^ 2) (2 * (t : ℂ)) (t : ℂ) := by
          simpa using hasDerivAt_pow 2 (t : ℂ)
        convert h.neg.div_const 2 using 1
        ring
      exact (hquad.cexp).mul_const ((Real.sqrt (2 * π) : ℝ) : ℂ)
    have := hbase.comp_ofReal (z := t)
    convert this using 1
    ring
  -- Equate the two derivatives of the same function.
  have heq :
      (∫ x : ℝ,
          Complex.I * x * Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
        = -(t : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ) :=
    hderiv.unique hderiv2
  -- Pull the constant factor `i` out of the integral.
  rw [show (fun x : ℝ =>
        Complex.I * x * Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      = (fun x : ℝ =>
        Complex.I * ((x : ℂ) * Complex.exp (Complex.I * t * x)
          * Complex.exp (-(x : ℂ) ^ 2 / 2))) from by funext x; ring] at heq
  rw [MeasureTheory.integral_const_mul] at heq
  -- Solve `i · J = R` for `J`, using `i·(-i) = 1` (no `i² = -1` needed for the cast step).
  rw [show Complex.I * t * Complex.exp (-(t : ℂ) ^ 2 / 2) * ((Real.sqrt (2 * π) : ℝ) : ℂ)
        = -Complex.I * (-(t : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2)
          * ((Real.sqrt (2 * π) : ℝ) : ℂ)) from by ring]
  rw [← heq, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  EIGENFUNCTION FORM AND CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Eigenfunction form.**  Writing ψ₁(x) = x·e^{-x²/2} for the first Hermite
    function, the Fourier transform carries ψ₁ to `(i·√(2π))·ψ₁`:

      ∫ e^{i t x} ψ₁(x) dx = (i·√(2π)) · ψ₁(t).

    So ψ₁ is a Fourier eigenfunction with eigenvalue `i·√(2π)` (eigenvalue `i`
    after unitary normalization), the first excited state above the Gaussian. -/
theorem first_hermite_fourier_eigenfunction (t : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * t * x) * ((x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2)))
      = (Complex.I * ((Real.sqrt (2 * π) : ℝ) : ℂ)) * ((t : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2)) := by
  rw [show (fun x : ℝ => Complex.exp (Complex.I * t * x) * ((x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2)))
        = (fun x : ℝ => (x : ℂ) * Complex.exp (Complex.I * t * x) * Complex.exp (-(x : ℂ) ^ 2 / 2))
      from by funext x; ring]
  rw [gaussian_fourier_first_hermite]
  ring

/-- **Odd-integrand sanity check (`t = 0`).**  The first moment of the Gaussian
    vanishes: ∫ x·e^{-x²/2} dx = 0. -/
theorem first_moment_gaussian_zero :
    (∫ x : ℝ, (x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2)) = 0 := by
  have h := gaussian_fourier_first_hermite 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one] at h
  simpa using h

/-- **Normalized eigenvalue.**  Dividing by `√(2π)`, the normalized first Hermite
    function `x·e^{-x²/2}/√(2π)` has Fourier eigenvalue exactly `i`:

      ∫ e^{i t x} · (x·e^{-x²/2}/√(2π)) dx = i · (t·e^{-t²/2}). -/
theorem first_hermite_fourier_normalized (t : ℝ) :
    (∫ x : ℝ, Complex.exp (Complex.I * t * x)
        * ((x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ)))
      = Complex.I * ((t : ℂ) * Complex.exp (-(t : ℂ) ^ 2 / 2)) := by
  have hC : ((Real.sqrt (2 * π) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [show (fun x : ℝ => Complex.exp (Complex.I * t * x)
        * ((x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2) / ((Real.sqrt (2 * π) : ℝ) : ℂ)))
      = (fun x : ℝ => (Complex.exp (Complex.I * t * x)
        * ((x : ℂ) * Complex.exp (-(x : ℂ) ^ 2 / 2))) / ((Real.sqrt (2 * π) : ℝ) : ℂ))
      from by funext x; ring]
  rw [MeasureTheory.integral_div, first_hermite_fourier_eigenfunction]
  field_simp

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## The first Hermite function is a Fourier eigenfunction  (oq-05-oq-03-oq-05)

### What's proved (0 sorries, 0 axioms):
- `gaussian_fourier_real`: the parent identity ∫ e^{itx} e^{-x²/2} = e^{-t²/2}√(2π),
  reproved self-contained.
- `gaussian_fourier_first_hermite`: **∫ e^{itx}·x·e^{-x²/2} dx = i·t·e^{-t²/2}·√(2π)** —
  the Fourier transform of the first Hermite function ψ₁(x) = x·e^{-x²/2},
  obtained by differentiating the parent identity under the integral sign.
- `first_hermite_fourier_eigenfunction`: the eigenfunction form
  ∫ e^{itx} ψ₁(x) dx = (i·√(2π))·ψ₁(t) — ψ₁ is a Fourier eigenfunction with
  eigenvalue i·√(2π) (eigenvalue i normalized), the first excited state.
- `first_hermite_fourier_normalized`: the unitary-normalized eigenvalue is exactly i.
- `first_moment_gaussian_zero`: the t = 0 shadow ∫ x·e^{-x²/2} dx = 0.

### Relation to the parent:
The parent shows the Gaussian (ground state) has Fourier eigenvalue 1 = i⁰; this
child shows the first Hermite function (first excited state) has eigenvalue i = i¹,
exhibiting the next rung of the Fourier eigenvalue ladder iⁿ.
-/

#check @gaussian_fourier_first_hermite
#check @first_hermite_fourier_eigenfunction
#check @first_hermite_fourier_normalized
#check @first_moment_gaussian_zero

end GaussianHermiteFourier
