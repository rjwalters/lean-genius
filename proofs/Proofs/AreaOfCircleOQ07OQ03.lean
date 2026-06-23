import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# `Γ(1/2) = √π`: the Gamma-function shadow of the Gaussian integral

## Open Question (area-of-circle-oq-07-oq-03)
Formalize the special-value identity `Real.Gamma (1/2) = √π` — the Gamma-function
shadow of the parent entry `area-of-circle-oq-07`, whose theorem states
`∫_ℝ e^{-x²} dx = √π`.

## Answer: YES — and the two are literally the same number.

The Euler Gamma function `Γ(s) = ∫₀^∞ u^{s-1} e^{-u} du` at `s = 1/2` becomes
`∫₀^∞ u^{-1/2} e^{-u} du`.  The substitution `u = x²` (so `du = 2x dx`,
`u^{-1/2} = x⁻¹`) turns this into `2 ∫₀^∞ e^{-x²} dx`, which by even symmetry is
`∫_ℝ e^{-x²} dx = √π`.  Mathlib packages this substitution inside the proof of
`Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π`.

This file records the identity together with two bridges that exhibit `Γ(1/2)`
explicitly as a Gaussian value:

* `gamma_one_half_eq_sqrt_pi`     — `Γ(1/2) = √π`;
* `gamma_one_half_eq_gaussian`    — `Γ(1/2) = ∫_ℝ e^{-x²}`, identifying `Γ(1/2)`
  with the full-line Gaussian integral of the parent entry;
* `gamma_one_half_eq_two_mul_gaussian_Ioi` — `Γ(1/2) = 2 · ∫_{x>0} e^{-x²}`,
  the half-line form that is the direct image of the `u = x²` substitution.

No new axioms: every step is a routine consequence of existing Mathlib results
(`Real.Gamma_one_half_eq`, `integral_gaussian_Ioi`).
-/

open Real MeasureTheory

/-- **`Γ(1/2) = √π`.** The Euler Gamma function at `1/2` evaluates to `√π`. -/
theorem gamma_one_half_eq_sqrt_pi : Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
  Real.Gamma_one_half_eq

/-- **Bridge to the parent Gaussian integral.** `Γ(1/2)` equals the full-line
Gaussian integral `∫_ℝ e^{-x²}`, the quantity proved equal to `√π` in
`area-of-circle-oq-07`. -/
theorem gamma_one_half_eq_gaussian :
    Real.Gamma (1 / 2) = ∫ x : ℝ, Real.exp (-x ^ 2) := by
  rw [Real.Gamma_one_half_eq]
  have h := integral_gaussian 1
  simp only [neg_one_mul, div_one] at h
  exact h.symm

/-- **Half-line form.** `Γ(1/2) = 2 · ∫_{x>0} e^{-x²}`, the direct image of the
substitution `u = x²` in `Γ(1/2) = ∫₀^∞ u^{-1/2} e^{-u} du`. -/
theorem gamma_one_half_eq_two_mul_gaussian_Ioi :
    Real.Gamma (1 / 2) = 2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2) := by
  rw [Real.Gamma_one_half_eq]
  have h := integral_gaussian_Ioi 1
  simp only [neg_one_mul, div_one] at h
  rw [h]
  ring

/-- **The squared half-value `Γ(1/2)² = π`.** The Gamma-function counterpart of
the parent entry's squared Gaussian identity `(∫_ℝ e^{-x²})² = π`. -/
theorem gamma_one_half_sq : Real.Gamma (1 / 2) ^ 2 = Real.pi := by
  rw [gamma_one_half_eq_sqrt_pi, Real.sq_sqrt Real.pi_pos.le]
