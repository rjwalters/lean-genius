import Mathlib

/-!
# Euler's reflection formula and its special-value products

Euler's reflection formula states that for all real (and complex) `s`,
`Γ(s) · Γ(1 - s) = π / sin(π s)`.

The core identity is Mathlib's `Real.Gamma_mul_Gamma_one_sub` /
`Complex.Gamma_mul_Gamma_one_sub`; this file re-exports it under a stable name and
then derives the genuine new content absent from Mathlib:

* the **concrete special-value products** obtained by feeding rational arguments into
  the reflection formula and evaluating `sin` at the corresponding special angles —
  `Γ(1/2)² = π`, `Γ(1/4)·Γ(3/4) = π√2`, `Γ(1/3)·Γ(2/3) = 2π/√3`,
  `Γ(1/6)·Γ(5/6) = 2π`. Reflection evaluates these products exactly even though the
  individual values `Γ(1/4)`, `Γ(1/3)`, … are not elementary.
* the **non-vanishing corollary**: whenever `sin(π s) ≠ 0` (in particular when `s` is
  not an integer), `Γ s ≠ 0`, read off directly from the reflection identity.

All results are fully machine-checked. The headline reflection identity is delegated
to Mathlib (hence the `mathlib` badge); the special-value products and the
sin-based non-vanishing argument are derived here.
-/

namespace GammaReflectionFormulaOQ01

open Real

/-! ## The reflection formula (re-exported) -/

/-- **Euler's reflection formula** for the real Gamma function:
`Γ(s) · Γ(1 - s) = π / sin(π s)`. -/
theorem gamma_reflection (s : ℝ) :
    Gamma s * Gamma (1 - s) = π / sin (π * s) :=
  Real.Gamma_mul_Gamma_one_sub s

/-- **Euler's reflection formula** for the complex Gamma function. -/
theorem gamma_reflection_complex (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (1 - z) = (π : ℂ) / Complex.sin ((π : ℂ) * z) :=
  Complex.Gamma_mul_Gamma_one_sub z

/-! ## Concrete special-value products

These are obtained by specializing the reflection formula at rational `s` and
evaluating `sin` at the resulting special angle. None of these product evaluations
are in Mathlib. -/

/-- `Γ(1/2)² = π`, recovered from reflection at `s = 1/2` (where `sin(π/2) = 1`).
This is the squared form of `Γ(1/2) = √π`, here obtained purely from the reflection
identity without the Gaussian integral. -/
theorem gamma_half_sq : Gamma (1 / 2) ^ 2 = π := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 2)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, show π * (1 / 2) = π / 2 by ring,
    Real.sin_pi_div_two] at h
  rw [pow_two, h, div_one]

/-- `Γ(1/4) · Γ(3/4) = π√2`, from reflection at `s = 1/4` (where `sin(π/4) = √2/2`). -/
theorem gamma_quarter_mul : Gamma (1 / 4) * Gamma (3 / 4) = π * Real.sqrt 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 4)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, show π * (1 / 4) = π / 4 by ring,
    Real.sin_pi_div_four] at h
  rw [h, div_div_eq_mul_div, div_eq_iff (show Real.sqrt 2 ≠ 0 by positivity),
    mul_assoc, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- `Γ(1/3) · Γ(2/3) = 2π/√3`, from reflection at `s = 1/3` (where `sin(π/3) = √3/2`). -/
theorem gamma_third_mul : Gamma (1 / 3) * Gamma (2 / 3) = 2 * π / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 : ℝ) - 1 / 3 = 2 / 3 by norm_num, show π * (1 / 3) = π / 3 by ring,
    Real.sin_pi_div_three] at h
  rw [h, div_div_eq_mul_div]
  ring

/-- `Γ(1/6) · Γ(5/6) = 2π`, from reflection at `s = 1/6` (where `sin(π/6) = 1/2`). -/
theorem gamma_sixth_mul : Gamma (1 / 6) * Gamma (5 / 6) = 2 * π := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 6)
  rw [show (1 : ℝ) - 1 / 6 = 5 / 6 by norm_num, show π * (1 / 6) = π / 6 by ring,
    Real.sin_pi_div_six] at h
  rw [h]
  ring

/-! ## Non-vanishing via reflection -/

/-- If `sin(π s) ≠ 0` then `Γ s ≠ 0`: the reflection identity forces the product
`Γ(s) · Γ(1 - s)` to equal the nonzero quantity `π / sin(π s)`, so neither factor can
vanish. -/
theorem gamma_ne_zero_of_sin_ne_zero {s : ℝ} (hs : sin (π * s) ≠ 0) :
    Gamma s ≠ 0 := by
  intro hz
  have h := Real.Gamma_mul_Gamma_one_sub s
  rw [hz, zero_mul] at h
  exact div_ne_zero pi_ne_zero hs h.symm

/-- The Gamma function does not vanish at any non-integer real argument, derived from
reflection: a non-integer argument makes `sin(π s) ≠ 0`. -/
theorem gamma_ne_zero_of_not_int {s : ℝ} (hs : ∀ n : ℤ, (n : ℝ) ≠ s) :
    Gamma s ≠ 0 := by
  apply gamma_ne_zero_of_sin_ne_zero
  intro hsin
  rw [Real.sin_eq_zero_iff] at hsin
  obtain ⟨n, hn⟩ := hsin
  -- `hn : (n : ℝ) * π = π * s`
  apply hs n
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  have h2 : (n : ℝ) * π = s * π := by linear_combination hn
  exact mul_right_cancel₀ hpi h2

end GammaReflectionFormulaOQ01
