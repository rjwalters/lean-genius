/-
# Gamma Reflection OQ-01-OQ-01-OQ-01: The general symmetric Beta value `B(s, 1-s) = π/sin(πs)`

**Open Question (parent `GammaReflectionFormulaOQ01OQ01`, openQuestions[0]).** The parent
entry evaluates the single symmetric Beta value `B(1/2, 1/2) = π`. This file proves the
**general** symmetric reflection identity

> `B(s, 1-s) = π / sin(π s)`   (for `0 < Re s < 1`),

by combining the **Beta–Gamma relation** `Γ(s)·Γ(t) = Γ(s+t)·B(s,t)` with **Euler's
reflection formula** `Γ(s)·Γ(1-s) = π / sin(π s)`. At `s + (1-s) = 1` the denominator
collapses to `Γ(1) = 1`, so the Beta integral equals the reflection constant directly.

The parent's special value `B(1/2, 1/2) = π` is recovered as the case `s = 1/2`
(`sin(π/2) = 1`), and a second concrete value `Γ(1/3)·Γ(2/3) = 2π/√3`
(`sin(π/3) = √3/2`) illustrates that the formula genuinely depends on `s`.

## What is new

Mathlib has the Beta integral `Complex.betaIntegral`, the Beta–Gamma identity
`Complex.Gamma_mul_Gamma_eq_betaIntegral`, and Euler's reflection formula
`Complex.Gamma_mul_Gamma_one_sub` / `Real.Gamma_mul_Gamma_one_sub`, but it does **not**
evaluate the symmetric Beta integral `B(s, 1-s)` in closed form. That closed form is
derived here as a single clean reflection statement, with the parent's `π` recovered as
one specialization and `2π/√3` as another.

## Method

`Complex.Gamma_mul_Gamma_eq_betaIntegral` gives `Γ(s)·Γ(1-s) = Γ(1)·B(s, 1-s)`. With
`Γ(1) = 1` the right side is just `B(s, 1-s)`; with the reflection formula the left side
is `π / sin(π s)`. Equate. The real-Gamma ratio form and the concrete values follow by
specialization and the standard sine values `sin(π/2)`, `sin(π/3)`.

## References

* Mathlib: `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`
  (`Gamma_mul_Gamma_eq_betaIntegral`, `Gamma_mul_Gamma_one_sub`).
* Whittaker & Watson, *A Course of Modern Analysis*, §12.14 (the Beta function and the
  reflection formula).
-/
import Mathlib

namespace GammaReflectionFormulaOQ01OQ01OQ01

open scoped Real

/-! ## The general symmetric Beta value -/

/-- **The symmetric Beta value `B(s, 1-s) = π / sin(π s)`** for `0 < Re s < 1`.

From the Beta–Gamma relation `Γ(s)·Γ(1-s) = Γ(s + (1-s))·B(s, 1-s)`, the argument
`s + (1-s) = 1` gives `Γ(1) = 1`, so the right side is `B(s, 1-s)`. Euler's reflection
formula rewrites the left side as `π / sin(π s)`. -/
theorem betaIntegral_one_sub_eq {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.betaIntegral s (1 - s) = (π : ℂ) / Complex.sin (π * s) := by
  have ht : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral hs0 ht
  rw [show s + (1 - s) = 1 by ring, Complex.Gamma_one, one_mul] at h
  rw [Complex.Gamma_mul_Gamma_one_sub] at h
  exact h.symm

/-- **Recovering the parent value `B(1/2, 1/2) = π`** from the general formula at
`s = 1/2`, where `sin(π · (1/2)) = sin(π/2) = 1`. -/
theorem betaIntegral_half_half :
    Complex.betaIntegral (1 / 2) (1 / 2) = (π : ℂ) := by
  have h := betaIntegral_one_sub_eq (s := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  rw [show (1 - 1 / 2 : ℂ) = 1 / 2 by norm_num] at h
  rw [h, show ((π : ℂ) * (1 / 2)) = ((π / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, Real.sin_pi_div_two]
  norm_num

/-! ## Real-Gamma ratio form and a second concrete value -/

/-- **The Beta–Gamma reflection identity over the real Gamma function:**
`Γ(s)·Γ(1-s) / Γ(1) = π / sin(π s)`. This is the textbook ratio form `B(s,1-s) =
Γ(s)Γ(1-s)/Γ(1)`, evaluated by Euler's reflection formula. -/
theorem beta_gamma_ratio_reflection (s : ℝ) :
    Real.Gamma s * Real.Gamma (1 - s) / Real.Gamma 1 = π / Real.sin (π * s) := by
  rw [Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub]

/-- **A second concrete symmetric value:** `Γ(1/3)·Γ(2/3) = 2π/√3`.

Euler's reflection formula at `s = 1/3` gives `π / sin(π/3)`, and `sin(π/3) = √3/2`,
so the value is `π / (√3/2) = 2π/√3`. Unlike the symmetric midpoint `s = 1/2`, here the
sine denominator is genuinely nontrivial. -/
theorem gamma_one_third_mul_two_thirds :
    Real.Gamma (1 / 3) * Real.Gamma (2 / 3) = 2 * π / Real.sqrt 3 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 3)
  rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at h
  rw [h, show ((π : ℝ) * (1 / 3)) = π / 3 by ring, Real.sin_pi_div_three,
    div_div_eq_mul_div]
  ring

end GammaReflectionFormulaOQ01OQ01OQ01
