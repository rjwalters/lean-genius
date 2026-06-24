/-
# Gamma Reflection OQ-01-OQ-01: The Beta value `B(1/2, 1/2) = π`

**Open Question (parent `GammaReflectionFormulaOQ01`, openQuestions[0]).** The parent
entry establishes Euler's reflection formula and the special value `Γ(1/2)² = π`. This
file feeds that value through the **Beta–Gamma relation**
`B(x, y) = Γ(x)·Γ(y) / Γ(x + y)` to evaluate

> `B(1/2, 1/2) = Γ(1/2)² / Γ(1) = π`,

and identifies this `π` with the **total mass of the (unnormalized) arcsine density**
`1/√(t(1−t))` on `[0, 1]`:

> `∫₀¹ dt / √(t(1−t)) = π`.

## What is new

Mathlib has the Beta integral `Complex.betaIntegral` and the Beta–Gamma identity
`Complex.Gamma_mul_Gamma_eq_betaIntegral`, but it does **not** evaluate `B(1/2, 1/2)`,
nor does it record the closed form `∫₀¹ dt/√(t(1−t)) = π`. Both are derived here. The
arcsine-density reading turns the reflection-formula constant `π` into a concrete
probability normalization (the arcsine law on `[0,1]` has density `1/(π√(t(1−t)))`).

## Method

`Complex.Gamma_mul_Gamma_eq_betaIntegral` gives `Γ(1/2)·Γ(1/2) = Γ(1)·B(1/2,1/2)`.
With `Γ(1) = 1` (`Complex.Gamma_one`) and `Γ(1/2) = π^(1/2)`
(`Complex.Gamma_one_half_eq`), the left side is `π^(1/2)·π^(1/2) = π^(1/2+1/2) = π`,
so `B(1/2,1/2) = π`. Unfolding `betaIntegral` and casting the complex integrand
`x^(-1/2)·(1−x)^(-1/2)` to the real `1/√(x(1−x))` throughout `[0,1]` (via
`Complex.ofReal_cpow`) turns this into the real arcsine integral, then
`intervalIntegral.integral_ofReal` transports the value `π` back to `ℝ`.

## References

* Mathlib: `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`,
  `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`.
* Whittaker & Watson, *A Course of Modern Analysis*, §12.4 (the Beta function).
-/
import Mathlib

namespace GammaReflectionFormulaOQ01OQ01

open scoped Real

/-! ## The Beta value at the symmetric point -/

/-- **The Beta value `B(1/2,1/2) = π`** (Mathlib's complex Beta integral).
From the Beta–Gamma relation `Γ(1/2)·Γ(1/2) = Γ(1)·B(1/2,1/2)`, with `Γ(1) = 1` and
`Γ(1/2) = π^(1/2)`, the product is `π^(1/2)·π^(1/2) = π^(1/2+1/2) = π`. -/
theorem betaIntegral_half_half :
    Complex.betaIntegral (1 / 2) (1 / 2) = (π : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (1 / 2 : ℂ)) (t := (1 / 2 : ℂ)) (by norm_num) (by norm_num)
  rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Complex.Gamma_one, one_mul] at h
  rw [Complex.Gamma_one_half_eq] at h
  have h0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← h, ← Complex.cpow_add _ _ h0, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    Complex.cpow_one]

/-- **The Beta value as a ratio of Gamma values**, over the real Gamma function:
`B(1/2,1/2) = Γ(1/2)·Γ(1/2) / Γ(1) = π`. This is the textbook form of the Beta–Gamma
relation specialized at `(1/2, 1/2)`, recovering the parent's `Γ(1/2)² = π`. -/
theorem beta_half_half_gamma_ratio :
    Real.Gamma (1 / 2) * Real.Gamma (1 / 2) / Real.Gamma 1 = π := by
  rw [Real.Gamma_one, div_one, ← pow_two, Real.Gamma_one_half_eq,
    Real.sq_sqrt Real.pi_pos.le]

/-! ## The arcsine total mass

We now read `B(1/2,1/2) = π` as a statement about a real integral. The complex Beta
integrand at `(1/2,1/2)` is `x^(1/2-1)·(1-x)^(1/2-1)`; on `[0,1]` this is the cast of
the real arcsine kernel `1/√(x(1-x))` (both sides vanish at the endpoints, where the
`x^(-1/2)` / `(1-x)^(-1/2)` powers are read as `0`). -/

/-- Pointwise identification of the complex Beta integrand at `(1/2, 1/2)` with the
real arcsine kernel, valid throughout `[0,1]`. -/
theorem beta_integrand_eq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (x : ℂ) ^ ((1 / 2 : ℂ) - 1) * (1 - (x : ℂ)) ^ ((1 / 2 : ℂ) - 1)
      = ((1 / Real.sqrt (x * (1 - x)) : ℝ) : ℂ) := by
  have h1x : 0 ≤ 1 - x := by linarith
  rw [show (1 / 2 : ℂ) - 1 = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hx0, ← Complex.ofReal_cpow h1x, ← Complex.ofReal_mul]
  norm_cast
  -- reals: `x^(-(1/2)) * (1-x)^(-(1/2)) = 1 / √(x(1-x))`
  rw [Real.sqrt_mul hx0, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.rpow_neg hx0, Real.rpow_neg h1x]
  ring

/-- **Total mass of the arcsine kernel:** `∫₀¹ dx / √(x(1-x)) = π`.

Transport of `betaIntegral_half_half` along `intervalIntegral.integral_ofReal`: the
complex Beta integral `B(1/2,1/2)` is literally the interval integral of the real
arcsine kernel cast to `ℂ`, so its value `π` is real and equals `∫₀¹ 1/√(x(1-x))`. -/
theorem arcsine_total_mass :
    ∫ x in (0 : ℝ)..1, 1 / Real.sqrt (x * (1 - x)) = π := by
  have key : Complex.betaIntegral (1 / 2) (1 / 2)
      = ∫ x in (0 : ℝ)..1, ((1 / Real.sqrt (x * (1 - x)) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    exact beta_integrand_eq hx.1 hx.2
  rw [intervalIntegral.integral_ofReal, betaIntegral_half_half] at key
  exact_mod_cast key.symm

/-- **The arcsine law is a probability distribution:** its density `1/(π√(x(1-x)))`
has total mass `1` over `[0,1]`. Immediate from `arcsine_total_mass` by factoring out
the normalising `1/π`. -/
theorem arcsine_density_total_mass :
    ∫ x in (0 : ℝ)..1, 1 / (π * Real.sqrt (x * (1 - x))) = 1 := by
  have h : ∀ x : ℝ, 1 / (π * Real.sqrt (x * (1 - x)))
      = π⁻¹ * (1 / Real.sqrt (x * (1 - x))) := by
    intro x; rw [mul_comm π, ← div_div]; ring
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, arcsine_total_mass,
    inv_mul_cancel₀ Real.pi_ne_zero]

end GammaReflectionFormulaOQ01OQ01
