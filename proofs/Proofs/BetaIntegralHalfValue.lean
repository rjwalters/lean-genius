import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The Beta Function at Half-Integer Arguments: `B(1/2, 1/2) = π`

## What This Proves

The Euler Beta integral `B(u, v) = ∫₀¹ t^(u-1) (1-t)^(v-1) dt` has the famous
half-integer special value

  **`betaIntegral_half_half`**:  `B(1/2, 1/2) = π`.

This is the area capstone to the parent entry's integer closed form
`B(m+1, n+1) = m!·n!/(m+n+1)!`: while the integer lattice is governed entirely
by factorials, the half-integer lattice brings in `π` through the Gauss value
`Γ(1/2) = √π`. Geometrically, `B(1/2,1/2) = ∫₀¹ dt/√(t(1-t)) = π` is the length
of the substitution `t = sin²θ` sweeping `[0, π/2]` twice.

We also push one step up the Beta recurrence to the next half-integer value

  **`betaIntegral_three_half_three_half`**:  `B(3/2, 3/2) = π/8`,

obtained from `Γ(3/2) = ½·Γ(1/2)` (the functional equation `Γ(s+1) = s·Γ(s)`)
and `Γ(3) = 2! = 2`.

## Relation to Mathlib

Mathlib provides the Beta–Gamma division formula
`Complex.betaIntegral_eq_Gamma_mul_div`, the Gauss value
`Complex.Gamma_one_half_eq : Γ(1/2) = π^(1/2)`, the functional equation
`Complex.Gamma_add_one`, and `Complex.Gamma_nat_eq_factorial`. It does **not**
state the half-integer Beta values `B(1/2,1/2) = π` or `B(3/2,3/2) = π/8`; we
assemble them here from those ingredients.

## Approach

`betaIntegral_half_half`: apply `betaIntegral_eq_Gamma_mul_div` (both real parts
are `1/2 > 0`), rewrite `1/2 + 1/2 = 1`, collapse `Γ(1) = 1`, substitute
`Γ(1/2) = π^(1/2)`, and recombine `π^(1/2) · π^(1/2) = π^(1/2 + 1/2) = π` via
`cpow_add` (base `(π : ℂ) ≠ 0`) and `cpow_one`.

`betaIntegral_three_half_three_half`: same Beta–Gamma split, then
`Γ(3/2) = ½·Γ(1/2)` from `Gamma_add_one` and `Γ(3) = 2` from
`Gamma_nat_eq_factorial`, finishing with `field_simp`/`ring` and the same
`π^(1/2)` recombination.
-/

namespace BetaIntegralHalfValue

open Complex

/-- `(π : ℂ) ≠ 0`, the base nonvanishing needed to recombine `cpow` powers. -/
private lemma piC_ne_zero : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

/-- The square of the Gauss value: `π^(1/2) · π^(1/2) = π`. -/
private lemma piC_half_sq :
    (Real.pi : ℂ) ^ (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.pi : ℂ) := by
  rw [← Complex.cpow_add _ _ piC_ne_zero, show (1 / 2 : ℂ) + 1 / 2 = 1 by ring,
    Complex.cpow_one]

/-- **`Γ(1/2) · Γ(1/2) = π`** — the squared Gauss value, recorded separately as
the analytic heart of the half-integer Beta value. -/
theorem gamma_half_sq : Gamma (1 / 2) * Gamma (1 / 2) = (Real.pi : ℂ) := by
  rw [Gamma_one_half_eq, piC_half_sq]

/-- **`B(1/2, 1/2) = π` (new).** The headline half-integer value of the Euler
Beta function. -/
theorem betaIntegral_half_half : betaIntegral (1 / 2) (1 / 2) = (Real.pi : ℂ) := by
  have hre : (0 : ℝ) < ((1 / 2 : ℂ)).re := by norm_num
  rw [betaIntegral_eq_Gamma_mul_div _ _ hre hre,
    show (1 / 2 : ℂ) + 1 / 2 = 1 by ring, Gamma_one, div_one, gamma_half_sq]

/-- `Γ(3/2) = ½ · Γ(1/2)`, the single recurrence step from the Gauss value. -/
private lemma gamma_three_half : Gamma (3 / 2) = (1 / 2 : ℂ) * Gamma (1 / 2) := by
  have h : Gamma ((1 / 2 : ℂ) + 1) = (1 / 2 : ℂ) * Gamma (1 / 2) :=
    Gamma_add_one _ (by norm_num)
  rwa [show (1 / 2 : ℂ) + 1 = 3 / 2 by ring] at h

/-- **`B(3/2, 3/2) = π/8` (new).** The next half-integer Beta value, reached by
one step of the Beta/Gamma recurrence above the headline value. -/
theorem betaIntegral_three_half_three_half :
    betaIntegral (3 / 2) (3 / 2) = (Real.pi : ℂ) / 8 := by
  have hre : (0 : ℝ) < ((3 / 2 : ℂ)).re := by norm_num
  have hsum : (3 / 2 : ℂ) + 3 / 2 = ((2 : ℕ) : ℂ) + 1 := by norm_num
  rw [betaIntegral_eq_Gamma_mul_div _ _ hre hre, hsum, Gamma_nat_eq_factorial,
    gamma_three_half, Gamma_one_half_eq]
  -- goal: (1/2 · π^(1/2)) · (1/2 · π^(1/2)) / (2! : ℂ) = π / 8
  have hpow := piC_half_sq
  rw [show ((Nat.factorial 2 : ℂ)) = 2 by norm_num [Nat.factorial]]
  rw [show (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ) *
      ((1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ))
      = (1 / 4 : ℂ) * ((Real.pi : ℂ) ^ (1 / 2 : ℂ) * (Real.pi : ℂ) ^ (1 / 2 : ℂ)) by ring,
    hpow]
  ring

end BetaIntegralHalfValue
