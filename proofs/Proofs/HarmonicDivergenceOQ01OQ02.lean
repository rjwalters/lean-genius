/-
# The Euler-Mascheroni Constant as a Gamma-Function Derivative

## What This Proves

This entry discharges the second open question of the parent Euler-Mascheroni
entry (`harmonic-divergence-oq-01`): *formalize the connection γ = -Γ'(1).*

The parent documented this connection only as comments, believing the required
Gamma-derivative infrastructure (`Mathlib.NumberTheory.Harmonic.GammaDeriv`) was
too costly to import. In fact the Mathlib oleans are precompiled, so the import
is cheap, and we obtain a fully machine-verified account:

1. γ = -Γ'(1), equivalently `HasDerivAt Γ (-γ) 1`.
2. The general integer formula Γ'(n+1) = n!·(-γ + H_n).
3. Concrete values: Γ'(1) = -γ, Γ'(2) = 1 - γ, Γ'(3) = 3 - 2γ.
4. Sign analysis: Γ'(1) < 0 < Γ'(2), so the (well-known) minimum of Γ on the
   positive reals lies strictly between 1 and 2.
5. Sharp enclosure of the derivative from the parent's bounds 1/2 < γ < 2/3:
   -2/3 < Γ'(1) < -1/2.
6. The half-integer derivative Γ'(1/2) = -√π(γ + 2 log 2) and its sign.

Every result delegates to Mathlib's `GammaDeriv` file plus the bounds
1/2 < γ < 2/3, so the entry is 0-axiom and sorry-free.

Tags: analysis, number-theory, euler-mascheroni, gamma-function,
      digamma, special-functions
-/

import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace EulerMascheroniGammaDeriv

open Real Filter

/-- The Euler-Mascheroni constant γ. -/
noncomputable def γ : ℝ := Real.eulerMascheroniConstant

/-! ## The defining connection γ = -Γ'(1) -/

/-- The Euler-Mascheroni constant is minus the derivative of Γ at 1. This is the
central identity requested by the parent entry's open question. -/
theorem gamma_eq_neg_deriv_Gamma_one : γ = -deriv Gamma 1 :=
  Real.eulerMascheroniConstant_eq_neg_deriv

/-- Equivalent formulation: Γ has derivative -γ at 1. -/
theorem hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 :=
  Real.hasDerivAt_Gamma_one

/-- The derivative of Γ at 1 equals -γ. -/
theorem deriv_Gamma_one : deriv Gamma 1 = -γ :=
  hasDerivAt_Gamma_one.deriv

/-! ## The general integer formula Γ'(n+1) = n!·(-γ + H_n) -/

/-- Explicit derivative of Γ at every positive integer, in terms of the harmonic
numbers and γ. -/
theorem deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = (Nat.factorial n : ℝ) * (-γ + harmonic n) :=
  Real.deriv_Gamma_nat n

/-- The same formula packaged as a `HasDerivAt` statement. -/
theorem hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma ((Nat.factorial n : ℝ) * (-γ + harmonic n)) (n + 1) :=
  Real.hasDerivAt_Gamma_nat n

/-! ## Concrete values of Γ' at small integers -/

/-- Γ'(2) = 1 - γ. -/
theorem deriv_Gamma_two : deriv Gamma 2 = 1 - γ := by
  have h := deriv_Gamma_nat 1
  have hh : (harmonic 1 : ℝ) = 1 := by
    norm_num [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hh] at h
  norm_num [Nat.factorial] at h
  linarith [h]

/-- Γ'(3) = 3 - 2γ. -/
theorem deriv_Gamma_three : deriv Gamma 3 = 3 - 2 * γ := by
  have h := deriv_Gamma_nat 2
  have hh : (harmonic 2 : ℝ) = 3 / 2 := by
    norm_num [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hh] at h
  norm_num [Nat.factorial] at h
  linarith [h]

/-! ## Sign analysis and the minimum of Γ

Positivity of γ gives Γ'(1) < 0, while γ < 1 gives Γ'(2) > 0. Since Γ is
smooth on (0, ∞), the sign change forces the minimum of Γ to lie strictly
between 1 and 2 (numerically near 1.4616). -/

/-- Γ'(1) < 0. -/
theorem deriv_Gamma_one_neg : deriv Gamma 1 < 0 := by
  rw [deriv_Gamma_one]
  have : (0 : ℝ) < γ := by
    have := Real.one_half_lt_eulerMascheroniConstant
    simp only [γ]; linarith
  linarith

/-- Γ'(2) > 0. -/
theorem deriv_Gamma_two_pos : 0 < deriv Gamma 2 := by
  rw [deriv_Gamma_two]
  have : γ < 2 / 3 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds
    simp only [γ]; linarith
  linarith

/-- The derivative of Γ changes sign between 1 and 2: Γ'(1) < 0 < Γ'(2). This
is the analytic signature of the unique minimum of Γ on the positive reals. -/
theorem deriv_Gamma_sign_change : deriv Gamma 1 < 0 ∧ 0 < deriv Gamma 2 :=
  ⟨deriv_Gamma_one_neg, deriv_Gamma_two_pos⟩

/-! ## Sharp enclosure of Γ'(1) from the parent bounds 1/2 < γ < 2/3 -/

/-- Lower and upper bounds on the derivative of Γ at 1, transferred from the
parent entry's enclosure 1/2 < γ < 2/3. -/
theorem deriv_Gamma_one_bounds : -2 / 3 < deriv Gamma 1 ∧ deriv Gamma 1 < -1 / 2 := by
  rw [deriv_Gamma_one]
  have h1 : (1 : ℝ) / 2 < γ := by
    have := Real.one_half_lt_eulerMascheroniConstant; simp only [γ]; linarith
  have h2 : γ < 2 / 3 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; simp only [γ]; linarith
  constructor <;> linarith

/-! ## The half-integer derivative Γ'(1/2) -/

/-- Γ'(1/2) = -√π·(γ + 2 log 2). -/
theorem hasDerivAt_Gamma_one_half :
    HasDerivAt Gamma (-√π * (γ + 2 * Real.log 2)) (1 / 2) :=
  Real.hasDerivAt_Gamma_one_half

/-- The derivative of Γ at 1/2 equals -√π·(γ + 2 log 2). -/
theorem deriv_Gamma_one_half :
    deriv Gamma (1 / 2) = -√π * (γ + 2 * Real.log 2) :=
  hasDerivAt_Gamma_one_half.deriv

/-- Γ'(1/2) < 0: the derivative is negative at the half-integer too. -/
theorem deriv_Gamma_one_half_neg : deriv Gamma (1 / 2) < 0 := by
  rw [deriv_Gamma_one_half]
  have hγ : (0 : ℝ) < γ := by
    have := Real.one_half_lt_eulerMascheroniConstant; simp only [γ]; linarith
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsum : (0 : ℝ) < γ + 2 * Real.log 2 := by linarith
  nlinarith [mul_pos hpi hsum]

end EulerMascheroniGammaDeriv
