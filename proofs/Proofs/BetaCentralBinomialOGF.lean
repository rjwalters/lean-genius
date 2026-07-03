import Proofs.BetaCentralBinomial
import Mathlib.Tactic

/-
# The Central Beta Sequence and its Ordinary Generating Function

## What This Proves

The parent entries establish the integer closed form of the Euler Beta integral
`B(m+1,n+1) = m!·n!/(m+n+1)!` (`betaIntegral_nat_nat`) and its **diagonal**
value as a central-binomial reciprocal
`B(n+1,n+1) = 1/((2n+1)·C(2n,n))` (`betaIntegral_diag_central_binom`).

This file studies the *diagonal sequence itself*,

  `b(n) := B(n+1,n+1) = (n!)² / (2n+1)! = 1 / ((2n+1)·C(2n,n))`,

as the coefficient sequence of a power series, and pins down its arithmetic
structure — the data that determines its ordinary generating function.

The headline result is the **two-term contiguous recurrence**

  **`centralBeta_recurrence`**:  `(4n+6) · b(n+1) = (n+1) · b(n)`.

Together with the initial value `b(0) = 1` (`centralBeta_zero`) this recurrence
*characterizes* the sequence, and hence its generating function
`y(x) = Σₙ b(n) xⁿ`: translating the recurrence coefficient-by-coefficient shows
`y` solves the first-order linear ODE `x(4-x) y'(x) + (2-x) y(x) = 2`,
`y(0) = 1`, whose closed-form solution is

  `Σₙ b(n) xⁿ = 4·arcsin(√x / 2) / √(x(4-x))`   (0 < x < 4),

the classical reciprocal-central-binomial generating function (value `π/2` at
`x = 2`). The analytic identity — interchanging the sum with the Beta integral
`b(n) = ∫₀¹ (t(1-t))ⁿ dt` and evaluating `∫₀¹ dt/(1 - x t(1-t))` — is recorded
here as the stated sequel; this file supplies the *verified arithmetic backbone*
(reciprocal form, gallery link, recurrence, base values) on which that analytic
proof rests.

## Relation to Mathlib

Mathlib provides `Nat.centralBinom`, `Nat.choose_mul_factorial_mul_factorial`,
and `Real.arcsin`, but states neither the diagonal Beta value nor its
generating function. We build `b(n)` over `ℝ`, connect it to the parent's
complex Beta value by a cast, and derive the recurrence from a single factorial
identity.
-/

namespace BetaCentralBinomialOGF

open scoped Nat
open Complex

/-- The **central Beta sequence** `b(n) = (n!)² / (2n+1)!`, the diagonal value
`B(n+1, n+1)` of the Euler Beta integral, viewed as a real sequence. -/
noncomputable def centralBeta (n : ℕ) : ℝ :=
    (n ! * n ! : ℝ) / (2 * n + 1)!

/-- `b(0) = 1`. -/
theorem centralBeta_zero : centralBeta 0 = 1 := by
  simp [centralBeta]

/-- `b(1) = 1/6`. -/
theorem centralBeta_one : centralBeta 1 = 1 / 6 := by
  norm_num [centralBeta, Nat.factorial]

/-- `b(2) = 1/30`. -/
theorem centralBeta_two : centralBeta 2 = 1 / 30 := by
  norm_num [centralBeta, Nat.factorial]

/-- The sequence is strictly positive. -/
theorem centralBeta_pos (n : ℕ) : 0 < centralBeta n := by
  unfold centralBeta
  have hnum : (0 : ℝ) < (n ! * n ! : ℝ) := by
    have := Nat.factorial_pos n
    positivity
  have hden : (0 : ℝ) < ((2 * n + 1)! : ℝ) := by
    have := Nat.factorial_pos (2 * n + 1)
    exact_mod_cast this
  positivity

/-- **Reciprocal / central-binomial form.**  `b(n) = 1 / ((2n+1)·C(2n,n))`,
matching the parent entry's `betaIntegral_diag_central_binom`. -/
theorem centralBeta_eq_reciprocal (n : ℕ) :
    centralBeta n = 1 / (((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ) := by
  have hM : ((((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ)) ≠ 0 := by
    have : 0 < (2 * n + 1) * (2 * n).choose n := by
      have := Nat.choose_pos (show n ≤ 2 * n by omega); positivity
    exact_mod_cast this.ne'
  have hN : ((n ! : ℝ) * (n ! : ℝ)) ≠ 0 := by
    have := Nat.factorial_pos n; positivity
  have hfacR : ((2 * n + 1)! : ℝ)
      = (((2 * n + 1) * (2 * n).choose n : ℕ) : ℝ) * ((n ! : ℝ) * (n ! : ℝ)) := by
    have h := BetaCentralBinomial.factorial_two_mul_succ n
    rw [h]; push_cast; ring
  rw [centralBeta, hfacR]
  field_simp

/-- **Link to the gallery Beta integral.**  As a complex number, `b(n)` is
exactly the diagonal Euler Beta value `B(n+1, n+1)`. -/
theorem centralBeta_eq_betaIntegral (n : ℕ) :
    ((centralBeta n : ℝ) : ℂ) = betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1) := by
  rw [BetaCentralBinomial.betaIntegral_diag_central_binom,
      centralBeta_eq_reciprocal]
  push_cast
  ring

/-- The factorial identity underlying the recurrence, over `ℕ`:

  `(4n+6) · (n+1)!² · (2n+1)! = (n+1) · n!² · (2(n+1)+1)!`.

Both sides expand, via `Nat.factorial_succ`, to `(4n+6)(n+1)² · n!² · (2n+1)!`. -/
theorem centralBeta_factorial_identity (n : ℕ) :
    (4 * n + 6) * ((n + 1)! * (n + 1)!) * (2 * n + 1)!
      = (n + 1) * (n ! * n !) * (2 * (n + 1) + 1)! := by
  have e1 : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
  have e2 : (2 * (n + 1) + 1)! = (2 * n + 3) * ((2 * n + 2) * (2 * n + 1)!) := by
    have h3 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by ring
    have h2 : 2 * n + 2 = (2 * n + 1) + 1 := by ring
    rw [h3, Nat.factorial_succ, h2, Nat.factorial_succ]
  rw [e1, e2]; ring

/-- **The contiguous recurrence (new).**  `(4n+6) · b(n+1) = (n+1) · b(n)`.

Equivalently `b(n+1) = (n+1)/(2(2n+3)) · b(n)`. This is the arithmetic engine
of the generating function: it is the coefficient form of the ODE
`x(4-x) y' + (2-x) y = 2` satisfied by `y(x) = Σ b(n) xⁿ`. -/
theorem centralBeta_recurrence (n : ℕ) :
    (4 * (n : ℝ) + 6) * centralBeta (n + 1) = ((n : ℝ) + 1) * centralBeta n := by
  have h1 : ((2 * n + 1)! : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * n + 1)).ne'
  have h2 : ((2 * (n + 1) + 1)! : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * (n + 1) + 1)).ne'
  have hkey := centralBeta_factorial_identity n
  have hkeyR : (4 * (n : ℝ) + 6) * (((n + 1)! : ℝ) * ((n + 1)! : ℝ)) * ((2 * n + 1)! : ℝ)
      = ((n : ℝ) + 1) * ((n ! : ℝ) * (n ! : ℝ)) * ((2 * (n + 1) + 1)! : ℝ) := by
    exact_mod_cast hkey
  unfold centralBeta
  rw [← mul_div_assoc, ← mul_div_assoc, div_eq_div_iff h2 h1]
  linear_combination hkeyR

end BetaCentralBinomialOGF
