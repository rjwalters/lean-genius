import Proofs.BetaIntegralRecurrence
import Mathlib.Tactic

/-
# The Symmetric Beta Value as a Central Binomial Reciprocal

## What This Proves

The parent entry establishes the integer closed form of the Euler Beta integral,
`B(m+1, n+1) = m!·n!/(m+n+1)!`. On the **diagonal** `m = n` this collapses to a
single Wallis-type quantity governed by the central binomial coefficient:

  **`betaIntegral_diag_central_binom`**:
    `B(n+1, n+1) = 1 / ((2n+1) · C(2n, n))`.

Equivalently `B(n+1, n+1) = (n!)² / (2n+1)!`, the reciprocal of the integer
`(2n+1)·\binom{2n}{n}`. This is exactly the normalization constant of the
symmetric Beta(n+1, n+1) density on `[0,1]`: the probability density
`x^n (1-x)^n / B(n+1,n+1)` integrates to one, so the total mass `B(n+1,n+1)` is
the reciprocal of `(2n+1)\binom{2n}{n}`.

The analytic content is entirely inherited from the parent's
`betaIntegral_nat_nat`; the new ingredient is the elementary factorial identity

  **`factorial_two_mul_succ`**:  `(2n+1)! = (2n+1) · C(2n,n) · (n!·n!)`,

which rewrites the diagonal value `(n!)²/(2n+1)!` as `1/((2n+1)·C(2n,n))`.

## Relation to Mathlib

Mathlib has the central binomial coefficient `Nat.centralBinom n = (2n).choose n`
and the factorial/choose factorization `Nat.choose_mul_factorial_mul_factorial`,
but it does not state this Beta value. We assemble it from the parent entry.
-/

namespace BetaCentralBinomial

open Complex

/-- **Factorial factorization (new).** `(2n+1)! = (2n+1) · C(2n,n) · (n!·n!)`.

This is the multiplicative bridge between the factorial form `(n!)²/(2n+1)!` and
the central-binomial form `1/((2n+1)·C(2n,n))`. It follows from the basic
identity `C(2n,n)·n!·n! = (2n)!` (specializing
`Nat.choose_mul_factorial_mul_factorial`) and one step of `Nat.factorial_succ`. -/
theorem factorial_two_mul_succ (n : ℕ) :
    Nat.factorial (2 * n + 1)
      = (2 * n + 1) * (2 * n).choose n * (Nat.factorial n * Nat.factorial n) := by
  have hle : n ≤ 2 * n := by omega
  have h := Nat.choose_mul_factorial_mul_factorial hle
  rw [show 2 * n - n = n by omega] at h
  -- h : (2*n).choose n * n ! * n ! = (2*n)!
  rw [Nat.factorial_succ (2 * n), ← h]
  ring

/-- **Diagonal Beta value as a central binomial reciprocal (new).**

  `B(n+1, n+1) = 1 / ((2n+1) · C(2n, n))`.

This is the total mass of the symmetric Beta(n+1, n+1) density on `[0,1]`. -/
theorem betaIntegral_diag_central_binom (n : ℕ) :
    betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1)
      = 1 / (((2 * n + 1) * (2 * n).choose n : ℕ) : ℂ) := by
  have hd1 : ((Nat.factorial (2 * n + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hd2 : (((2 * n + 1) * (2 * n).choose n : ℕ) : ℂ) ≠ 0 := by
    have hpos : 0 < (2 * n + 1) * (2 * n).choose n := by
      have := Nat.choose_pos (show n ≤ 2 * n by omega); positivity
    exact_mod_cast hpos.ne'
  have key : Nat.factorial n * Nat.factorial n * ((2 * n + 1) * (2 * n).choose n)
      = Nat.factorial (2 * n + 1) := by
    rw [factorial_two_mul_succ]; ring
  rw [BetaIntegralRecurrence.betaIntegral_nat_nat n n,
      show n + n + 1 = 2 * n + 1 by ring,
      div_eq_div_iff hd1 hd2, one_mul, ← Nat.cast_mul, ← Nat.cast_mul, key]

/-- The same value phrased with Mathlib's `Nat.centralBinom`:
`B(n+1, n+1) = 1 / ((2n+1) · centralBinom n)`. -/
theorem betaIntegral_diag_centralBinom (n : ℕ) :
    betaIntegral ((n : ℂ) + 1) ((n : ℂ) + 1)
      = 1 / (((2 * n + 1) * Nat.centralBinom n : ℕ) : ℂ) := by
  rw [betaIntegral_diag_central_binom]; rfl

/-- `B(1,1) = 1` recovered from the central-binomial form (`n = 0`:
`(2·0+1)·C(0,0) = 1`). -/
theorem betaIntegral_one_one_central : betaIntegral 1 1 = 1 := by
  have h := betaIntegral_diag_central_binom 0
  norm_num at h
  simpa using h

/-- `B(2,2) = 1/6` from the central-binomial form (`n = 1`:
`(2·1+1)·C(2,1) = 3·2 = 6`). -/
theorem betaIntegral_two_two : betaIntegral 2 2 = 1 / 6 := by
  have h := betaIntegral_diag_central_binom 1
  norm_num [Nat.choose] at h
  simpa using h

end BetaCentralBinomial
