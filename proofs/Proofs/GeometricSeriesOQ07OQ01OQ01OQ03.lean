/-
# Moments of the descent statistic via the Eulerian polynomial

This file is a depth follow-up of the Frobenius lineage
(`GeometricSeriesOQ07OQ01OQ01`, which identifies the geometric-moment numerator
as the Eulerian polynomial `Eₘ` and proves `Eₘ(1) = m!`).

The Eulerian polynomial of order `m`,

  Eₘ(X) = ∑_{k} ⟨m,k-1⟩ Xᵏ        (no constant term, degree `m`),

is the *descent generating function* of the symmetric group `Sₘ`: the
coefficient of `Xᵏ` is the number of permutations of `{1,…,m}` with exactly
`k-1` descents.  Consequently `Eₘ(1) = m!` (already proved upstream) and, more
finely, the *moments of the descent statistic* are read off from the
derivatives of `Eₘ` evaluated at `1`:

  T(m) := E'ₘ(1) = ∑_{k} k·⟨m,k-1⟩      (first factorial moment of `k = des+1`)
  U(m) := E''ₘ(1) = ∑_{k} k(k-1)·⟨m,k-1⟩ (second factorial moment).

The point of this entry is that the *analytic* definition of `Eₘ` by the
first-order differential recurrence

  E_{m+1} = X·(1-X)·E'ₘ + (m+1)·X·Eₘ

turns these moment computations into a **mechanical derivative-and-evaluate**:
differentiating the recurrence once (resp. twice) and evaluating at `X = 1`
(where the factor `X·(1-X)` vanishes) gives clean linear recurrences for `T`
and `U`, whose closed forms are

  **2·E'ₘ(1)  = (m+1)!**              (`two_mul_deriv_eulerPoly_eval_one`,  m ≥ 1)
  **12·E''ₘ(1) = (3m-2)·(m+1)!**       (`twelve_mul_deriv2_eulerPoly_eval_one`, m ≥ 2).

Dividing by `m!` recovers the two classical facts about a uniformly random
permutation of `{1,…,m}`:

  * the **mean number of descents is `(m-1)/2`**, and
  * the **variance of the number of descents is `(m+1)/12`**.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ03

open Polynomial Nat
open GeometricSeriesOQ07OQ01OQ01

variable {R : Type*} [CommRing R]

/-! ## Part 1: the one-step moment recurrences

Both are pure consequences of the differential recurrence `eulerPoly_succ`,
obtained by differentiating once / twice and evaluating at `X = 1`.  The factor
`X·(1-X)` evaluates to `0` at `X = 1`, which is what makes the higher derivative
terms drop out. -/

/-- **First moment recurrence.**  `E'_{m+1}(1) = (m+1)·Eₘ(1) + m·E'ₘ(1)`.
Differentiate `E_{m+1} = X(1-X)E'ₘ + (m+1)X·Eₘ` once and evaluate at `1`. -/
theorem deriv_eulerPoly_eval_one_succ (m : ℕ) :
    (derivative (eulerPoly (m + 1) : R[X])).eval 1
      = ((m : R) + 1) * (eulerPoly m : R[X]).eval 1
        + (m : R) * (derivative (eulerPoly m : R[X])).eval 1 := by
  rw [eulerPoly_succ]
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
    derivative_natCast, eval_add, eval_sub, eval_mul, eval_X, eval_one,
    eval_natCast, eval_zero, one_mul, mul_one, zero_mul, add_zero, zero_add]
  ring

/-- **Second moment recurrence.**  `E''_{m+1}(1) = 2m·E'ₘ(1) + (m-1)·E''ₘ(1)`.
Differentiate the recurrence twice and evaluate at `1`. -/
theorem deriv2_eulerPoly_eval_one_succ (m : ℕ) :
    (derivative (derivative (eulerPoly (m + 1) : R[X]))).eval 1
      = 2 * (m : R) * (derivative (eulerPoly m : R[X])).eval 1
        + ((m : R) - 1) * (derivative (derivative (eulerPoly m : R[X]))).eval 1 := by
  rw [eulerPoly_succ]
  simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_one,
    derivative_natCast, derivative_zero, eval_add, eval_sub, eval_mul, eval_X, eval_one,
    eval_natCast, eval_zero, one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_zero]
  ring

/-! ## Part 2: closed forms (integral, denominator-free) -/

/-- **The first factorial moment of the descent statistic.**
For `m ≥ 1`, `2·E'ₘ(1) = (m+1)!`.  Equivalently `∑ₖ k·⟨m,k-1⟩ = (m+1)!/2`, so the
mean number of descents over `Sₘ` is `(m-1)/2`. -/
theorem two_mul_deriv_eulerPoly_eval_one {m : ℕ} (hm : 1 ≤ m) :
    2 * (derivative (eulerPoly m : R[X])).eval 1 = ((m + 1)! : R) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [eulerPoly_one, derivative_X]
    simp [Nat.factorial]
  | succ m hm ih =>
    rw [deriv_eulerPoly_eval_one_succ, eval_eulerPoly_one]
    have hf1 : ((m + 1)! : R) = ((m : R) + 1) * (m ! : R) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hf2 : ((m + 1 + 1)! : R) = ((m : R) + 2) * (((m : R) + 1) * (m ! : R)) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    rw [hf1] at ih
    rw [hf2]
    linear_combination (m : R) * ih

/-- **The second factorial moment of the descent statistic.**
For `m ≥ 2`, `12·E''ₘ(1) = (3m-2)·(m+1)!`.  Combined with the first moment this
yields variance `(m+1)/12` of the descent count over `Sₘ`. -/
theorem twelve_mul_deriv2_eulerPoly_eval_one {m : ℕ} (hm : 2 ≤ m) :
    12 * (derivative (derivative (eulerPoly m : R[X]))).eval 1
      = (3 * (m : R) - 2) * ((m + 1)! : R) := by
  induction m, hm using Nat.le_induction with
  | base =>
    -- E₂ = X + X², E''₂ = 2, so 12·2 = 24 = (3·2-2)·3! = 4·6.
    rw [eulerPoly_two]
    simp only [derivative_add, derivative_X, derivative_X_pow]
    push_cast
    simp [Nat.factorial]
    ring
  | succ m hm ih =>
    have hm1 : 1 ≤ m := le_trans (by norm_num) hm
    rw [deriv2_eulerPoly_eval_one_succ]
    have hmean := two_mul_deriv_eulerPoly_eval_one (R := R) hm1
    have hf : ((m + 1 + 1)! : R) = ((m : R) + 2) * ((m + 1)! : R) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hf]
    push_cast
    linear_combination (12 * (m : R)) * hmean + ((m : R) - 1) * ih

/-! ## Part 3: the descent statistic over `ℚ`

Specialising to `ℚ` turns the integral identities into the mean and variance of
the number of descents of a uniformly random permutation of `{1,…,m}`. -/

/-- **Mean of the `descents+1` statistic.**  Over `ℚ`,
`E'ₘ(1) / Eₘ(1) = (m+1)/2`, i.e. the average value of `k = des+1` over `Sₘ` is
`(m+1)/2`, so the mean number of descents is `(m-1)/2`. -/
theorem mean_descents_succ {m : ℕ} (hm : 1 ≤ m) :
    (derivative (eulerPoly m : ℚ[X])).eval 1 / (eulerPoly m : ℚ[X]).eval 1
      = ((m : ℚ) + 1) / 2 := by
  have hS : (eulerPoly m : ℚ[X]).eval 1 = (m ! : ℚ) := eval_eulerPoly_one m
  have hT : 2 * (derivative (eulerPoly m : ℚ[X])).eval 1 = ((m + 1)! : ℚ) :=
    two_mul_deriv_eulerPoly_eval_one hm
  have hfac : (m ! : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos m).ne'
  have hfac1 : ((m + 1)! : ℚ) = ((m : ℚ) + 1) * (m ! : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hS, div_eq_div_iff hfac (by norm_num : (2 : ℚ) ≠ 0)]
  linear_combination hT + hfac1

/-- **Variance of the descent statistic.**  Over `ℚ`, for `m ≥ 2`,

  `E''ₘ(1)/Eₘ(1) + E'ₘ(1)/Eₘ(1) - (E'ₘ(1)/Eₘ(1))² = (m+1)/12`.

The left side is `E[k(k-1)] + E[k] - E[k]² = E[k²] - E[k]² = Var(k)`, the variance
of `k = des+1` (equal to the variance of the number of descents).  So the number
of descents of a uniformly random permutation of `{1,…,m}` has variance
`(m+1)/12`. -/
theorem variance_descents_succ {m : ℕ} (hm : 2 ≤ m) :
    (derivative (derivative (eulerPoly m : ℚ[X]))).eval 1 / (eulerPoly m : ℚ[X]).eval 1
      + (derivative (eulerPoly m : ℚ[X])).eval 1 / (eulerPoly m : ℚ[X]).eval 1
      - ((derivative (eulerPoly m : ℚ[X])).eval 1 / (eulerPoly m : ℚ[X]).eval 1) ^ 2
      = ((m : ℚ) + 1) / 12 := by
  have hm1 : 1 ≤ m := le_trans (by norm_num) hm
  have hS : (eulerPoly m : ℚ[X]).eval 1 = (m ! : ℚ) := eval_eulerPoly_one m
  have hTval : (derivative (eulerPoly m : ℚ[X])).eval 1 = ((m + 1)! : ℚ) / 2 := by
    linear_combination (two_mul_deriv_eulerPoly_eval_one (R := ℚ) hm1) / 2
  have hUval : (derivative (derivative (eulerPoly m : ℚ[X]))).eval 1
      = (3 * (m : ℚ) - 2) * ((m + 1)! : ℚ) / 12 := by
    linear_combination (twelve_mul_deriv2_eulerPoly_eval_one (R := ℚ) hm) / 12
  have hfac : (m ! : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hfac1 : ((m + 1)! : ℚ) = ((m : ℚ) + 1) * (m ! : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hS, hTval, hUval, hfac1]
  field_simp
  ring

end GeometricSeriesOQ07OQ01OQ01OQ03
