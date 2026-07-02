/-
  Derangements: the inclusion–exclusion (binomial) formula
      D(n) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!
  Open question: derangements-convergence-oq-07-oq-02

  ## Context

  The parent open question `derangements-convergence-oq-07` proves the *fixed-point
  convolution identity*

      n! = Σ_{k=0}^{n} C(n,k) · D(n−k)                              (∗)

  (`factorial_eq_sum_choose_mul_numDerangements`), which expresses `n!` as a binomial
  convolution of the derangement numbers `D(m) = numDerangements m`.  The natural
  companion is the *inverse* relation obtained by binomial (Möbius) inversion of (∗):

      D(n) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!                   (†)

  which is the classical inclusion–exclusion formula for derangements written in the
  binomial-coefficient convention.

  ## What this file adds

  Mathlib's `numDerangements_sum` already establishes an inclusion–exclusion sum for
  `numDerangements`, but in the **ascending-factorial** convention:

      (D(n) : ℤ) = Σ_{k=0}^{n} (−1)^k · (k+1).ascFactorial (n−k).

  The term `(k+1).ascFactorial (n−k)` equals `(k+1)(k+2)⋯n = n!/k!`, which is *not*
  the same syntactic object as `C(n,k)·(n−k)!`.  The bridge is the purely arithmetic
  identity

      (k+1).ascFactorial (n−k) = C(n,k) · (n−k)!          for k ≤ n,

  proved here by cancelling `k!` from both sides using
  `Nat.factorial_mul_ascFactorial` and `Nat.choose_mul_factorial_mul_factorial`.
  Rewriting `numDerangements_sum` term-by-term with this bridge yields (†).

  This is the standard binomial form of the derangement count and complements the
  parent's convolution identity; neither the bridge lemma nor the binomial form of
  the sum is stated in Mathlib.

  ## Main results
  - `ascFactorial_succ_eq_choose_mul_factorial`
        : `(k+1).ascFactorial (n−k) = C(n,k)·(n−k)!` for `k ≤ n`
  - `numDerangements_eq_sum_neg_one_pow_choose_mul_factorial`
        : `(D(n) : ℤ) = Σ_{k≤n} (−1)^k · C(n,k) · (n−k)!`   (the formula (†))
  - `numDerangements_eq_alternating_binomial_sum`
        : the same, packaged with an `ℕ`-valued absolute-value reading of each term
-/
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open Finset Nat
open scoped BigOperators

namespace DerangementsInclusionExclusion

/-- The ascending factorial appearing in `numDerangements_sum` is exactly the
binomial term `C(n,k)·(n−k)!`.  For `k ≤ n`,

    `(k+1).ascFactorial (n−k) = n.choose k * (n−k)!`.

Both sides equal `n!/k!`; we prove it by multiplying through by `k!` and cancelling,
using `Nat.factorial_mul_ascFactorial` on the left and
`Nat.choose_mul_factorial_mul_factorial` on the right. -/
theorem ascFactorial_succ_eq_choose_mul_factorial {n k : ℕ} (h : k ≤ n) :
    (k + 1).ascFactorial (n - k) = n.choose k * (n - k)! := by
  -- It suffices to prove the equality after multiplying by the positive number `k!`.
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
  -- Left side: k! * (k+1).ascFactorial (n-k) = (k + (n-k))! = n!
  have hleft : k ! * (k + 1).ascFactorial (n - k) = n ! := by
    rw [Nat.factorial_mul_ascFactorial, Nat.add_sub_cancel' h]
  -- Right side: k! * (C(n,k) * (n-k)!) = C(n,k) * k! * (n-k)! = n!
  have hright : k ! * (n.choose k * (n - k)!) = n ! := by
    rw [← Nat.choose_mul_factorial_mul_factorial h]; ring
  rw [hleft, hright]

/-- **Inclusion–exclusion (binomial) formula for derangements.**

    `(numDerangements n : ℤ) = Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)!`.

This is the binomial-inversion companion of the parent's convolution identity
`n! = Σ C(n,k)·D(n−k)`.  It is obtained from Mathlib's `numDerangements_sum`
(stated with ascending factorials) by rewriting each term through
`ascFactorial_succ_eq_choose_mul_factorial`. -/
theorem numDerangements_eq_sum_neg_one_pow_choose_mul_factorial (n : ℕ) :
    (numDerangements n : ℤ)
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ k * (n.choose k) * ((n - k)! : ℤ) := by
  rw [numDerangements_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  -- Rewrite the ascending-factorial term into the binomial term.
  rw [ascFactorial_succ_eq_choose_mul_factorial hkn]
  push_cast
  ring

/-- The same inclusion–exclusion formula, with the summand's magnitude exhibited as
the natural number `C(n,k)·(n−k)!` and the sign carried by `(−1)^k`. -/
theorem numDerangements_eq_alternating_binomial_sum (n : ℕ) :
    (numDerangements n : ℤ)
      = ∑ k ∈ Finset.range (n + 1),
          (-1 : ℤ) ^ k * ((n.choose k * (n - k)! : ℕ) : ℤ) := by
  rw [numDerangements_eq_sum_neg_one_pow_choose_mul_factorial]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  ring

/-- Sanity check: `D(4) = 9`, and the alternating binomial sum reproduces it:
`24 − 24 + 12 − 4 + 1 = 9`. -/
example : (numDerangements 4 : ℤ)
    = ∑ k ∈ Finset.range 5, (-1 : ℤ) ^ k * (Nat.choose 4 k) * ((4 - k)! : ℤ) :=
  numDerangements_eq_sum_neg_one_pow_choose_mul_factorial 4

end DerangementsInclusionExclusion
