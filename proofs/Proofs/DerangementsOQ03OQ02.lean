/-
# Derangements OQ-03-OQ-02: Third-Order Convergence Rate

## Context

Building on the derangements convergence hierarchy:
- **OQ-03**: First-order rate |D(n)/n! - 1/e| ≤ 1/(n+1)!
- **OQ-03-OQ-01**: Second-order rate |D(n)/n! - 1/e - (-1)^n/(n+1)!| ≤ 1/(n+2)!

## Main Result

**OQ-03-OQ-02**: Third-order refinement with two correction terms:

  |D(n)/n! - 1/e - (-1)^n/(n+1)! - (-1)^(n+1)/(n+2)!| ≤ 1/(n+3)!

The asymptotic expansion:
  D(n)/n! = 1/e + (-1)^n/(n+1)! + (-1)^(n+1)/(n+2)! + R_n
  where |R_n| ≤ 1/(n+3)!

The signs alternate: above 1/e for even n, below for odd n.
The corrections alternate in sign: +, -, +, -, ...

## Proof Strategy

The key identity: D(n)/n! = altFactPartialSum(n), and 1/e = ∑' altFactTerm(k).
The error is the tail starting at n+1. By splitting the tail twice:
  tail(n+1) = altFactTerm(n+1) + altFactTerm(n+2) + tail(n+3)

The two corrections cancel: -altFactTerm(n+1) = (-1)^n/(n+1)! and
-altFactTerm(n+2) = (-1)^(n+1)/(n+2)!. The residual is -tail(n+3),
bounded by 1/(n+3)! via alternating_tail_bound.

## Sorries

0 sorries (fully proved).

## Tags

derangements, convergence, alternating-series, asymptotic-expansion, third-order
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Finset Nat Real BigOperators Filter Topology

noncomputable section

-- Reopen DerangementsOQ03 namespace to access its definitions and lemmas
namespace DerangementsOQ03

-- ============================================================
-- SECTION I: Algebraic Helper Lemmas
-- ============================================================

/-- The altFactTerm at n+1 plus the correction (-1)^n/(n+1)! equals zero.
    This captures the cancellation: -altFactTerm(n+1) = (-1)^n/(n+1)! -/
private lemma cancel_first_correction (n : ℕ) :
    altFactTerm (n + 1) + (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) = 0 := by
  simp only [altFactTerm]
  rw [pow_succ]
  ring

/-- The altFactTerm at n+2 plus the correction (-1)^(n+1)/(n+2)! equals zero.
    This captures: -altFactTerm(n+2) = (-1)^(n+1)/(n+2)! -/
private lemma cancel_second_correction (n : ℕ) :
    altFactTerm (n + 2) + (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ) = 0 := by
  simp only [altFactTerm]
  rw [pow_succ, pow_succ]
  ring

-- ============================================================
-- SECTION II: Main Theorem
-- ============================================================

/-- **Third-order convergence rate**: Two correction terms refine D(n)/n! ≈ 1/e.

    |D(n)/n! - e^{-1} - (-1)^n/(n+1)! - (-1)^(n+1)/(n+2)!| ≤ 1/(n+3)!

    The proof iterates the tail-splitting from OQ-03-OQ-01:
    After two splits and cancellations, the residual is ∑' altFactTerm(n+3+k),
    bounded by 1/(n+3)! via alternating_tail_bound. -/
theorem third_order_convergence_rate (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) -
     (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) -
     (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ)| ≤
    1 / ((n + 3).factorial : ℝ) := by
  -- Rewrite D(n)/n! as partial sum and 1/e as tsum
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  -- First tail split: ∑(n+1+k) = altFactTerm(n+1) + ∑(n+2+k)
  rw [tsum_tail_split (n + 1)]
  -- Second tail split: ∑(n+2+k) = altFactTerm(n+2) + ∑(n+3+k)
  rw [show n + 1 + 1 = n + 2 from by omega, tsum_tail_split (n + 2)]
  -- Simplify: the partial sum terms cancel, and both corrections cancel
  -- leaving -(∑' k, altFactTerm(n+3+k))
  have hc1 := cancel_first_correction n
  have hc2 := cancel_second_correction n
  have hsimp :
      altFactPartialSum n -
      (altFactPartialSum n + (altFactTerm (n + 1) +
        (altFactTerm (n + 2) + ∑' k, altFactTerm (n + 2 + 1 + k)))) -
      (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) -
      (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ) =
      -(∑' k, altFactTerm (n + 2 + 1 + k)) := by
    linear_combination -hc1 - hc2
  rw [hsimp, abs_neg]
  -- Apply alternating tail bound: |∑(n+3+k)| ≤ 1/(n+3)!
  have h_bound := alternating_tail_bound (n + 2)
  simp only [show n + 2 + 1 = n + 3 from by omega] at h_bound
  exact_mod_cast h_bound

-- ============================================================
-- SECTION III: Corollaries
-- ============================================================

/-- **Asymptotic expansion form**: D(n)/n! approximated by three terms. -/
theorem asymptotic_expansion_two_corrections (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) -
     (rexp (-1) + (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) +
      (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ))| ≤
    1 / ((n + 3).factorial : ℝ) := by
  have h := third_order_convergence_rate n
  have heq : (numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) -
      (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) -
      (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ) =
      (numDerangements n : ℝ) / (n.factorial : ℝ) -
      (rexp (-1) + (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) +
       (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ)) := by ring
  rwa [← heq]

/-- **Correction signs**: The first correction (-1)^n/(n+1)! and second
    correction (-1)^(n+1)/(n+2)! alternate in sign. -/
theorem corrections_alternate_sign (n : ℕ) :
    (-1 : ℝ) ^ (n + 1) / ((n + 2).factorial : ℝ) =
    -((-1 : ℝ) ^ n / ((n + 2).factorial : ℝ)) := by
  rw [pow_succ]; ring

/-- **Error ratio**: The ratio of consecutive error bounds is 1/(n+3):
    (1/(n+3)!) / (1/(n+2)!) = 1/(n+3) -/
theorem error_bound_ratio (n : ℕ) :
    (1 / ((n + 3).factorial : ℝ)) / (1 / ((n + 2).factorial : ℝ)) =
    1 / ((n + 3) : ℝ) := by
  rw [Nat.factorial_succ (n + 2)]
  push_cast
  field_simp
  ring

/-- **Numerical verification for n = 0**: D(0)/0! = 1, correction = 1 - 1/1! - 1/2! = 1 - 1 - 1/2 = -1/2.
    The third-order bound: |1 - 1/e - 1 - (-1)/2| = |-1/e - 1/2| ≤ 1/3! = 1/6. -/
theorem third_order_bound_n0 :
    |(numDerangements 0 : ℝ) / ((0 : ℕ).factorial : ℝ) - rexp (-1) -
     (-1 : ℝ) ^ 0 / ((1 : ℕ).factorial : ℝ) -
     (-1 : ℝ) ^ 1 / ((2 : ℕ).factorial : ℝ)| ≤
    1 / ((3 : ℕ).factorial : ℝ) := third_order_convergence_rate 0

end DerangementsOQ03
