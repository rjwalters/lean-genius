/-
  Second-Order Derangement Convergence Rate
  Open Question: derangements-oq-03-oq-01

  Refines the convergence rate from |D(n)/n! - 1/e| ≤ 1/(n+1)!
  to the two-term asymptotic:

    D(n)/n! = 1/e + (-1)^n/(n+1)! + O(1/(n+2)!)

  More precisely: |D(n)/n! - 1/e - (-1)^n/(n+1)!| ≤ 1/(n+2)!

  This shows the first-order correction to D(n)/n! ≈ 1/e is
  exactly (-1)^n/(n+1)!, alternating in sign and decaying factorially.

  Main Results:
  - `tsum_tail_split`: tail splitting lemma for summable series
  - `second_order_convergence_rate`: |D(n)/n! - e^{-1} - (-1)^n/(n+1)!| ≤ 1/(n+2)!
  - `second_order_lower_bound`: 1/(n+1)! - 1/(n+2)! ≤ |D(n)/n! - e^{-1}|
  - `error_ratio_bound`: consecutive error ratio bounded by 1/(n+2)
  - `correction_term_sign_even/odd`: sign of the correction term

  Building on DerangementsOQ03 (convergence rate to 1/e).

  Axioms: 0
  Sorries: 0
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Finset Nat Real BigOperators Filter Topology

noncomputable section

-- We reuse definitions from DerangementsOQ03 by reopening the namespace
namespace DerangementsOQ03

-- ============================================================
-- Tail Splitting Lemma
-- ============================================================

/-- **Tail splitting**: The tail of a summable series starting at index m
    can be split into its first term and a shifted tail.
    ∑' k, f(m+k) = f(m) + ∑' k, f(m+1+k) -/
theorem tsum_tail_split (m : ℕ) :
    ∑' k, altFactTerm (m + k) =
    altFactTerm m + ∑' k, altFactTerm (m + 1 + k) := by
  have hs : Summable (fun k => altFactTerm (m + k)) := by
    exact summable_altFactTerm.comp_injective (fun a b h => by omega)
  rw [show (fun k => altFactTerm (m + k)) = (fun k => altFactTerm (m + (0 + k))) from by
    congr 1; ext k; ring_nf]
  conv_lhs => arg 1; ext k; rw [show m + (0 + k) = m + k from by ring]
  rw [eq_comm]
  have h0 : altFactTerm (m + 0) = altFactTerm m := by ring_nf
  rw [h0]
  have hshift : HasSum (fun k => altFactTerm (m + 1 + k))
      (∑' k, altFactTerm (m + k) - altFactTerm m) := by
    have hfull := hs.hasSum
    -- Split off the k=0 term
    have h0eq : ∑' k, altFactTerm (m + k) =
        altFactTerm m + ∑' k, altFactTerm (m + (k + 1)) := by
      have := hs.hasSum
      rw [tsum_eq_zero_add hs]
      simp only [Nat.zero_add]
    rw [h0eq]
    ring_nf
    have : Summable (fun k => altFactTerm (m + (k + 1))) := by
      exact hs.comp_injective (fun a b h => by omega)
    convert this.hasSum using 1
    ext k; congr 1; omega
  rw [hshift.tsum_eq]; ring

-- ============================================================
-- Second-Order Convergence Rate
-- ============================================================

/-- **Second-order convergence rate**: The refined bound shows that D(n)/n!
    approximates 1/e with a correction term (-1)^n/(n+1)! and a residual
    bounded by 1/(n+2)!.

    |D(n)/n! - e^{-1} - (-1)^n/(n+1)!| ≤ 1/(n+2)!

    Proof:
    1. D(n)/n! - e^{-1} = -(∑' k, altFactTerm(n+1+k))  [from convergence_rate proof]
    2. Split: ∑' k, altFactTerm(n+1+k) = altFactTerm(n+1) + ∑' k, altFactTerm(n+2+k)
    3. altFactTerm(n+1) = (-1)^{n+1}/(n+1)!, so -altFactTerm(n+1) = (-1)^n/(n+1)!
    4. The residual -(∑' k, altFactTerm(n+2+k)) has |·| ≤ 1/(n+2)!
       by the alternating series estimation (existing alternating_tail_bound). -/
theorem second_order_convergence_rate (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) -
     (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ)| ≤
    1 / ((n + 2).factorial : ℝ) := by
  -- Step 1: Rewrite D(n)/n! as the partial sum
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  -- The error is: altFactPartialSum n - (altFactPartialSum n + tail) - correction
  -- = -tail - correction
  -- = -(altFactTerm(n+1) + tail') - (-1)^n/(n+1)!
  -- where tail = ∑' k, altFactTerm(n+1+k) and tail' = ∑' k, altFactTerm(n+2+k)

  -- Step 2: Split the tail
  have hsplit := tsum_tail_split (n + 1)
  rw [hsplit]

  -- Step 3: Simplify: the altFactTerm(n+1) cancels with the correction
  have hterm : altFactTerm (n + 1) = (-1 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) := rfl
  have hneg_correction : -(-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ n := by
    rw [pow_succ]; ring

  -- Step 4: The expression simplifies to -(∑' k, altFactTerm(n+2+k))
  have hsimp :
      altFactPartialSum n -
      (altFactPartialSum n + (altFactTerm (n + 1) + ∑' k, altFactTerm (n + 1 + 1 + k))) -
      (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) =
      -(∑' k, altFactTerm (n + 1 + 1 + k)) := by
    rw [hterm]
    have h1 : (-1 : ℝ) ^ (n + 1) / ((n + 1).factorial : ℝ) -
        (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) =
        -(2 * (-1 : ℝ) ^ n) / ((n + 1).factorial : ℝ) := by
      rw [pow_succ]; ring
    ring

  rw [hsimp, abs_neg]

  -- Step 5: Apply the alternating tail bound at index n+2
  have h_bound := alternating_tail_bound (n + 1)
  rwa [show n + 1 + 1 = n + 2 from by omega] at h_bound

-- ============================================================
-- Lower Bound on Error (Tightness)
-- ============================================================

/-- **Lower bound on the first-order error**: The error |D(n)/n! - 1/e| is at least
    1/(n+1)! - 1/(n+2)!. This shows the convergence rate 1/(n+1)! is tight
    up to lower-order terms.

    From the second-order expansion:
    D(n)/n! - 1/e = (-1)^n/(n+1)! + residual, |residual| ≤ 1/(n+2)!
    So |D(n)/n! - 1/e| ≥ 1/(n+1)! - 1/(n+2)! by the triangle inequality. -/
theorem second_order_lower_bound (n : ℕ) :
    1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ) ≤
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| := by
  -- Use the decomposition: error = correction + residual
  rw [derangements_div_factorial, exp_neg_one_eq_tsum_alt, tsum_eq_partial_sum_add_tail n]
  -- Simplify: altFactPartialSum n - (altFactPartialSum n + tail) = -tail
  have hsimp : altFactPartialSum n -
      (altFactPartialSum n + ∑' k, altFactTerm (n + 1 + k)) =
      -(∑' k, altFactTerm (n + 1 + k)) := by ring
  rw [hsimp, abs_neg]
  -- Split tail = first term + rest
  rw [tsum_tail_split (n + 1)]
  -- |a + b| ≥ |a| - |b|
  have habs_triangle := abs_sub_abs_le_abs_sub
    (altFactTerm (n + 1)) (-(∑' k, altFactTerm (n + 1 + 1 + k)))
  -- We need: |first term| - |rest| ≤ |first term + rest|
  have h1 : |altFactTerm (n + 1)| - |∑' k, altFactTerm (n + 1 + 1 + k)| ≤
      |altFactTerm (n + 1) + ∑' k, altFactTerm (n + 1 + 1 + k)| := by
    have := abs_sub_abs_le_abs_sub
      (altFactTerm (n + 1) + ∑' k, altFactTerm (n + 1 + 1 + k))
      (∑' k, altFactTerm (n + 1 + 1 + k))
    simp only [add_sub_cancel_right] at this
    linarith [abs_nonneg (∑' k, altFactTerm (n + 1 + 1 + k))]
  -- |altFactTerm(n+1)| = 1/(n+1)!
  rw [altFactTerm_abs] at h1
  -- |tail from n+2| ≤ 1/(n+2)!
  have h2 := alternating_tail_bound (n + 1)
  rw [show n + 1 + 1 = n + 2 from by omega] at h2
  linarith

-- ============================================================
-- Ratio of Consecutive Errors
-- ============================================================

/-- **Error ratio bound**: The ratio of consecutive convergence errors satisfies
    |error(n+1)| / |error(n)| ≤ 1/(n+2) asymptotically.

    This formalizes as: the (n+1) error bound is 1/(n+2) times the n error bound.
    Since 1/(n+2)! = 1/(n+2) · 1/(n+1)!, each step improves by factor 1/(n+2). -/
theorem error_ratio_bound (n : ℕ) :
    (1 : ℝ) / ((n + 2).factorial : ℝ) =
    1 / ((n + 1).factorial : ℝ) * (1 / (n + 2 : ℝ)) := by
  rw [show (n + 2).factorial = (n + 1).factorial * (n + 2) from by
    rw [Nat.factorial_succ]; ring]
  push_cast
  field_simp

-- ============================================================
-- Sign of Correction Term
-- ============================================================

/-- For even n, the correction term (-1)^n/(n+1)! is positive:
    D(2m)/n! overshoots 1/e, so the positive correction captures this. -/
theorem correction_term_sign_even (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ (2 * n) / ((2 * n + 1).factorial : ℝ) := by
  apply div_nonneg
  · simp [pow_mul, neg_one_sq]
  · exact (factorial_cast_pos _).le

/-- For odd n, the correction term (-1)^n/(n+1)! is negative:
    D(2m+1)/n! undershoots 1/e, so the negative correction captures this. -/
theorem correction_term_sign_odd (n : ℕ) :
    (-1 : ℝ) ^ (2 * n + 1) / ((2 * n + 2).factorial : ℝ) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · simp [pow_succ, pow_mul, neg_one_sq]
  · exact (factorial_cast_pos _).le

-- ============================================================
-- Concrete Bounds
-- ============================================================

/-- Second-order error bound for n = 0: |D(0)/0! - e^{-1} - 1/1!| ≤ 1/2 -/
theorem second_order_bound_n0 :
    |(numDerangements 0 : ℝ) / (Nat.factorial 0 : ℝ) - rexp (-1) -
     1 / (Nat.factorial 1 : ℝ)| ≤ 1 / 2 := by
  have h := second_order_convergence_rate 0
  simp only [pow_zero, one_div] at h
  convert h using 2
  norm_num

/-- Second-order error bound for n = 1: |D(1)/1! - e^{-1} - (-1)/2!| ≤ 1/6 -/
theorem second_order_bound_n1 :
    |(numDerangements 1 : ℝ) / (Nat.factorial 1 : ℝ) - rexp (-1) -
     (-1 : ℝ) / (Nat.factorial 2 : ℝ)| ≤ 1 / 6 := by
  have h := second_order_convergence_rate 1
  simp only [pow_one, neg_one_mul, one_div] at h
  convert h using 2
  norm_num

/-- Second-order error bound for n = 2: |D(2)/2! - e^{-1} - 1/3!| ≤ 1/24 -/
theorem second_order_bound_n2 :
    |(numDerangements 2 : ℝ) / (Nat.factorial 2 : ℝ) - rexp (-1) -
     1 / (Nat.factorial 3 : ℝ)| ≤ 1 / 24 := by
  have h := second_order_convergence_rate 2
  simp only [pow_succ, pow_zero, one_mul, neg_one_mul, neg_neg, one_div] at h
  convert h using 2
  norm_num

end DerangementsOQ03

end
