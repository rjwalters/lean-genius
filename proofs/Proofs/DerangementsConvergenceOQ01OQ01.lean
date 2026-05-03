/-
  Derangements Nearest Integer Theorem
  Open Question: derangements-convergence-oq-01-oq-01

  For n ≥ 1, the number of derangements D(n) equals the nearest integer to n!/e:
    |D(n) - n!/e| < 1/2

  This follows from the alternating series rate bound in DerangementsConvergence.lean:
    |D(n)/n! - e⁻¹| ≤ 1/(n+1)!

  Multiplying by n! gives |D(n) - n!/e| ≤ 1/(n+1), and for n ≥ 2 this is ≤ 1/3 < 1/2.
  The n=1 case follows from e > 2: |D(1) - 1/e| = 1/e < 1/2.

  ## Main Results

  - `derangements_rate_scaled`: |D(n) - n!/e| ≤ 1/(n+1) for all n ≥ 0
  - `derangements_nearest_integer`: |D(n) - n!/e| < 1/2 for n ≥ 2
  - `derangements_nearest_all`: |D(n) - n!/e| < 1/2 for n ≥ 1
  - `derangements_unique_nearest`: D(n) is the unique natural number within 1/2 of n!/e
-/

import Proofs.DerangementsConvergence
import Mathlib.Tactic

open Nat Real Filter Topology

namespace DerangementsNearestInt

-- ============================================================
-- §1. SCALED RATE BOUND
-- ============================================================

/-- The alternating series rate bound scaled to integers:
    |D(n) - n!/e| ≤ 1/(n+1) for all n. -/
theorem derangements_rate_scaled (n : ℕ) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1| ≤ 1 / (n + 1 : ℕ) := by
  have hrate := derangements_convergence_rate n
  have hn_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr n.factorial_pos
  have hexp_pos : (0 : ℝ) < rexp 1 := Real.exp_pos 1
  -- rexp(-1) = 1/rexp(1)
  rw [show rexp (-1) = 1 / rexp 1 from by rw [Real.exp_neg]; ring] at hrate
  -- D(n) - n!/e = n! * (D(n)/n! - 1/e)
  have hrw : (numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1 =
             (n.factorial : ℝ) * ((numDerangements n : ℝ) / n.factorial - 1 / rexp 1) := by
    field_simp; ring
  rw [hrw, abs_mul, abs_of_pos hn_pos]
  -- n! * |D(n)/n! - 1/e| ≤ n! / (n+1)! = 1/(n+1)
  calc (n.factorial : ℝ) * |(numDerangements n : ℝ) / n.factorial - 1 / rexp 1|
      ≤ n.factorial * (1 / (n + 1).factorial) :=
        mul_le_mul_of_nonneg_left hrate hn_pos.le
    _ = 1 / (n + 1 : ℕ) := by
        have hsucc : ((n + 1).factorial : ℝ) = (n + 1 : ℕ) * n.factorial := by
          push_cast [Nat.factorial_succ]; ring
        rw [hsucc]
        have hn1_pos : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
        field_simp

-- ============================================================
-- §2. THE NEAREST INTEGER THEOREM
-- ============================================================

/-- **Main theorem**: For n ≥ 2, D(n) is within 1/2 of n!/e. -/
theorem derangements_nearest_integer (n : ℕ) (hn : 2 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1| < 1 / 2 := by
  calc |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1|
      ≤ 1 / (n + 1 : ℕ) := derangements_rate_scaled n
    _ ≤ 1 / (3 : ℝ) := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast show 3 ≤ n + 1 from by omega
    _ < 1 / 2 := by norm_num

/-- **n=1 case**: D(1) = 0 and |0 - 1/e| = 1/e < 1/2 since e > 2. -/
theorem derangements_nearest_integer_n1 :
    |(numDerangements 1 : ℝ) - ((1 : ℕ).factorial : ℝ) / rexp 1| < 1 / 2 := by
  have hD1 : (numDerangements 1 : ℝ) = 0 := by
    norm_cast
    decide
  have hf1 : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num
  rw [hD1, hf1, zero_sub, abs_neg, abs_of_pos (by positivity)]
  -- Goal: 1 / rexp 1 < 1 / 2, i.e., 2 < rexp 1
  rw [div_lt_div_iff (Real.exp_pos 1) two_pos]
  linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 from one_ne_zero)]

/-- **All n ≥ 1**: D(n) is the nearest integer to n!/e. -/
theorem derangements_nearest_all (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1| < 1 / 2 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · -- n = 1
    have hn1 : n = 1 := by omega
    subst hn1
    exact derangements_nearest_integer_n1
  · exact derangements_nearest_integer n h

-- ============================================================
-- §3. UNIQUENESS
-- ============================================================

/-- D(n) is the unique natural number within distance 1/2 of n!/e. -/
theorem derangements_unique_nearest (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : |(m : ℝ) - (n.factorial : ℝ) / rexp 1| < 1 / 2) :
    m = numDerangements n := by
  have hd := derangements_nearest_all n hn
  -- |m - D(n)| ≤ |m - n!/e| + |D(n) - n!/e| < 1
  have hclose : |(m : ℝ) - numDerangements n| < 1 := by
    have hrw : (m : ℝ) - numDerangements n =
               (m - n.factorial / rexp 1) + (n.factorial / rexp 1 - numDerangements n) := by ring
    rw [hrw]
    calc |(m : ℝ) - n.factorial / rexp 1 + (n.factorial / rexp 1 - numDerangements n)|
        ≤ |(m : ℝ) - n.factorial / rexp 1| + |n.factorial / rexp 1 - numDerangements n| :=
          abs_add _ _
      _ < 1 / 2 + 1 / 2 := by
          have : |n.factorial / rexp 1 - (numDerangements n : ℝ)| < 1 / 2 := by
            rw [abs_sub_comm]; exact hd
          linarith
      _ = 1 := by norm_num
  -- Two naturals within distance 1 must be equal
  have heq : (m : ℤ) = numDerangements n := by
    have h1 : -(1 : ℤ) < (m : ℤ) - numDerangements n := by
      exact_mod_cast (abs_lt.mp hclose).1
    have h2 : (m : ℤ) - numDerangements n < 1 := by
      exact_mod_cast (abs_lt.mp hclose).2
    omega
  exact_mod_cast heq

-- ============================================================
-- §4. TIGHTER BOUNDS
-- ============================================================

/-- For n ≥ 3, the error is at most 1/4. -/
theorem derangements_quarter_bound (n : ℕ) (hn : 3 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1| ≤ 1 / 4 := by
  calc |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1|
      ≤ 1 / (n + 1 : ℕ) := derangements_rate_scaled n
    _ ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast show 4 ≤ n + 1 from by omega

/-- The error is at most 1/k for any k ≤ n+1 (parametric bound). -/
theorem derangements_parametric_bound (n k : ℕ) (hk : k ≤ n + 1) (hk_pos : 0 < k) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1| ≤ 1 / k := by
  calc |(numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1|
      ≤ 1 / (n + 1 : ℕ) := derangements_rate_scaled n
    _ ≤ 1 / k := by
        apply one_div_le_one_div_of_le (Nat.cast_pos.mpr hk_pos)
        exact_mod_cast hk

end DerangementsNearestInt
