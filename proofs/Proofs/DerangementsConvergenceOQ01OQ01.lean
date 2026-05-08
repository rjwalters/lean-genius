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

-- ============================================================
-- §5. PARITY-CONTROLLED ERROR SIGN
-- ============================================================

/-! The previous sections establish the *magnitude* bound `|D(n) - n!/e| < 1/2`.
    This section pins down the *sign*: the rounding direction is parity-controlled.

    For monic alternating series `∑ k, (-1)^k / (n+1+k)!`, the partial sums are
    all non-negative (`alt_partial_sum_nonneg` from `DerangementsConvergence`),
    hence the tsum is non-negative. Combined with the factorization

      `D(n)/n! - 1/e = (-1)^n · ∑' k, (-1)^k / (n+1+k)!`

    (derived from `derangements_div_factorial` + `exp_neg_one_eq_tsum_alt` +
    `tsum_eq_partial_sum_add_tail`), this gives the parity-sign theorem:

      `(-1)^n · (D(n) - n!/e) ≥ 0`,

    i.e. `D(n) ≥ n!/e` for even n and `D(n) ≤ n!/e` for odd n.

    The proof reuses ONLY public lemmas already in `DerangementsConvergence.lean`;
    no new infrastructure required.
-/

/-- **Parity-controlled error sign**: the rounding direction of `D(n)` toward
    `n!/e` is determined by the parity of `n` — `D(n) ≥ n!/e` when `n` is
    even, and `D(n) ≤ n!/e` when `n` is odd. Combined with
    `derangements_rate_scaled` this gives the two-sided sharp bound

      `0 ≤ (-1)^n · (D(n) - n!/e) ≤ 1/(n+1)`. -/
theorem derangements_error_sign (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * ((numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1) := by
  -- Define f k := (-1)^k / (n+1+k)! — the parity-stripped tail factor.
  set f : ℕ → ℝ := fun k => (-1 : ℝ) ^ k / ((n + 1 + k).factorial : ℝ) with hf_def
  -- Step A: f is summable. Bound |f k| ≤ 1/k! and 1/k! is summable.
  have hf_summable : Summable f := by
    apply Summable.of_norm_bounded (fun k : ℕ => (1 : ℝ) / (k.factorial : ℝ))
    · -- ∑ 1/k! is summable (special case of summable_pow_div_factorial 1).
      have := summable_pow_div_factorial (1 : ℝ)
      simpa [one_pow] using this
    · -- |f k| = 1/(n+1+k)! ≤ 1/k!.
      intro k
      simp only [hf_def, norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow]
      apply div_le_div_of_nonneg_left (by norm_num) (factorial_cast_pos' k)
      exact_mod_cast Nat.factorial_le (Nat.le_add_left k (n + 1))
  -- Step B: tsum f ≥ 0. Each partial sum is ≥ 0 (alt_partial_sum_nonneg);
  -- the tsum is the limit, so ≥ 0.
  have hf_tsum_nonneg : (0 : ℝ) ≤ ∑' k, f k := by
    have htend := hf_summable.hasSum.tendsto_sum_nat
    apply ge_of_tendsto' htend
    intro N
    exact alt_partial_sum_nonneg (n + 1) N
  -- Step C: factor (D(n) - n!/e) = -n! · (-1)^(n+1) · ∑' f.
  -- This combines:
  --   D(n)/n! = altFactPartialSum n           (derangements_div_factorial)
  --   1/e = altFactPartialSum n + tail        (exp_neg_one_eq_tsum_alt + tsum_eq_partial_sum_add_tail)
  --   tail = (-1)^(n+1) · ∑' f                (factor (-1)^(n+1) out of altFactTerm (n+1+k))
  have h_factorial_pos : (0 : ℝ) < (n.factorial : ℝ) := factorial_cast_pos' n
  have h_factor :
      (numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1 =
        -(n.factorial : ℝ) * ((-1 : ℝ) ^ (n + 1)) * ∑' k, f k := by
    have hdiv := derangements_div_factorial n
    have hexp := exp_neg_one_eq_tsum_alt
    have htail := tsum_eq_partial_sum_add_tail n
    -- altFactTerm (n+1+k) = (-1)^(n+1) · f k.
    have h_alt_eq : (fun k => altFactTerm (n + 1 + k)) =
                    (fun k => (-1 : ℝ) ^ (n + 1) * f k) := by
      funext k
      simp only [altFactTerm, hf_def]
      rw [pow_add, mul_div_assoc]
    have h_tail_factored : ∑' k, altFactTerm (n + 1 + k) =
                           (-1 : ℝ) ^ (n + 1) * ∑' k, f k := by
      rw [h_alt_eq]; exact tsum_mul_left
    have h_exp_full :
        rexp (-1) = altFactPartialSum n + (-1 : ℝ) ^ (n + 1) * ∑' k, f k := by
      rw [hexp, htail, h_tail_factored]
    have h_exp_neg : rexp (-1) = 1 / rexp 1 := by rw [Real.exp_neg]
    -- D(n)/n! - rexp(-1) = -((-1)^(n+1) · ∑' f).
    have hkey : (numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1) =
                -((-1 : ℝ) ^ (n + 1) * ∑' k, f k) := by
      rw [hdiv, h_exp_full]; ring
    -- D(n) - n!/e = n! · (D(n)/n! - rexp(-1)).
    have h_n_factorize :
        (numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1 =
        (n.factorial : ℝ) *
          ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) := by
      rw [h_exp_neg]; field_simp
    rw [h_n_factorize, hkey]; ring
  -- Step D: (-1)^n · (-1)^(n+1) = -1; together with -1 outside, the signs cancel.
  have h_combine : (-1 : ℝ) ^ n * ((-1 : ℝ) ^ (n + 1)) = -1 := by
    rw [← pow_add]
    rw [show n + (n + 1) = 2 * n + 1 from by ring]
    rw [pow_succ, pow_mul]
    simp
  rw [h_factor]
  -- Goal: 0 ≤ (-1)^n · (-n! · (-1)^(n+1) · ∑' f).
  have h_simplify :
      (-1 : ℝ) ^ n * (-(n.factorial : ℝ) * (-1 : ℝ) ^ (n + 1) * ∑' k, f k) =
        (n.factorial : ℝ) * ∑' k, f k := by
    have hrearrange :
        (-1 : ℝ) ^ n * (-(n.factorial : ℝ) * (-1 : ℝ) ^ (n + 1) * ∑' k, f k) =
        (-((-1 : ℝ) ^ n * (-1 : ℝ) ^ (n + 1))) * (n.factorial : ℝ) * ∑' k, f k := by
      ring
    rw [hrearrange, h_combine]
    ring
  rw [h_simplify]
  exact mul_nonneg h_factorial_pos.le hf_tsum_nonneg

end DerangementsNearestInt
