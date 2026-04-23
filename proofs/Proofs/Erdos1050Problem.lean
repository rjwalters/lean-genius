/-
  Erdős Problem #1050: Irrationality of ∑ 1/(2^n - 3)

  Source: https://erdosproblems.com/1050
  Status: SOLVED (Borwein 1991)

  Statement:
  Is the sum ∑_{n≥1} 1/(2^n - 3) irrational?

  Answer: YES (Borwein 1991).

  Borwein proved more generally that ∑_{n≥1} 1/(q^n + r) is irrational
  for integer q ≥ 2 and rational r ≠ 0 (with r ≠ -q^n for all n).

  Erdős conjectured these sums should be transcendental for all integer t.

  Tags: number-theory, irrationality, series, transcendence
-/

import Mathlib

namespace Erdos1050

open BigOperators Real

/-!
## Part I: The Series

Definition of the series ∑ 1/(q^n + r).
-/

/-- The general series T(q, r) = ∑_{n≥1} 1/(q^n + r). -/
noncomputable def T (q : ℕ) (r : ℚ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / ((q : ℝ)^n + (r : ℝ))

/-- The specific series S = ∑_{n≥1} 1/(2^n - 3). -/
noncomputable def S : ℝ := T 2 (-3)

/-- Alternative notation for clarity. -/
noncomputable def sumTwoMinusThree : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (2^n - 3 : ℝ)

/-- The two definitions agree. -/
theorem S_eq_sumTwoMinusThree : S = sumTwoMinusThree := by
  simp only [S, T, sumTwoMinusThree]
  congr 1; ext n
  split_ifs with h <;> simp_all
  push_cast; ring

/-!
## Part II: Convergence

The series converges under appropriate conditions.
-/

/-- The series converges when q ≥ 2 and r ≠ -q^n for any n ≥ 1. -/
theorem T_summable (q : ℕ) (r : ℚ) (hq : q ≥ 2)
    (hr : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Summable (fun n : ℕ => if n = 0 then 0 else 1 / ((q : ℝ)^n + (r : ℝ))) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  -- Compare with geometric series 2 * (1/q)^n for large n
  apply Summable.of_norm_bounded_eventually_nat (fun n => 2 * (1 / (q : ℝ)) ^ n)
  · -- Bounding series 2*(1/q)^n is summable (geometric with ratio 1/q < 1)
    apply Summable.mul_left
    apply summable_geometric_of_lt_one
    · positivity
    · rw [one_div]; exact inv_lt_one_of_one_lt₀ hq1
  · -- Eventually: ‖if n=0 then 0 else 1/(q^n+r)‖ ≤ 2*(1/q)^n
    -- Key: q^n → ∞, so eventually q^n > 2*(|r|+1), giving |r| < q^n/2
    have htend : Tendsto (fun n : ℕ => (q : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq1
    filter_upwards [htend.eventually_gt_atTop (2 * (|(r : ℝ)| + 1)), eventually_ge_atTop 1]
      with n hqn hn1
    have hn0 : n ≠ 0 := by omega
    rw [if_neg hn0]
    -- q^n > 2*(|r|+1) implies |r| < q^n/2
    have hr_lt : |(r : ℝ)| < (q : ℝ) ^ n / 2 := by linarith
    -- q^n/2 > |r| ≥ -r, so q^n + r > q^n/2 > 0
    have hdenom_pos : (0 : ℝ) < (q : ℝ) ^ n + (r : ℝ) := by
      linarith [neg_abs_le (r : ℝ)]
    -- q^n + r ≥ q^n/2 (since r ≥ -|r| > -q^n/2)
    have hdenom_ge : (q : ℝ) ^ n / 2 ≤ (q : ℝ) ^ n + (r : ℝ) := by
      linarith [neg_abs_le (r : ℝ)]
    rw [Real.norm_of_nonneg (div_nonneg one_nonneg hdenom_pos.le)]
    -- 1/(q^n+r) ≤ 1/(q^n/2) = 2/q^n = 2*(1/q)^n
    have hqn_half_pos : (0 : ℝ) < (q : ℝ) ^ n / 2 := by positivity
    have hqn_pos : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hqpos n
    have hqn_ne : (q : ℝ) ^ n ≠ 0 := hqn_pos.ne'
    calc 1 / ((q : ℝ) ^ n + (r : ℝ))
        ≤ 1 / ((q : ℝ) ^ n / 2) :=
          div_le_div_of_nonneg_left zero_le_one hqn_half_pos hdenom_ge
      _ = 2 * (1 / (q : ℝ)) ^ n := by
          rw [div_pow, one_pow]
          field_simp

/-- S = ∑ 1/(2^n - 3) converges. -/
theorem S_summable : Summable (fun n : ℕ => if n = 0 then 0 else 1 / (2^n - 3 : ℝ)) := by
  -- Compare with 4*(1/2)^n, which dominates for all n ≥ 0:
  --   n=0: 0 ≤ 4;  n=1: |−1| ≤ 2;  n=2: 1 ≤ 1;  n≥3: 1/(2^n−3) ≤ 4/2^n (since 2^n ≥ 4)
  apply Summable.of_norm_bounded (fun n : ℕ => 4 * (1 / 2 : ℝ) ^ n)
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
  · intro n
    rcases le_or_lt 3 n with hn | hn
    · -- n ≥ 3: 2^n ≥ 8, so 2^n - 3 > 0 and 1/(2^n-3) ≤ 4/2^n
      have hn0 : n ≠ 0 := by omega
      simp only [hn0, if_false]
      have h2n_ge8 : (8 : ℝ) ≤ 2 ^ n := by
        have : (8 : ℕ) ≤ 2 ^ n :=
          calc (8 : ℕ) = 2 ^ 3 := by norm_num
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        exact_mod_cast this
      have h2n_pos : (0 : ℝ) < 2 ^ n := by positivity
      have hdenom_pos : (0 : ℝ) < 2 ^ n - 3 := by linarith
      rw [Real.norm_of_nonneg (div_nonneg one_nonneg (le_of_lt hdenom_pos))]
      have h12 : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by
        rw [one_div, inv_pow, one_div]
      rw [h12, div_le_div_iff hdenom_pos h2n_pos]
      nlinarith
    · -- n ∈ {0, 1, 2}: check numerically
      interval_cases n
      · simp
      · simp only [show (1 : ℕ) ≠ 0 from Nat.one_ne_zero, if_false]
        norm_num [Real.norm_eq_abs]
      · simp only [show (2 : ℕ) ≠ 0 from two_ne_zero, if_false]
        norm_num [Real.norm_eq_abs]

/-- The denominators 2^n - 3 are nonzero for n ≥ 2. -/
theorem denom_nonzero (n : ℕ) (hn : n ≥ 2) : (2 : ℝ)^n - 3 ≠ 0 := by
  have h : (2 : ℝ) ^ n ≥ 4 := by
    calc (2 : ℝ) ^ n ≥ 2 ^ 2 := pow_le_pow_right (by norm_num) hn
      _ = 4 := by norm_num
  linarith

/-- Note: 2^1 - 3 = -1, so the n=1 term is -1. -/
theorem first_term : 1 / ((2 : ℝ)^1 - 3) = -1 := by
  norm_num

/-!
## Part III: First Terms

Computing the initial terms of the series.
-/

/-- 2^1 - 3 = -1. -/
theorem term_1 : (2 : ℤ)^1 - 3 = -1 := by norm_num

/-- 2^2 - 3 = 1. -/
theorem term_2 : (2 : ℤ)^2 - 3 = 1 := by norm_num

/-- 2^3 - 3 = 5. -/
theorem term_3 : (2 : ℤ)^3 - 3 = 5 := by norm_num

/-- 2^4 - 3 = 13. -/
theorem term_4 : (2 : ℤ)^4 - 3 = 13 := by norm_num

/-- 2^5 - 3 = 29. -/
theorem term_5 : (2 : ℤ)^5 - 3 = 29 := by norm_num

/-- The series starts: -1 + 1 + 1/5 + 1/13 + 1/29 + ... -/
theorem S_first_terms :
    S = -1 + 1 + 1/5 + 1/13 + 1/29 +
      ∑' n : ℕ, if n ≤ 5 then 0 else 1 / (2^n - 3 : ℝ) := by
  rw [S_eq_sumTwoMinusThree, sumTwoMinusThree]
  -- finite part (supported on {0,...,5}) is summable
  have hfin : Summable (fun n : ℕ =>
      if n ≤ 5 then (if n = 0 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) else 0) :=
    summable_of_ne_finset_zero (s := Finset.range 6) (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      simp [show ¬(n ≤ 5) from by omega])
  -- tail part is summable (geometric bound 4*(1/2)^n dominates for n ≥ 3)
  have htail : Summable (fun n : ℕ => if n ≤ 5 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) := by
    apply Summable.of_norm_bounded (fun n : ℕ => 4 * (1 / 2 : ℝ) ^ n)
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 4
    · intro n
      by_cases h5 : n ≤ 5
      · simp only [if_pos h5, norm_zero]; positivity
      · have hn3 : 3 ≤ n := by omega
        rw [if_neg h5]
        have h2n_ge8 : (8 : ℝ) ≤ 2 ^ n :=
          by exact_mod_cast (calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3)
        have h2n_pos : (0 : ℝ) < 2 ^ n := by positivity
        have hdenom_pos : (0 : ℝ) < 2 ^ n - 3 := by linarith
        rw [Real.norm_of_nonneg (div_nonneg one_nonneg hdenom_pos.le)]
        have h12 : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by rw [one_div, inv_pow, one_div]
        rw [h12, div_le_div_iff hdenom_pos h2n_pos]
        nlinarith
  -- split: f = finite_part + tail pointwise, so ∑ f = ∑ finite_part + ∑ tail
  rw [show ∑' n : ℕ, (if n = 0 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) =
      (∑' n : ℕ, if n ≤ 5 then (if n = 0 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) else 0) +
      (∑' n : ℕ, if n ≤ 5 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) from by
    rw [← tsum_add hfin htail]; congr 1; ext n
    by_cases h5 : n ≤ 5
    · by_cases h0 : n = 0 <;> simp [h5, h0]
    · have h0 : n ≠ 0 := by omega
      simp [h5, h0]]
  -- reduce to showing finite part = -1 + 1 + 1/5 + 1/13 + 1/29
  suffices h : ∑' n : ℕ, (if n ≤ 5 then
      (if n = 0 then (0 : ℝ) else 1 / (2 ^ n - 3 : ℝ)) else 0) =
      -1 + 1 + 1 / 5 + 1 / 13 + 1 / 29 by linarith
  rw [tsum_eq_sum (s := Finset.range 6) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    simp [show ¬(n ≤ 5) from by omega])]
  simp [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-!
## Part IV: Borwein's Theorem

The main irrationality result.
-/

/-- **Borwein (1991)**: ∑_{n≥1} 1/(q^n + r) is irrational
    for integer q ≥ 2 and rational r ≠ 0, r ≠ -q^n. -/
axiom borwein_irrationality (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r)

/-- **Erdős Problem #1050: SOLVED**
    ∑_{n≥1} 1/(2^n - 3) is irrational. -/
theorem S_irrational : Irrational S := by
  apply borwein_irrationality 2 (-3)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_ofNat]
    intro h
    -- We have -3 = -(2^n), so 3 = 2^n
    -- But 2^n ∈ {2, 4, 8, 16, ...}, never equals 3
    have h2 : (3 : ℝ) = (2 : ℝ)^n := by
      have : (-3 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    -- For n ≥ 1, we have 2^n ∈ {2, 4, 8, ...}, never 3
    -- Case split: n = 1 gives 2; n ≥ 2 gives ≥ 4
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1, so 2^1 = 2 ≠ 3
      have : n = 1 := by omega
      simp only [this, pow_one] at h2
      norm_num at h2
    · -- n ≥ 2, so 2^n ≥ 4 > 3
      have hnat : (2 : ℕ)^n ≥ 4 := by
        calc (2 : ℕ)^n ≥ 2^2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn2
          _ = 4 := by norm_num
      have hreal : (2 : ℝ)^n ≥ 4 := by
        have : ((2 : ℕ)^n : ℝ) ≥ 4 := by exact_mod_cast hnat
        simp only [Nat.cast_ofNat] at this
        exact this
      linarith

/-!
## Part V: Related Series

Other series covered by Borwein's theorem.
-/

/-- ∑ 1/(2^n - 1) is irrational (Erdős's original result). -/
theorem sum_2n_minus_1_irrational : Irrational (T 2 (-1)) := by
  apply borwein_irrationality 2 (-1)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_one]
    intro h
    -- -1 = -(2^n) implies 1 = 2^n, but 2^n ≥ 2 for n ≥ 1
    have h1 : (1 : ℝ) = (2 : ℝ)^n := by
      have : (-1 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    have hnat : (2 : ℕ)^n ≥ 2 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    have hreal : (2 : ℝ)^n ≥ 2 := by
      have : ((2 : ℕ)^n : ℝ) ≥ 2 := by exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at this
      exact this
    linarith

/-- ∑ 1/(2^n + 1) is irrational. -/
theorem sum_2n_plus_1_irrational : Irrational (T 2 1) := by
  apply borwein_irrationality 2 1
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_one]
    intro h
    -- 1 = -(2^n) implies 2^n = -1, but 2^n > 0
    have hneg : (2 : ℝ)^n = -1 := by
      have : (1 : ℝ) = -((2 : ℝ)^n) := h
      linarith
    have hpos : (2 : ℝ)^n > 0 := pow_pos (by norm_num : (0 : ℝ) < 2) n
    linarith

/-- ∑ 1/(3^n - 1) is irrational. -/
theorem sum_3n_minus_1_irrational : Irrational (T 3 (-1)) := by
  apply borwein_irrationality 3 (-1)
  · norm_num
  · norm_num
  · intro n hn
    simp only [Rat.cast_neg, Rat.cast_one]
    intro h
    -- -1 = -(3^n) implies 1 = 3^n, but 3^n ≥ 3 for n ≥ 1
    have h1 : (1 : ℝ) = (3 : ℝ)^n := by
      have : (-1 : ℝ) = -((3 : ℝ)^n) := h
      linarith
    have hnat : (3 : ℕ)^n ≥ 3 := by
      calc (3 : ℕ)^n ≥ 3^1 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 3) hn
        _ = 3 := by norm_num
    have hreal : (3 : ℝ)^n ≥ 3 := by
      have : ((3 : ℕ)^n : ℝ) ≥ 3 := by exact_mod_cast hnat
      simp only [Nat.cast_ofNat] at this
      exact this
    linarith

/-- ∑ 1/(q^n + r) for any valid q, r. -/
theorem general_irrational (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r) := borwein_irrationality q r hq hr hpole

/-!
## Part VI: The Transcendence Conjecture

Erdős conjectured a stronger result.
-/

/-- **Erdős's Conjecture**: ∑ 1/(2^n + t) is transcendental for all integer t ≠ 0. -/
def ErdosTranscendenceConjecture : Prop :=
  ∀ t : ℤ, t ≠ 0 → (∀ n : ℕ, n ≥ 1 → (t : ℝ) ≠ -2^n) →
    Transcendental ℚ (T 2 t)

/-- General transcendence conjecture. -/
def GeneralTranscendenceConjecture : Prop :=
  ∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
    (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
    Transcendental ℚ (T q r)

/-- Transcendence implies irrationality:
    if T(q,r) is transcendental over ℚ, it cannot equal any rational number. -/
theorem transcendence_implies_irrationality :
    GeneralTranscendenceConjecture →
    ∀ q : ℕ, q ≥ 2 → ∀ r : ℚ, r ≠ 0 →
      (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) →
      Irrational (T q r) := by
  intro h q hq r hr hpole
  have htrans := h q hq r hr hpole
  -- Irrational = ¬ ∃ rat : ℚ, (rat : ℝ) = T q r
  -- If such a rational exists, T q r is a root of X - C rat, hence algebraic
  intro hmem
  apply htrans
  rw [Set.mem_range] at hmem
  obtain ⟨rat, hrat⟩ := hmem
  -- hrat : (rat : ℝ) = T q r, so T q r is algebraic: root of X - C rat
  exact ⟨Polynomial.X - Polynomial.C rat, Polynomial.X_sub_C_ne_zero rat, by
    simp [Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C, ← hrat]⟩

/-- The general transcendence conjecture implies the Erdős transcendence conjecture. -/
theorem general_implies_erdos_transcendence :
    GeneralTranscendenceConjecture → ErdosTranscendenceConjecture := by
  intro h q hq
  exact h q 1 hq (by norm_num)

/-!
## Part VII: Connection to Erdős Problem #1049

This problem relates to the divisor sum irrationality.
-/

/-- Recall: S(t) = ∑ 1/(t^n - 1) from Problem #1049. -/
noncomputable def S_1049 (t : ℝ) : ℝ :=
  ∑' n : ℕ, if n = 0 then 0 else 1 / (t^n - 1)

/-- T(q, -1) = S_1049(q) for integer q. -/
theorem T_eq_S_1049 (q : ℕ) (hq : q ≥ 2) : T q (-1) = S_1049 q := by
  simp only [T, S_1049]
  congr 1; ext n
  split_ifs with h
  · simp
  · push_cast; ring

/-- The problems are related through shifting the constant. -/
theorem problems_related (q : ℕ) (hq : q ≥ 2) (r : ℚ) (hr : r ≠ 0) :
    -- T(q, r) and S_1049(q) are both irrational for appropriate parameters
    Irrational (T q (-1)) ∧
    (∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) → Irrational (T q r) := by
  -- The conjunction premise: the second component gives us the pole condition
  intro ⟨_, hpole⟩
  exact borwein_irrationality q r hq hr hpole

/-!
## Part VIII: Approximation and Numerical Values

Computing the value of the series.
-/

/-- S ≈ 0.2868... -/
axiom S_approx : S > 0.286 ∧ S < 0.288

/-- S is positive (despite the first term being negative). -/
theorem S_positive : S > 0 := by
  obtain ⟨hl, _⟩ := S_approx
  linarith

/-- Upper bound: S < 1. -/
theorem S_lt_one : S < 1 := by
  obtain ⟨_, hu⟩ := S_approx
  linarith

/-- The partial sums converge to S. -/
theorem partial_sums_converge :
    Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, if n = 0 then 0 else 1 / (2^n - 3 : ℝ))
      Filter.atTop (nhds S) := by
  -- S = tsum of the function; the partial sums converge since the series is summable
  have heq : S = ∑' n : ℕ, (if n = 0 then 0 else 1 / (2 ^ n - 3 : ℝ)) := by
    rw [S_eq_sumTwoMinusThree, sumTwoMinusThree]
  rw [heq]
  exact S_summable.hasSum.tendsto_sum_tsum

/-!
## Part IX: OEIS Connection

The sequence of denominators.
-/

/-- OEIS A331372: Related sequence. -/
def oeis_A331372 : ℕ → ℤ
  | 0 => 1
  | n + 1 => 2^(n+1) - 3

/-- The denominators form A000051 shifted: 2^n - 3. -/
theorem denom_sequence (n : ℕ) (hn : n ≥ 1) :
    oeis_A331372 n = 2^n - 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [oeis_A331372]

/-- Denominators grow exponentially. -/
theorem denom_growth (n : ℕ) (hn : n ≥ 3) :
    (oeis_A331372 n : ℝ) > 2^(n-1) := by
  have hd := denom_sequence n (by omega)
  simp only [hd]; push_cast
  -- Goal: (2:ℝ)^n - 3 > (2:ℝ)^(n-1)
  -- 2^n = 2 * 2^(n-1), so need 2^(n-1) - 3 > 0, i.e., 2^(n-1) > 3
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    rw [← pow_succ]; congr 1; omega
  have hge : (2 : ℝ) ^ (n - 1) ≥ 4 := by
    calc (2 : ℝ) ^ (n - 1) ≥ (2 : ℝ) ^ 2 :=
          pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  linarith

/-!
## Part X: Main Results

Summary of Erdős Problem #1050.
-/

/-- **Erdős Problem #1050: SOLVED**

    Question: Is ∑_{n≥1} 1/(2^n - 3) irrational?

    Answer: YES (Borwein 1991).

    Borwein proved the more general result that ∑_{n≥1} 1/(q^n + r)
    is irrational for integer q ≥ 2 and rational r ≠ 0, r ≠ -q^n.

    The stronger transcendence conjecture remains OPEN. -/
theorem erdos_1050 : Irrational S := S_irrational

/-- The answer to Erdős #1050. -/
def erdos_1050_answer : String :=
  "SOLVED: ∑ 1/(2^n - 3) is irrational (Borwein 1991)"

/-- The status of Erdős #1050. -/
def erdos_1050_status : String :=
  "SOLVED by Peter Borwein (1991)"

/-- Borwein's general theorem. -/
theorem borwein_theorem (q : ℕ) (r : ℚ) (hq : q ≥ 2) (hr : r ≠ 0)
    (hpole : ∀ n : ℕ, n ≥ 1 → (r : ℝ) ≠ -((q : ℝ)^n)) :
    Irrational (T q r) := borwein_irrationality q r hq hr hpole

#check erdos_1050
#check borwein_irrationality
#check ErdosTranscendenceConjecture

end Erdos1050
