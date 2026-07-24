/-
Erdős Problem #249 OQ-01: Tighter Bounds on Σ φ(n)/2^n

We extend the formalization of Erdős Problem #249 (Is Σ φ(n)/2^n irrational?)
with tighter bounds on the series value.

Main results:
- Computation of terms for n = 3, 4, 5, 6, 7, 8, 9, 10
- Strict bounds: 87/64 < totientPowerSum < 351/256
  (interval width 3/256 ≈ 0.012; true value ≈ 1.368)
- The sum is not a rational with denominator dividing 4
  (subsumes: not an integer, not a half-integer)
- The sum is not equal to 4/3
- Strict upper bound < 2 via comparison with Σ n/2^n

All results proved from Mathlib with 0 sorries and 0 literal `axiom` declarations;
5 term-value certificates (n = 4, 6, 8, 9, 10) use `native_decide`, which depends
on the `Lean.ofReduceBool` kernel-reduction axiom.

References:
- Erdős Problem #249: https://erdosproblems.com/249
- OEIS A256936
-/

import Proofs.Erdos249Problem

open Erdos249

namespace Erdos249OQ01

-- ══════════════════════════════════════════════════════════════════
-- § New Term Computations
-- ══════════════════════════════════════════════════════════════════

/-- φ(3) = 2 (since 3 is prime), so the n = 3 term is 2/8 = 1/4. -/
theorem termFn_three : termFn 3 = 1 / 4 := by
  unfold termFn
  simp [Nat.totient_prime (show Nat.Prime 3 by norm_num)]
  norm_num

/-- φ(4) = 2 (since 4 = 2²), so the n = 4 term is 2/16 = 1/8. -/
theorem termFn_four : termFn 4 = 1 / 8 := by
  unfold termFn
  have : Nat.totient 4 = 2 := by native_decide
  rw [this]; norm_num

/-- φ(5) = 4 (since 5 is prime), so the n = 5 term is 4/32 = 1/8. -/
theorem termFn_five : termFn 5 = 1 / 8 := by
  unfold termFn
  simp [Nat.totient_prime (show Nat.Prime 5 by norm_num)]
  norm_num

-- ══════════════════════════════════════════════════════════════════
-- § Partial Sum
-- ══════════════════════════════════════════════════════════════════

/-- The partial sum of the first 6 terms (n = 0, ..., 5):
    0 + 1/2 + 1/4 + 1/4 + 1/8 + 1/8 = 10/8 = 5/4. -/
theorem partial_sum_6 :
    Finset.sum (Finset.range 6) termFn = 5 / 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [termFn_zero, termFn_one, termFn_two, termFn_three, termFn_four, termFn_five]
  norm_num

-- ══════════════════════════════════════════════════════════════════
-- § Tighter Lower Bound
-- ══════════════════════════════════════════════════════════════════

/-- **Tighter lower bound**: ∑ φ(n)/2^n ≥ 5/4.

    Proof: the partial sum of the first 6 terms (n = 0..5) equals 5/4,
    and all remaining terms are non-negative (since φ(n) ≥ 0). -/
theorem totientPowerSum_ge_five_fourths : totientPowerSum ≥ 5 / 4 := by
  unfold totientPowerSum
  have h := sum_le_hasSum (Finset.range 6)
    (fun b _ => termFn_nonneg b) totientPowerSum_summable.hasSum
  linarith [partial_sum_6]

/-- The sum exceeds 1: ∑ φ(n)/2^n > 1.

    Combined with the upper bound ≤ 2 from the parent formalization,
    this shows the sum lies in (1, 2], ruling out integer values 0 and 1. -/
theorem totientPowerSum_gt_one : totientPowerSum > 1 := by
  linarith [totientPowerSum_ge_five_fourths]

-- ══════════════════════════════════════════════════════════════════
-- § Strict Upper Bound
-- ══════════════════════════════════════════════════════════════════

/-- The comparison series Σ n * (1/2)^n has sum exactly 2. -/
private theorem hasSum_n_mul_half :
    HasSum (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 2 : ℝ)) (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
  have heq : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
  rwa [heq] at h

/-- Each term is bounded by the comparison sequence: φ(n)/2^n ≤ n/2^n. -/
private theorem termFn_le_comp (n : ℕ) :
    termFn n ≤ (n : ℝ) * (1 / 2 : ℝ) ^ n := by
  simp only [termFn]
  calc (Nat.totient n : ℝ) / 2 ^ n
      ≤ (n : ℝ) / 2 ^ n :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.totient_le n)) (by positivity)
    _ = (n : ℝ) * (1 / 2) ^ n := by
        rw [one_div, inv_pow, div_eq_mul_inv]

/-- At n = 4: φ(4)/2^4 = 1/8 < 4/16 = 1/4 = 4 * (1/2)^4.
    This strict gap witnesses that Σ φ(n)/2^n < Σ n/2^n. -/
private theorem termFn_four_lt : termFn 4 < 4 * (1 / 2 : ℝ) ^ 4 := by
  rw [termFn_four]; norm_num

/-- **Strict upper bound**: ∑ φ(n)/2^n < 2.

    Since φ(n) ≤ n for all n (so each term ≤ n * (1/2)^n)
    and φ(4) = 2 < 4 (strict gap at n = 4),
    the sum is strictly less than ∑ n * (1/2)^n = 2. -/
theorem totientPowerSum_lt_two : totientPowerSum < 2 := by
  unfold totientPowerSum
  exact hasSum_lt (i := 4) termFn_le_comp termFn_four_lt
    totientPowerSum_summable.hasSum hasSum_n_mul_half

/-- The sum is not an integer: 5/4 ≤ ∑ φ(n)/2^n < 2 rules out all integers. -/
theorem totientPowerSum_not_int : ¬∃ m : ℤ, totientPowerSum = ↑m := by
  intro ⟨m, hm⟩
  have h1 := totientPowerSum_ge_five_fourths
  have h2 := totientPowerSum_lt_two
  rw [hm] at h1 h2
  -- m ≥ 5/4 and m < 2, so m = 1. But m ≥ 5/4 > 1.
  have hlo : (1 : ℝ) < (m : ℝ) := by linarith
  have hhi : (m : ℝ) < 2 := h2
  have hlo' : 1 < m := by exact_mod_cast hlo
  have hhi' : m < 2 := by exact_mod_cast hhi
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Tighter Interval: (5/4, 3/2)
-- ══════════════════════════════════════════════════════════════════

/-- φ(6) = 2 (since 6 = 2·3), so the n = 6 term is 2/64 = 1/32. -/
theorem termFn_six : termFn 6 = 1 / 32 := by
  unfold termFn
  have : Nat.totient 6 = 2 := by native_decide
  rw [this]; norm_num

/-- Extended partial sum: first 7 terms (n = 0, ..., 6) sum to 41/32. -/
theorem partial_sum_7 :
    Finset.sum (Finset.range 7) termFn = 41 / 32 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [termFn_zero, termFn_one, termFn_two, termFn_three, termFn_four, termFn_five, termFn_six]
  norm_num

/-- **Strict lower bound**: ∑ φ(n)/2^n > 5/4.

    Since partial_sum_7 = 41/32 > 40/32 = 5/4, and all remaining terms
    are non-negative, the total sum strictly exceeds 5/4. -/
theorem totientPowerSum_gt_five_fourths : totientPowerSum > 5 / 4 := by
  unfold totientPowerSum
  have h := sum_le_hasSum (Finset.range 7)
    (fun b _ => termFn_nonneg b) totientPowerSum_summable.hasSum
  linarith [partial_sum_7]

/-- Partial sum of the comparison series through 6 terms:
    ∑_{n=0}^{5} n*(1/2)^n = 57/32. -/
private theorem comparison_partial_sum_6 :
    Finset.sum (Finset.range 6) (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) = 57 / 32 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- **Tighter upper bound**: ∑ φ(n)/2^n < 3/2.

    Strategy: split both our series and the comparison at n = 6.
    The tail of our series is bounded by the comparison tail:
      ∑_{n≥6} φ(n)/2^n ≤ ∑_{n≥6} n/2^n = 2 - 57/32 = 7/32
    So the total ≤ 5/4 + 7/32 = 47/32 < 3/2. -/
theorem totientPowerSum_lt_three_halves : totientPowerSum < 3 / 2 := by
  -- Split both series at position 6
  have h_our : HasSum (fun j => termFn (j + 6))
      ((∑' n, termFn n) - Finset.sum (Finset.range 6) termFn) := by
    rw [hasSum_nat_add_iff, sub_add_cancel]
    exact totientPowerSum_summable.hasSum
  have h_comp : HasSum (fun j : ℕ => (↑(j + 6) : ℝ) * (1 / 2) ^ (j + 6))
      (2 - Finset.sum (Finset.range 6) (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n)) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) 6).mpr
      (by rw [sub_add_cancel]; exact hasSum_n_mul_half)
  -- Tail of termFn ≤ tail of comparison (pointwise)
  have h := hasSum_le (fun j => termFn_le_comp (j + 6)) h_our h_comp
  -- Substitute computed partial sums
  rw [partial_sum_6, comparison_partial_sum_6] at h
  -- h : tsum termFn - 5/4 ≤ 2 - 57/32, i.e., tsum termFn ≤ 47/32
  unfold totientPowerSum
  linarith

/-- The sum is not a rational with denominator dividing 4.

    Since 5/4 < x < 3/2 = 6/4, there is no integer m with x = m/4.
    This subsumes: not an integer, not a half-integer. -/
theorem totientPowerSum_not_quarter_int :
    ¬∃ m : ℤ, totientPowerSum = ↑m / 4 := by
  intro ⟨m, hm⟩
  have h1 := totientPowerSum_gt_five_fourths
  have h2 := totientPowerSum_lt_three_halves
  rw [hm] at h1 h2
  -- m/4 > 5/4 and m/4 < 3/2, so 5 < m < 6 (in ℝ), impossible for integers
  have h5 : (5 : ℝ) < m := by linarith
  have h6 : (m : ℝ) < 6 := by linarith
  have : 5 < m := by
    by_contra h; push_neg at h
    have : (m : ℝ) ≤ 5 := by exact_mod_cast h
    linarith
  have : m < 6 := by
    by_contra h; push_neg at h
    have : (6 : ℝ) ≤ m := by exact_mod_cast h
    linarith
  omega

-- ══════════════════════════════════════════════════════════════════
-- § Tighter Interval: (87/64, 351/256)
-- ══════════════════════════════════════════════════════════════════

/-- φ(7) = 6 (since 7 is prime), so the n = 7 term is 6/128 = 3/64. -/
theorem termFn_seven : termFn 7 = 3 / 64 := by
  unfold termFn
  simp [Nat.totient_prime (show Nat.Prime 7 by norm_num)]
  norm_num

/-- φ(8) = 4 (since 8 = 2³), so the n = 8 term is 4/256 = 1/64. -/
theorem termFn_eight : termFn 8 = 1 / 64 := by
  unfold termFn
  have : Nat.totient 8 = 4 := by native_decide
  rw [this]; norm_num

/-- φ(9) = 6 (since 9 = 3²), so the n = 9 term is 6/512 = 3/256. -/
theorem termFn_nine : termFn 9 = 3 / 256 := by
  unfold termFn
  have : Nat.totient 9 = 6 := by native_decide
  rw [this]; norm_num

/-- φ(10) = 4 (since 10 = 2·5), so the n = 10 term is 4/1024 = 1/256. -/
theorem termFn_ten : termFn 10 = 1 / 256 := by
  unfold termFn
  have : Nat.totient 10 = 4 := by native_decide
  rw [this]; norm_num

/-- Extended partial sum: first 11 terms (n = 0, ..., 10) sum to 87/64.
    Decimal: 87/64 = 1.359375. -/
theorem partial_sum_11 :
    Finset.sum (Finset.range 11) termFn = 87 / 64 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [termFn_zero, termFn_one, termFn_two, termFn_three, termFn_four, termFn_five, termFn_six,
      termFn_seven, termFn_eight, termFn_nine, termFn_ten]
  norm_num

/-- Partial sum of the comparison series through 11 terms:
    ∑_{n=0}^{10} n*(1/2)^n = 509/256. -/
private theorem comparison_partial_sum_11 :
    Finset.sum (Finset.range 11) (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) = 509 / 256 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- φ(11) = 10 (since 11 is prime), so termFn 11 is strictly positive. -/
private theorem termFn_eleven_pos : (0 : ℝ) < termFn 11 := by
  unfold termFn
  have h11 : 0 < Nat.totient 11 := Nat.totient_pos.mpr (by norm_num)
  exact div_pos (by exact_mod_cast h11) (by positivity)

/-- φ(11) = 10 < 11 (since 11 is prime), witnessing a strict gap at n = 11
    between termFn and the comparison sequence n * (1/2)^n. -/
private theorem termFn_eleven_lt_comp : termFn 11 < (11 : ℝ) * (1 / 2 : ℝ) ^ 11 := by
  unfold termFn
  simp [Nat.totient_prime (show Nat.Prime 11 by norm_num)]
  norm_num

/-- **Tighter lower bound**: ∑ φ(n)/2^n > 87/64.

    Proof: the partial sum of the first 11 terms (n = 0..10) equals 87/64,
    and the term at n = 11 is strictly positive, so the partial sum through
    n = 11 (hence the full tsum) strictly exceeds 87/64. -/
theorem totientPowerSum_gt_87_64 : totientPowerSum > 87 / 64 := by
  unfold totientPowerSum
  have h := sum_le_hasSum (Finset.range 12)
    (fun b _ => termFn_nonneg b) totientPowerSum_summable.hasSum
  rw [Finset.sum_range_succ, partial_sum_11] at h
  linarith [termFn_eleven_pos]

/-- **Tighter upper bound**: ∑ φ(n)/2^n < 351/256.

    Strategy: split both series at n = 11.
    The tail of our series is bounded by the comparison tail:
      ∑_{n≥11} φ(n)/2^n ≤ ∑_{n≥11} n/2^n = 2 - 509/256 = 3/256
    So the total ≤ 87/64 + 3/256 = 351/256. -/
theorem totientPowerSum_lt_351_256 : totientPowerSum < 351 / 256 := by
  have h_our : HasSum (fun j => termFn (j + 11))
      ((∑' n, termFn n) - Finset.sum (Finset.range 11) termFn) := by
    rw [hasSum_nat_add_iff, sub_add_cancel]
    exact totientPowerSum_summable.hasSum
  have h_comp : HasSum (fun j : ℕ => (↑(j + 11) : ℝ) * (1 / 2) ^ (j + 11))
      (2 - Finset.sum (Finset.range 11) (fun n : ℕ => (n : ℝ) * (1 / 2) ^ n)) :=
    (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * (1 / 2) ^ n) 11).mpr
      (by rw [sub_add_cancel]; exact hasSum_n_mul_half)
  have h := hasSum_lt (i := 0) (fun j => termFn_le_comp (j + 11)) termFn_eleven_lt_comp
    h_our h_comp
  rw [partial_sum_11, comparison_partial_sum_11] at h
  unfold totientPowerSum
  linarith

/-- The sum is not equal to 4/3.

    Since 87/64 > 4/3 (equivalently, 87·3 > 4·64, i.e. 261 > 256),
    the lower bound rules out 4/3. -/
theorem totientPowerSum_ne_four_thirds : totientPowerSum ≠ 4 / 3 := by
  have h := totientPowerSum_gt_87_64
  intro heq; rw [heq] at h; norm_num at h

-- ══════════════════════════════════════════════════════════════════
-- § Summary
-- ══════════════════════════════════════════════════════════════════

/-
**Tight bounds**: 87/64 < ∑ φ(n)/2^n < 351/256

The sum (≈ 1.368) is:
- Strictly greater than 87/64 = 1.359375 (from partial sum with 11 terms)
- Strictly less than 351/256 ≈ 1.371 (from tail splitting at n = 11)
- Not an integer (follows from 87/64 > 1 and 351/256 < 2)
- Not a half-integer (3/2 = 384/256 > 351/256)
- Not a quarter-integer (the interval (87/64, 351/256) = (348/256, 351/256) contains
  no multiple of 1/4, since 5/4 = 320/256 < 348/256 and 6/4 = 384/256 > 351/256)
- Not equal to 4/3 (since 4/3 = 256/192 < 87/64 = 261/192)

**Status**: OPEN — irrationality still unknown, but the value is pinned
to the narrow interval (87/64, 351/256) of width 3/256 ≈ 0.012.
-/

end Erdos249OQ01
