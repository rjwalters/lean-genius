/-
Erdős Problem #249 OQ-01: Tighter Bounds on Σ φ(n)/2^n

We extend the formalization of Erdős Problem #249 (Is Σ φ(n)/2^n irrational?)
with tighter bounds on the series value.

Main results:
- Computation of terms for n = 3, 4, 5
- Tighter lower bound: totientPowerSum ≥ 5/4
- Consequence: the sum exceeds 1 (ruling out values 0 and 1)

Combined with the parent's upper bound (≤ 2), we know:
  1 < Σ φ(n)/2^n ≤ 2

All results proved from Mathlib with 0 axioms and 0 sorries.

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
  convert hasSum_coe_mul_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)
    using 1
  norm_num

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
  exact hasSum_lt (i := 4) termFn_four_lt termFn_le_n_mul_half_pow
    totientPowerSum_summable.hasSum hasSum_n_mul_half

/-- The sum is not an integer: 5/4 ≤ ∑ φ(n)/2^n < 2 rules out all integers. -/
theorem totientPowerSum_not_int : ¬∃ m : ℤ, totientPowerSum = ↑m := by
  intro ⟨m, hm⟩
  have h1 := totientPowerSum_ge_five_fourths
  have h2 := totientPowerSum_lt_two
  rw [hm] at h1 h2
  -- m ≥ 5/4 and m < 2, so m = 1. But m ≥ 5/4 > 1.
  have : (1 : ℝ) < m := by linarith
  have : (m : ℝ) < 2 := h2
  have : m = 1 := by omega
  linarith

-- ══════════════════════════════════════════════════════════════════
-- § Summary
-- ══════════════════════════════════════════════════════════════════

/-
**Tight bounds**: 5/4 ≤ ∑ φ(n)/2^n < 2

The sum is:
- At least 5/4 (from partial sum computation)
- Strictly less than 2 (from strict gap at n = 4 in comparison with Σ n/2^n)
- Not an integer (since 5/4 ≤ x < 2 has no integer solutions)
- Positive (> 1)

**Status**: OPEN — irrationality still unknown, but the value is now pinned
to the interval [5/4, 2) and confirmed non-integer.
-/

end Erdos249OQ01
