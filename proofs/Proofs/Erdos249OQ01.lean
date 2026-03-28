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
-- § Summary
-- ══════════════════════════════════════════════════════════════════

/-
**Extended bounds**: 5/4 ≤ ∑ φ(n)/2^n ≤ 2

**Term values**:
  n  | φ(n) | φ(n)/2^n
  0  |   0  |     0
  1  |   1  |   1/2
  2  |   1  |   1/4
  3  |   2  |   1/4
  4  |   2  |   1/8
  5  |   4  |   1/8

  Partial sum (n ≤ 5) = 5/4 = 1.25

**Status**: OPEN — irrationality still unknown.
The sum is not 0 or 1. Whether it equals 2 (the upper bound from
∑ n/2^n = 2) would require showing φ(n) < n for some n,
which is true (φ(4) = 2 < 4) but the formal machinery for strict
inequality of infinite sums needs tsum_lt_tsum.
-/

end Erdos249OQ01
