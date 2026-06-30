import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-
# Finite Geometric Sums and the Infinite Limit: Bounds and Monotonicity

## What This Proves

For a real ratio `r` the finite geometric partial sum

  `S n = ∑_{k=0}^{n-1} r^k`

has the textbook closed form `(1 - r^n)/(1 - r)` when `r ≠ 1`
(`geometric_sum_closed`). The base gallery entry `GeometricSeries.lean`
already records that closed form and, separately, the infinite value
`∑' k, r^k = (1 - r)⁻¹` for `|r| < 1`. What it does **not** make explicit is
the quantitative bridge between the two: *how the finite sums approach the
infinite limit*.

This entry fills that gap for `0 ≤ r < 1`:

* `geometric_sum_tail` — the exact defect `(1 - r)⁻¹ - S n = r^n / (1 - r)`,
  i.e. the infinite tail is itself a scaled geometric power.
* `geometric_sum_lt_inv` — every finite sum is **strictly** below the limit,
  `S n < (1 - r)⁻¹` (for `0 < r < 1`).
* `geometric_sum_le_inv` — the non-strict bound `S n ≤ (1 - r)⁻¹`, valid for
  all `n` including `n = 0`, and for `r = 0`.
* `geometric_sum_monotone` — the partial sums increase in `n`.
* `geometric_sum_tendsto_inv` — they converge upward to `(1 - r)⁻¹`.

Together these say the finite geometric sums form a bounded increasing sequence
converging to the infinite value, with an explicit error term `r^n/(1-r)`.

## Why This Matters

The error term `r^n/(1-r)` is exactly the estimate used whenever a geometric
series is truncated (numerical analysis, generating functions, the comparison
test, the ratio-test remainder). Stating it as a typed identity — rather than
re-deriving it inline each time — makes the finite/infinite relationship
reusable.

## Mathlib Relationship

The closed form `geom_sum_eq` and the infinite value
`tsum_geometric_of_lt_one` are Mathlib. The defect identity, the strict and
non-strict bounds, the monotonicity statement, and the explicit upward
convergence are assembled here; they are not single Mathlib lemmas.
-/

namespace GeometricSeriesOQ08

open Finset

variable {r : ℝ}

/-- **Closed form** in the `(1 - rⁿ)/(1 - r)` convention.
Wraps Mathlib's `geom_sum_eq` (which uses `(rⁿ - 1)/(r - 1)`). -/
theorem geometric_sum_closed (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, r ^ k = (1 - r ^ n) / (1 - r) := by
  rw [geom_sum_eq hr]
  rw [div_eq_div_iff (sub_ne_zero.mpr hr) (sub_ne_zero.mpr (fun h => hr h.symm))]
  ring

/-- **Exact truncation defect.** For `r < 1` the gap between the infinite value
`(1 - r)⁻¹` and the `n`-term partial sum is the scaled power `rⁿ / (1 - r)`. -/
theorem geometric_sum_tail (hr : r < 1) (n : ℕ) :
    (1 - r)⁻¹ - ∑ k ∈ range n, r ^ k = r ^ n / (1 - r) := by
  have h1r : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (ne_of_gt hr)
  rw [geometric_sum_closed (ne_of_lt hr) n]
  field_simp
  ring

/-- **Non-strict bound.** For `0 ≤ r < 1`, every finite geometric sum is at most
the infinite value `(1 - r)⁻¹`. Holds for all `n` (including `n = 0`). -/
theorem geometric_sum_le_inv (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ range n, r ^ k ≤ (1 - r)⁻¹ := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have htail : (1 - r)⁻¹ - ∑ k ∈ range n, r ^ k = r ^ n / (1 - r) :=
    geometric_sum_tail hr1 n
  have hnonneg : 0 ≤ r ^ n / (1 - r) :=
    div_nonneg (pow_nonneg hr0 n) (le_of_lt h1r)
  linarith [htail ▸ hnonneg]

/-- **Strict bound.** For `0 < r < 1`, every finite geometric sum is *strictly*
below the infinite value `(1 - r)⁻¹` (the missing tail is positive). -/
theorem geometric_sum_lt_inv (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ range n, r ^ k < (1 - r)⁻¹ := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  have htail : (1 - r)⁻¹ - ∑ k ∈ range n, r ^ k = r ^ n / (1 - r) :=
    geometric_sum_tail hr1 n
  have hpos : 0 < r ^ n / (1 - r) := div_pos (pow_pos hr0 n) h1r
  linarith [htail ▸ hpos]

/-- **Monotonicity.** For `0 ≤ r` the partial sums increase in `n`
(each new term `rⁿ` is nonnegative). -/
theorem geometric_sum_monotone (hr0 : 0 ≤ r) :
    Monotone (fun n => ∑ k ∈ range n, r ^ k) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Finset.sum_range_succ]
  have : 0 ≤ r ^ n := pow_nonneg hr0 n
  linarith

/-- **Upward convergence.** For `0 ≤ r < 1` the finite geometric sums converge to
the infinite value `(1 - r)⁻¹`. Combined with `geometric_sum_monotone` and
`geometric_sum_le_inv`, this exhibits `(1 - r)⁻¹` as the supremum of an
increasing, bounded sequence. -/
theorem geometric_sum_tendsto_inv (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun n => ∑ k ∈ range n, r ^ k) Filter.atTop
      (nhds (1 - r)⁻¹) := by
  have habs : |r| < 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have hsum := hasSum_geometric_of_abs_lt_one habs
  simpa using hsum.tendsto_sum_nat

/-! ## Concrete instance

`r = 1/2`: the four-term sum is `15/8`, strictly below the limit `2`,
with truncation defect `(1/2)^4 / (1 - 1/2) = 1/8`. -/

example : ∑ k ∈ range 4, (1 / 2 : ℝ) ^ k = 15 / 8 := by norm_num [Finset.sum_range_succ]

example : (1 - (1 / 2 : ℝ))⁻¹ - ∑ k ∈ range 4, (1 / 2 : ℝ) ^ k = 1 / 8 := by
  rw [geometric_sum_tail (by norm_num) 4]; norm_num

example : ∑ k ∈ range 4, (1 / 2 : ℝ) ^ k < (1 - (1 / 2 : ℝ))⁻¹ :=
  geometric_sum_lt_inv (by norm_num) (by norm_num) 4

end GeometricSeriesOQ08
