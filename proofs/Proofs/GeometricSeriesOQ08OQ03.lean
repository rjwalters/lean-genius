import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-
# The Ico-slice of a Geometric Series and the Cauchy Criterion

## What This Proves

The parent entry `GeometricSeriesOQ08.lean` quantifies how the finite
geometric partial sums `∑_{k<n} rᵏ` approach the infinite value `(1 − r)⁻¹`,
with the exact truncation defect `rⁿ / (1 − r)`. This follow-up turns that
one-sided "head vs. limit" statement into the **two-sided slice** estimate that
the comparison and ratio tests actually invoke: a bound on an arbitrary middle
block `∑_{k ∈ Ico m n} rᵏ`.

* `geometric_slice_closed` — the closed form `(rᵐ − rⁿ)/(1 − r)` for the slice
  (a thin wrapper over Mathlib's `geom_sum_Ico'`).
* `geometric_slice_eq_tail_sub` — the **difference-of-tails identity**
  `∑_{k ∈ Ico m n} rᵏ = rᵐ/(1 − r) − rⁿ/(1 − r)`: the slice is exactly the
  parent's `m`-tail minus its `n`-tail. This is the bridge that ties the slice
  back to `GeometricSeriesOQ08.geometric_sum_tail`.
* `geometric_slice_factor` — the **self-similarity** `∑_{k ∈ Ico m n} rᵏ =
  rᵐ · ∑_{k < n − m} rᵏ`: a slice starting at `m` is `rᵐ` times a fresh
  partial sum.
* `geometric_slice_le` / `geometric_slice_abs_le` — the slice bound
  `∑_{k ∈ Ico m n} rᵏ ≤ rᵐ/(1 − r)` and its absolute-value form, valid for
  *all* `m, n` (the slice is empty, hence `0`, when `n ≤ m`).
* `geometric_slice_bound_tendsto` — the envelope `rᵐ/(1 − r) → 0`.
* `geometric_slice_cauchy` — the **Cauchy criterion**: for every `ε > 0` there
  is an `N` past which *every* block has `|∑_{k ∈ Ico m n} rᵏ| ≤ ε`,
  uniformly in the right endpoint `n`. This is the exact estimate that proves a
  geometric series Cauchy, and the template the comparison/ratio tests follow.

## Why This Matters

The truncation defect `rⁿ/(1 − r)` answers "how far is the `n`-term sum from the
limit?". The slice bound `rᵐ/(1 − r)` answers the question convergence proofs
really ask: "how large can the discarded *tail block* between steps `m` and `n`
be?" — and the answer does not depend on `n`. Packaging this as a typed Cauchy
statement (`geometric_slice_cauchy`) gives the reusable engine behind the
comparison test, the ratio-test remainder, and dominated convergence of
geometric majorants.

## Mathlib Relationship

The slice closed form (`geom_sum_Ico'`) and the raw slice bound
(`geom_sum_Ico_le_of_lt_one`) are Mathlib lemmas; they are wrapped here for the
gallery's self-containedness and clearly attributed. The genuinely assembled
content is the difference-of-tails identity, the self-similar factorisation, the
absolute-value/Cauchy packaging, and the explicit `ε`–`N` Cauchy criterion —
none of which is a single Mathlib lemma for this series.
-/

namespace GeometricSeriesOQ08OQ03

open Finset

variable {r : ℝ}

/-- **Slice closed form.** For `r ≠ 1` and `m ≤ n`, the middle block has the
closed form `(rᵐ − rⁿ)/(1 − r)`. Wraps Mathlib's `geom_sum_Ico'`. -/
theorem geometric_slice_closed (hr : r ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, r ^ k = (r ^ m - r ^ n) / (1 - r) :=
  geom_sum_Ico' hr hmn

/-- **Difference of tails.** For `r < 1` and `m ≤ n`, the slice equals the
parent's `m`-tail minus its `n`-tail:
`∑_{k ∈ Ico m n} rᵏ = rᵐ/(1 − r) − rⁿ/(1 − r)`. This is the bridge from the
two-sided slice back to `GeometricSeriesOQ08.geometric_sum_tail`. -/
theorem geometric_slice_eq_tail_sub (hr : r < 1) {m n : ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Ico m n, r ^ k = r ^ m / (1 - r) - r ^ n / (1 - r) := by
  rw [geometric_slice_closed (ne_of_lt hr) hmn, sub_div]

/-- **Self-similarity.** A slice starting at `m` is `rᵐ` times a fresh partial
sum: `∑_{k ∈ Ico m n} rᵏ = rᵐ · ∑_{k < n − m} rᵏ`. Holds for all `m, n`. -/
theorem geometric_slice_factor (m n : ℕ) :
    ∑ k ∈ Ico m n, r ^ k = r ^ m * ∑ k ∈ range (n - m), r ^ k := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [pow_add]

/-- **Slice bound.** For `0 ≤ r < 1` the middle block is at most `rᵐ/(1 − r)`,
*independently of the right endpoint* `n` (and of whether `m ≤ n`). Wraps
Mathlib's `geom_sum_Ico_le_of_lt_one`. -/
theorem geometric_slice_le (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    ∑ k ∈ Ico m n, r ^ k ≤ r ^ m / (1 - r) :=
  geom_sum_Ico_le_of_lt_one hr0 hr1

/-- **Absolute slice bound (Cauchy estimate).** For `0 ≤ r < 1`,
`|∑_{k ∈ Ico m n} rᵏ| ≤ rᵐ/(1 − r)`. The slice is nonnegative, so the absolute
value is harmless; this is the form used in the comparison/ratio tests. -/
theorem geometric_slice_abs_le (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    |∑ k ∈ Ico m n, r ^ k| ≤ r ^ m / (1 - r) := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg hr0 i)]
  exact geometric_slice_le hr0 hr1 m n

/-- **Envelope vanishes.** The slice bound `rᵐ/(1 − r)` tends to `0` as the left
endpoint `m → ∞`. -/
theorem geometric_slice_bound_tendsto (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Filter.Tendsto (fun m => r ^ m / (1 - r)) Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun m => r ^ m) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  simpa using h0.div_const (1 - r)

/-- **Cauchy criterion.** For `0 ≤ r < 1` and any `ε > 0` there is a threshold
`N` such that *every* slice with left endpoint `m ≥ N` satisfies
`|∑_{k ∈ Ico m n} rᵏ| ≤ ε`, uniformly in the right endpoint `n`. This is the
estimate that exhibits the geometric series as Cauchy and underlies the
comparison and ratio tests. -/
theorem geometric_slice_cauchy (hr0 : 0 ≤ r) (hr1 : r < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, |∑ k ∈ Ico m n, r ^ k| ≤ ε := by
  have h1r : (0 : ℝ) < 1 - r := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hε h1r) hr1
  refine ⟨N, fun m hm n => ?_⟩
  have hbound : |∑ k ∈ Ico m n, r ^ k| ≤ r ^ m / (1 - r) :=
    geometric_slice_abs_le hr0 hr1 m n
  have hmono : r ^ m ≤ r ^ N := pow_le_pow_of_le_one hr0 hr1.le hm
  have hle : r ^ m / (1 - r) ≤ ε := by
    rw [div_le_iff₀ h1r]
    calc r ^ m ≤ r ^ N := hmono
      _ ≤ ε * (1 - r) := le_of_lt hN
  linarith

/-! ## Concrete instance

`r = 1/2`, slice `Ico 2 5`: the block `(1/2)² + (1/2)³ + (1/2)⁴ = 7/16`,
equal to the tail difference `(1/2)²/(1−1/2) − (1/2)⁵/(1−1/2) = 1/2 − 1/16`,
and bounded by the endpoint-free envelope `(1/2)²/(1−1/2) = 1/2`. -/

example : ∑ k ∈ Ico 2 5, (1 / 2 : ℝ) ^ k = 7 / 16 := by
  norm_num [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]

example : ∑ k ∈ Ico 2 5, (1 / 2 : ℝ) ^ k =
    (1 / 2 : ℝ) ^ 2 / (1 - 1 / 2) - (1 / 2 : ℝ) ^ 5 / (1 - 1 / 2) :=
  geometric_slice_eq_tail_sub (by norm_num) (by norm_num)

example : ∑ k ∈ Ico 2 5, (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ 2 / (1 - 1 / 2) :=
  geometric_slice_le (by norm_num) (by norm_num) 2 5

end GeometricSeriesOQ08OQ03
