import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-
# The Geometric Series as an Abstract Cauchy Sequence

## What This Proves

The sibling entry `GeometricSeriesOQ08OQ03.lean` produced the elementary `ε`–`N`
estimate `geometric_slice_cauchy`: for `0 ≤ r < 1` and every `ε > 0` there is a
threshold `N` past which *every* middle block `∑_{k ∈ Ico m n} rᵏ` is at most `ε`.
That statement is the raw analytic content of "the geometric series is Cauchy",
but phrased as a bespoke inequality. This follow-up **promotes it to Mathlib's
abstract predicates**, so the result can be plugged directly into the library's
convergence machinery:

* `geometric_partialSum_dist` — the metric reading of the slice: for `m ≤ n` the
  distance between the partial sums `∑_{k<m} rᵏ` and `∑_{k<n} rᵏ` is exactly the
  block `∑_{k ∈ Ico m n} rᵏ`, hence `≤ rᵐ/(1 − r)`.
* `geometric_partialSum_dist_le` — the symmetric distance bound
  `dist (Sₘ) (Sₙ) ≤ r^{min m n}/(1 − r)`, the form `Metric.cauchySeq_iff` wants.
* `geometric_partialSum_cauchySeq` — **the headline**: the partial sums
  `n ↦ ∑_{k<n} rᵏ` form a `CauchySeq`, proved straight from the slice bound via
  `Metric.cauchySeq_iff`, *without* invoking `hasSum_geometric`.
* `geometric_partialSum_le` — the partial sums are bounded by `(1 − r)⁻¹`
  (the `m = 0` slice bound), the hypothesis needed for the comparison test.
* `geometric_summable` — **summability recovered elementarily**: from the bounded
  monotone partial sums via `summable_of_sum_range_le`, again with no appeal to
  the closed-form `hasSum_geometric`.
* `geometric_cauchySeq_finset` — the unordered/Mathlib-native face: the net of
  finite partial sums `s ↦ ∑_{k ∈ s} rᵏ` over the directed set of finsets is a
  `CauchySeq` (`summable_iff_cauchySeq_finset`), the predicate that *defines*
  summability in a complete group.

## Why This Matters

`geometric_slice_cauchy` answers "is the tail block small?" with a hand-rolled
inequality. Convergence theorems in Mathlib speak a different language —
`CauchySeq`, `Summable`, `cauchySeq_finset` — and this file is the translation
layer. The payoff is conceptual honesty: the geometric series is shown to
**converge as a Cauchy sequence**, and to be **summable**, from first principles
(bounded blocks / bounded monotone partial sums) rather than by quoting the
already-evaluated infinite sum. The closed form `(1 − r)⁻¹` is the *consequence*
of convergence here, not its premise.

## Mathlib Relationship

The block bound (`geom_sum_Ico_le_of_lt_one`), the metric Cauchy criterion
(`Metric.cauchySeq_iff`), the bounded-partial-sums summability test
(`summable_of_sum_range_le`), and the `Summable ↔ CauchySeq`-over-finsets bridge
(`summable_iff_cauchySeq_finset`) are Mathlib lemmas. The assembled content is the
metric repackaging of the slice estimate and the deliberate derivation of
`CauchySeq`/`Summable` that routes around `hasSum_geometric`.
-/

namespace GeometricSeriesOQ08OQ03OQ01

open Finset

variable {r : ℝ}

/-- The `n`-th partial sum `∑_{k<n} rᵏ`. -/
local notation3 "S" => fun (n : ℕ) => ∑ k ∈ range n, r ^ k

/-- **Slice bound (self-contained).** For `0 ≤ r < 1`,
`|∑_{k ∈ Ico m n} rᵏ| ≤ rᵐ/(1 − r)`, independently of the right endpoint `n`.
The slice is a sum of nonnegative terms, so the absolute value is harmless. -/
theorem geometric_slice_abs_le (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    |∑ k ∈ Ico m n, r ^ k| ≤ r ^ m / (1 - r) := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg hr0 i)]
  exact geom_sum_Ico_le_of_lt_one hr0 hr1

/-- **Metric reading of the slice.** For `m ≤ n` the distance between the two
partial sums is the middle block, hence bounded by `rᵐ/(1 − r)`. -/
theorem geometric_partialSum_dist (hr0 : 0 ≤ r) (hr1 : r < 1) {m n : ℕ}
    (hmn : m ≤ n) :
    dist (∑ k ∈ range m, r ^ k) (∑ k ∈ range n, r ^ k) ≤ r ^ m / (1 - r) := by
  have hslice : ∑ k ∈ Ico m n, r ^ k =
      (∑ k ∈ range n, r ^ k) - ∑ k ∈ range m, r ^ k :=
    Finset.sum_Ico_eq_sub _ hmn
  rw [Real.dist_eq, abs_sub_comm, ← hslice]
  exact geometric_slice_abs_le hr0 hr1 m n

/-- **Symmetric distance bound.** `dist (Sₘ) (Sₙ) ≤ r^{min m n}/(1 − r)` for all
`m, n`: the exact shape consumed by `Metric.cauchySeq_iff`. -/
theorem geometric_partialSum_dist_le (hr0 : 0 ≤ r) (hr1 : r < 1) (m n : ℕ) :
    dist (∑ k ∈ range m, r ^ k) (∑ k ∈ range n, r ^ k)
      ≤ r ^ min m n / (1 - r) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h]; exact geometric_partialSum_dist hr0 hr1 h
  · rw [min_eq_right h, dist_comm]; exact geometric_partialSum_dist hr0 hr1 h

/-- **The geometric partial sums are a Cauchy sequence.** Proved directly from the
slice bound via `Metric.cauchySeq_iff`, with no appeal to `hasSum_geometric`. -/
theorem geometric_partialSum_cauchySeq (hr0 : 0 ≤ r) (hr1 : r < 1) :
    CauchySeq (fun n => ∑ k ∈ range n, r ^ k) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have h1r : (0 : ℝ) < 1 - r := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (mul_pos hε h1r) hr1
  refine ⟨N, fun m hm n hn => ?_⟩
  have hbound : dist (∑ k ∈ range m, r ^ k) (∑ k ∈ range n, r ^ k)
      ≤ r ^ min m n / (1 - r) := geometric_partialSum_dist_le hr0 hr1 m n
  have hmono : r ^ min m n ≤ r ^ N :=
    pow_le_pow_of_le_one hr0 hr1.le (le_min hm hn)
  have hlt : r ^ min m n / (1 - r) < ε := by
    rw [div_lt_iff₀ h1r]
    calc r ^ min m n ≤ r ^ N := hmono
      _ < ε * (1 - r) := hN
  linarith

/-- **Bounded partial sums.** Every partial sum `∑_{k<n} rᵏ` is at most
`(1 − r)⁻¹` — the `m = 0` instance of the slice bound. -/
theorem geometric_partialSum_le (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ k ∈ range n, r ^ k ≤ (1 - r)⁻¹ := by
  rw [Finset.range_eq_Ico]
  simpa [one_div] using geom_sum_Ico_le_of_lt_one (x := r) (m := 0) (n := n) hr0 hr1

/-- **Summability, recovered elementarily.** The geometric series is summable
because its terms are nonnegative and its partial sums are bounded
(`summable_of_sum_range_le`) — no use of the closed-form `hasSum_geometric`. -/
theorem geometric_summable (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k => r ^ k) :=
  summable_of_sum_range_le (fun n => pow_nonneg hr0 n)
    (fun n => geometric_partialSum_le hr0 hr1 n)

/-- **Cauchy over finsets.** The Mathlib-native predicate: the net of finite
partial sums `s ↦ ∑_{k ∈ s} rᵏ` over the directed set of finsets is a
`CauchySeq` — equivalent to summability via `summable_iff_cauchySeq_finset`. -/
theorem geometric_cauchySeq_finset (hr0 : 0 ≤ r) (hr1 : r < 1) :
    CauchySeq (fun s : Finset ℕ => ∑ k ∈ s, r ^ k) :=
  summable_iff_cauchySeq_finset.mp (geometric_summable hr0 hr1)

/-! ## Concrete instance

For `r = 1/2` the partial sums are Cauchy and bounded by `(1 − 1/2)⁻¹ = 2`, and
the series is summable. -/

example : CauchySeq (fun n => ∑ k ∈ range n, (1 / 2 : ℝ) ^ k) :=
  geometric_partialSum_cauchySeq (by norm_num) (by norm_num)

example : Summable (fun k => (1 / 2 : ℝ) ^ k) :=
  geometric_summable (by norm_num) (by norm_num)

example (n : ℕ) : ∑ k ∈ range n, (1 / 2 : ℝ) ^ k ≤ 2 := by
  have := geometric_partialSum_le (r := 1 / 2) (by norm_num) (by norm_num) n
  norm_num at this ⊢; linarith

end GeometricSeriesOQ08OQ03OQ01
