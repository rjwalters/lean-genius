import Proofs.GeometricSeriesOQ08OQ03OQ01
import Mathlib.Tactic

/-
# Identifying the Limit: the Geometric Sum from First Principles

## What This Proves

The sibling entry `GeometricSeriesOQ08OQ03OQ01.lean` established that the partial
sums `S n = ∑_{k<n} rᵏ` of the geometric series form a **`CauchySeq`** and that
the series is **`Summable`**, both derived purely from the tail-block (slice)
bound `rᵐ/(1 − r)` — deliberately *without* quoting the evaluated closed form
`hasSum_geometric`. At that stage we knew the series converges, but the **value**
of the limit was still open. This entry closes the arc: it pins the limit to the
expected `(1 − r)⁻¹` and recovers `HasSum`/`tsum` from first principles.

* `geometric_truncation_defect` — the elementary identity
  `∑_{k<n} rᵏ = (1 − r)⁻¹ − rⁿ/(1 − r)`, a pure `geom_sum_eq` rearrangement
  (finite-sum algebra, no analysis).
* `geometric_partialSum_tendsto` — **the partial sums converge to `(1 − r)⁻¹`**:
  the defect `rⁿ/(1 − r) → 0`, so `S n → (1 − r)⁻¹`.
* `geometric_limit_from_completeness` — **the abstract route, made explicit**:
  feed the sibling's `CauchySeq` into `cauchySeq_tendsto_of_complete` to obtain
  *some* limit `L` from completeness of `ℝ` alone (existence before value), then
  identify `L = (1 − r)⁻¹` by `tendsto_nhds_unique` against the defect limit. This
  is exactly the question the sibling left open.
* `geometric_hasSum` — **`HasSum (fun n ↦ rⁿ) (1 − r)⁻¹`**, assembled from the
  sibling's `Summable` and the partial-sum limit via
  `Summable.hasSum_iff_tendsto_nat`, with no appeal to `hasSum_geometric`.
* `geometric_tsum` — the unconditional sum `∑' n, rⁿ = (1 − r)⁻¹`.

## Why This Matters

The lineage `oq-08-oq-03 → …-oq-01 → …-oq-01-oq-01` rebuilds the geometric series'
convergence theory from the Cauchy criterion upward: first the `ε`–`N` block
estimate, then the abstract `CauchySeq`/`Summable` predicates, and now the limit
*value*. The completeness of `ℝ` supplies the existence of a limit knowing only
that the partial sums are Cauchy; the truncation defect supplies its identity.
Together they reproduce Mathlib's `hasSum_geometric_of_lt_one` /
`tsum_geometric_of_lt_one` along an independent path that never assumes the
closed form it concludes — the sum `(1 − r)⁻¹` is earned, not quoted.

## Mathlib Relationship

`geom_sum_eq`, `tendsto_pow_atTop_nhds_zero_of_lt_one`,
`cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`, and
`Summable.hasSum_iff_tendsto_nat` are Mathlib lemmas; the `CauchySeq`/`Summable`
inputs are reused verbatim from the sibling entry. The content here is the
deliberate identification of the limit through completeness + the truncation
defect, recovering `hasSum_geometric` without invoking it.
-/

namespace GeometricSeriesOQ08OQ03OQ01OQ01

open Finset Filter

variable {r : ℝ}

/-- **Truncation defect (algebraic form).** For `1 − r ≠ 0`, the `n`-th partial sum
is the full limit `(1 − r)⁻¹` minus the tail factor `rⁿ/(1 − r)`. This is a pure
rearrangement of the finite geometric sum `geom_sum_eq`; no analysis is used. -/
theorem geometric_truncation_defect (h1r : (1 : ℝ) - r ≠ 0) (n : ℕ) :
    ∑ k ∈ range n, r ^ k = (1 - r)⁻¹ - r ^ n / (1 - r) := by
  have hr1 : r ≠ 1 := fun h => h1r (by rw [h]; ring)
  have hr1' : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  rw [geom_sum_eq hr1]
  field_simp
  ring

/-- **The partial sums converge to `(1 − r)⁻¹`.** Reading the truncation defect as
`n → ∞`: the tail `rⁿ/(1 − r)` tends to `0` (since `rⁿ → 0`), so the partial sums
tend to `(1 − r)⁻¹`. Computed directly from the defect, not from `hasSum_geometric`. -/
theorem geometric_partialSum_tendsto (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n => ∑ k ∈ range n, r ^ k) atTop (nhds (1 - r)⁻¹) := by
  have h1r : (1 : ℝ) - r ≠ 0 := (by linarith : (0 : ℝ) < 1 - r).ne'
  have hzero : Tendsto (fun n => r ^ n / (1 - r)) atTop (nhds 0) := by
    have hp : Tendsto (fun n => r ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using hp.div_const (1 - r)
  have heq : (fun n => ∑ k ∈ range n, r ^ k)
      = fun n => (1 - r)⁻¹ - r ^ n / (1 - r) :=
    funext fun n => geometric_truncation_defect h1r n
  rw [heq]
  have hc : Tendsto (fun _ : ℕ => (1 - r)⁻¹) atTop (nhds (1 - r)⁻¹) := tendsto_const_nhds
  simpa using hc.sub hzero

/-- **The abstract route, completed.** Completeness of `ℝ` turns the sibling's
`CauchySeq` into the existence of *some* limit `L` (value unknown); the truncation
defect then forces `L = (1 − r)⁻¹` by uniqueness of limits. This answers the open
question left by `GeometricSeriesOQ08OQ03OQ01`: existence is supplied by
completeness, identity by the defect. -/
theorem geometric_limit_from_completeness (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ L, Tendsto (fun n => ∑ k ∈ range n, r ^ k) atTop (nhds L) ∧ L = (1 - r)⁻¹ := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (GeometricSeriesOQ08OQ03OQ01.geometric_partialSum_cauchySeq hr0 hr1)
  exact ⟨L, hL, tendsto_nhds_unique hL (geometric_partialSum_tendsto hr0 hr1)⟩

/-- **`HasSum` recovered from first principles.** The sibling's `Summable` gives the
`HasSum ↔ partial-sum convergence` bridge; the partial sums converge to `(1 − r)⁻¹`;
hence `HasSum (fun n ↦ rⁿ) (1 − r)⁻¹` — an independent derivation of
`hasSum_geometric_of_lt_one` that never invokes it. -/
theorem geometric_hasSum (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n => r ^ n) (1 - r)⁻¹ :=
  (GeometricSeriesOQ08OQ03OQ01.geometric_summable hr0 hr1).hasSum_iff_tendsto_nat.mpr
    (geometric_partialSum_tendsto hr0 hr1)

/-- **The unconditional sum.** `∑' n, rⁿ = (1 − r)⁻¹`, the value of the now-identified
limit — recovering `tsum_geometric_of_lt_one` along the Cauchy/completeness path. -/
theorem geometric_tsum (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (geometric_hasSum hr0 hr1).tsum_eq

/-! ## Concrete instance

For `r = 1/2` the partial sums converge to `(1 − 1/2)⁻¹ = 2`, and `∑' n, (1/2)ⁿ = 2`. -/

example : Tendsto (fun n => ∑ k ∈ range n, (1 / 2 : ℝ) ^ k) atTop (nhds 2) := by
  have := geometric_partialSum_tendsto (r := 1 / 2) (by norm_num) (by norm_num)
  norm_num at this; exact this

example : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = 2 := by
  have := geometric_tsum (r := 1 / 2) (by norm_num) (by norm_num)
  norm_num at this; exact this

end GeometricSeriesOQ08OQ03OQ01OQ01
