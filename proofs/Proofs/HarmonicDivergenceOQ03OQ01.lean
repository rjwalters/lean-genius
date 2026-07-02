import Mathlib
import Proofs.HarmonicDivergenceOQ03

/-!
# A Positive, Absolutely Convergent Series for `log 2`

The companion entry `HarmonicDivergenceOQ03` shows the **alternating** harmonic
series `1 - 1/2 + 1/3 - 1/4 + ⋯` converges *conditionally* to `log 2` (its value
exists only as an ordered limit of partial sums; `¬ Summable`).

This file pairs consecutive terms — `(1 - 1/2) + (1/3 - 1/4) + ⋯` — to obtain a
series of **positive** terms with the *same* sum:

  `∑ₖ 1/((2k+1)(2k+2)) = log 2`.

Because `1/((2k+1)(2k+2)) = O(1/k²)`, this regrouped series is **absolutely**
convergent, so unlike its alternating parent it has an honest `HasSum` /
`tsum` value.  This is the standard "the sum of an alternating series equals the
sum of its consecutive pairings" phenomenon made concrete for the Mercator
series, answering the parent entry's open question about reorganizing the
boundary value.

## Main results
* `sum_pairTerm_eq` — the `N`-th partial sum equals the `2N`-th alternating
  partial sum (`altPartial (2N)`).
* `summable_pairTerm` — the positive series is (absolutely) summable.
* `hasSum_pairTerm_log_two` / `tsum_pairTerm` — `∑ₖ 1/((2k+1)(2k+2)) = log 2`.

All results are `0`-sorry, `0`-axiom, built on `altHarmonic_tendsto_log_two`.
-/

namespace HarmonicAlt

open Filter Finset
open scoped Topology

/-- The `k`-th paired term `1/((2k+1)(2k+2))`, obtained by grouping the
`2k`-th and `(2k+1)`-th terms of the alternating harmonic series:
`(-1)^{2k}/(2k+1) + (-1)^{2k+1}/(2k+2) = 1/(2k+1) - 1/(2k+2) = 1/((2k+1)(2k+2))`. -/
noncomputable def pairTerm (k : ℕ) : ℝ := 1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2))

theorem pairTerm_nonneg (k : ℕ) : 0 ≤ pairTerm k := by
  rw [pairTerm]; positivity

/-- Pairing identity: two consecutive alternating terms collapse to one positive term. -/
theorem altTerm_pair (k : ℕ) : altTerm (2 * k) + altTerm (2 * k + 1) = pairTerm k := by
  have h1 : ((-1 : ℝ)) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  have h2 : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  simp only [altTerm, pairTerm]
  push_cast
  rw [h1, h2]
  have ha : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  have hb : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **The `N`-th paired partial sum equals the `2N`-th alternating partial sum.** -/
theorem sum_pairTerm_eq (N : ℕ) :
    ∑ k ∈ range N, pairTerm k = altPartial (2 * N) := by
  induction N with
  | zero => simp [altPartial]
  | succ n ih =>
    have hstep : altPartial (2 * (n + 1)) =
        altPartial (2 * n) + altTerm (2 * n) + altTerm (2 * n + 1) := by
      unfold altPartial
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Finset.sum_range_succ, ih, hstep]
    have := altTerm_pair n
    linarith

/-- The paired partial sums converge to `log 2` (a subsequence of the alternating
partial sums along the even indices). -/
theorem tendsto_sum_pairTerm :
    Tendsto (fun N => ∑ k ∈ range N, pairTerm k) atTop (𝓝 (Real.log 2)) := by
  have hfun : (fun N => ∑ k ∈ range N, pairTerm k) = (fun N => altPartial (2 * N)) :=
    funext sum_pairTerm_eq
  rw [hfun]
  have h2N : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  exact altHarmonic_tendsto_log_two.comp h2N

/-- **The positive regrouped series is (absolutely) summable.** Its partial sums
are monotone (positive terms) and bounded above by their limit `log 2`. -/
theorem summable_pairTerm : Summable pairTerm := by
  apply summable_of_sum_range_le pairTerm_nonneg
  intro N
  have hmono : Monotone (fun M => ∑ i ∈ range M, pairTerm i) :=
    monotone_nat_of_le_succ fun m => by
      rw [Finset.sum_range_succ]; linarith [pairTerm_nonneg m]
  exact hmono.ge_of_tendsto tendsto_sum_pairTerm N

/-- **A positive series for `log 2`:** `∑ₖ 1/((2k+1)(2k+2)) = log 2`. -/
theorem hasSum_pairTerm_log_two : HasSum pairTerm (Real.log 2) := by
  have hval : ∑' k, pairTerm k = Real.log 2 :=
    tendsto_nhds_unique summable_pairTerm.hasSum.tendsto_sum_nat tendsto_sum_pairTerm
  exact hval ▸ summable_pairTerm.hasSum

/-- `tsum` form: `∑' k, 1/((2k+1)(2k+2)) = log 2`. -/
theorem tsum_pairTerm : ∑' k, pairTerm k = Real.log 2 :=
  hasSum_pairTerm_log_two.tsum_eq

end HarmonicAlt
