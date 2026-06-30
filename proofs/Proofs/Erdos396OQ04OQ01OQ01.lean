/-
# Erdős Problem #396 — OQ-04 → OQ-01 → OQ-01: the Catalan ratio deficit is harmonic

The parent entry `Erdos396OQ04OQ01` reads the two-term Catalan recurrence as a
statement about the ratio of consecutive Catalan numbers,

  `r n = (4n+2)/(n+2) = 4 − 6/(n+2)`,

and shows `r n < 4`, `r` is strictly increasing, and `r n → 4`.

This follow-up looks at the **deficit** `δ n = 4 − r n`, the amount by which the
`n`-th multiplicative step falls short of the limiting growth rate `4`.  From the
partial-fraction identity the deficit is *exactly* `δ n = 6/(n+2)`, the tail of a
harmonic series.  The headline is a sharp convergence-versus-divergence
dichotomy:

* **`deficit_tendsto_zero`** : `δ n → 0` — individual steps approach the rate `4`;
* **`deficit_sum_eq`** : `∑_{k<n} δ k = 6·(H_{n+1} − 1)`, where
  `H m = ∑_{i<m} 1/(i+1)` is the `m`-th harmonic number — the cumulative
  shortfall is a harmonic partial sum;
* **`deficit_sum_tendsto_atTop`** : `∑_{k<n} δ k → ∞`.

So although every ratio individually races up to `4`, the **total** distance the
ratios lag behind `4` is harmonic and therefore *diverges*.  This is the precise
discrete reason the asymptotic refinement of `catalan n ∼ 4^n / (n^{3/2}√π)`
carries a polynomial correction below `4^n`: the multiplicative deficits do not
sum to a finite constant.

As a corollary we get a closed form for the running sum of the ratios
(**`ratio_sum_eq`**): `∑_{k<n} r k = 4n − 6·(H_{n+1} − 1)`.

Everything is derived from the parent's ratio identity together with the
divergence of the harmonic series; no Stirling estimate is used.

Reference: https://erdosproblems.com/396
-/

import Mathlib
import Proofs.Erdos396OQ04OQ01

open Nat Filter Topology Finset

namespace Erdos396OQ01OQ01

open Erdos396OQ01

/-- The `n`-th **deficit** of the Catalan recurrence ratio: how far the step
    `r n` falls short of the limiting growth rate `4`. -/
noncomputable def catalanDeficit (n : ℕ) : ℝ := 4 - catalanRatio n

/-- The `m`-th harmonic number `H m = ∑_{i<m} 1/(i+1)` as a real number. -/
noncomputable def realHarmonic (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (1 : ℝ) / (i + 1)

/-- **Deficit identity.** `δ n = 6/(n+2)` — the deficit is the tail of a
    harmonic series. -/
theorem deficit_eq (n : ℕ) : catalanDeficit n = 6 / ((n : ℝ) + 2) := by
  rw [catalanDeficit, ratio_eq_four_sub]; ring

/-- The deficit is strictly positive. -/
theorem deficit_pos (n : ℕ) : 0 < catalanDeficit n := by
  rw [deficit_eq]; positivity

/-- **Individual steps approach the rate `4`.** `δ n → 0`. -/
theorem deficit_tendsto_zero : Tendsto catalanDeficit atTop (𝓝 0) := by
  have h : Tendsto (fun n => 4 - catalanRatio n) atTop (𝓝 (4 - 4)) :=
    tendsto_const_nhds.sub ratio_tendsto_four
  simpa [catalanDeficit, sub_self] using h

/-- The harmonic partial sum recurrence `H (m+1) = H m + 1/(m+1)`. -/
theorem realHarmonic_succ (m : ℕ) :
    realHarmonic (m + 1) = realHarmonic m + 1 / ((m : ℝ) + 1) := by
  simp [realHarmonic, Finset.sum_range_succ]

/-- `H 1 = 1`. -/
theorem realHarmonic_one : realHarmonic 1 = 1 := by
  simp [realHarmonic]

/-- **Cumulative deficit is a harmonic partial sum.**
    `∑_{k<n} δ k = 6·(H_{n+1} − 1)`. -/
theorem deficit_sum_eq (n : ℕ) :
    ∑ k ∈ Finset.range n, catalanDeficit k = 6 * (realHarmonic (n + 1) - 1) := by
  induction n with
  | zero => simp [realHarmonic_one]
  | succ m ih =>
    have hH : realHarmonic (m + 1 + 1) = realHarmonic (m + 1) + 1 / ((m : ℝ) + 2) := by
      rw [realHarmonic_succ (m + 1)]; push_cast; ring
    rw [Finset.sum_range_succ, ih, deficit_eq, hH]; ring

/-- **Running sum of the ratios.** `∑_{k<n} r k = 4n − 6·(H_{n+1} − 1)`. -/
theorem ratio_sum_eq (n : ℕ) :
    ∑ k ∈ Finset.range n, catalanRatio k = 4 * n - 6 * (realHarmonic (n + 1) - 1) := by
  have hsplit : ∑ k ∈ Finset.range n, catalanRatio k
      = ∑ k ∈ Finset.range n, ((4 : ℝ) - catalanDeficit k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [catalanDeficit]; ring
  rw [hsplit, Finset.sum_sub_distrib, deficit_sum_eq]
  simp [Finset.sum_const, Finset.card_range]
  ring

/-- The harmonic partial sums diverge (Mathlib's harmonic-series divergence). -/
theorem realHarmonic_tendsto_atTop : Tendsto realHarmonic atTop atTop := by
  unfold realHarmonic
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- **Cumulative shortfall diverges.** `∑_{k<n} δ k → ∞`.

    The contrast with `deficit_tendsto_zero` is the whole point: each step's
    deficit vanishes, yet the deficits sum to a harmonic series and so their
    running total is unbounded. -/
theorem deficit_sum_tendsto_atTop :
    Tendsto (fun n => ∑ k ∈ Finset.range n, catalanDeficit k) atTop atTop := by
  have hH : Tendsto (fun n => realHarmonic (n + 1)) atTop atTop :=
    realHarmonic_tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hsub : Tendsto (fun n => realHarmonic (n + 1) - 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-1) hH
  have hmul : Tendsto (fun n => 6 * (realHarmonic (n + 1) - 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 6) hsub
  exact hmul.congr (fun n => (deficit_sum_eq n).symm)

/- ## Sanity checks -/

/-- `δ 0 = 3`: `r 0 = 1`, so the first step lags `4` by `3`. -/
example : catalanDeficit 0 = 3 := by rw [deficit_eq]; norm_num

/-- Cumulative deficit over the first two steps:
    `δ 0 + δ 1 = 3 + 2 = 5 = 6·(H₃ − 1) = 6·(1 + 1/2 + 1/3 − 1)`. -/
example : ∑ k ∈ Finset.range 2, catalanDeficit k = 5 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.range_zero, Finset.sum_empty]
  rw [deficit_eq, deficit_eq]; norm_num

end Erdos396OQ01OQ01
