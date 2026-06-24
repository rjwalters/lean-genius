import Mathlib

/-
# Basel Problem OQ-10-OQ-01: Explicit error bound for the Leibniz approximation of π/4

## Open Question (from BaselProblemOQ10)
Quantify the conditional convergence of the Leibniz–Madhava–Gregory series: prove the
alternating-series error bound
  |∑_{i<k} (-1)^i/(2i+1) − π/4| ≤ 1/(2k+1),
giving an explicit (slow) convergence rate.

## Why this is not a corollary of Mathlib's `alternating_series_error_bound`
Mathlib *does* package an alternating-series error bound
(`alternating_series_error_bound`), but it is stated for the **`tsum`** of the series and
requires the hypothesis `Summable f`. The Leibniz family is **not** summable (it is only
*conditionally* convergent — see `BaselProblemOQ10.not_summable_leibniz`), so that packaged
result cannot be applied here: its `∑'` would collapse to the junk value `0`.

The fix is to bypass `tsum` entirely. The two underlying sandwich lemmas
  `Antitone.alternating_series_le_tendsto`  (even partial sums ≤ limit), and
  `Antitone.tendsto_le_alternating_series`  (limit ≤ odd partial sums),
require only that the *ordered* partial sums `Tendsto` to a limit `l` — no summability.
We package these into a summability-free error bound `alternating_error_bound_of_tendsto`
and apply it with `l = π/4` via Mathlib's `tendsto_sum_pi_div_four`.

## Contents
* `alternating_error_bound_of_tendsto` — general summability-free error bound for any
  antitone non-negative sequence whose alternating partial sums converge.
* `leibniz_error_bound` — the explicit Leibniz bound |∑_{i<k} (-1)^i/(2i+1) − π/4| ≤ 1/(2k+1).
* `leibniz_error_bound_le_inv` — the same bound phrased as ≤ 1/(2k+1) with the partial sum on
  the left, plus a sanity corollary that the bound tends to 0.

## Status
Fully machine-checked, 0 axioms, 0 sorries.
-/

namespace BaselOQ10OQ01

open Filter Topology BigOperators Real Finset

/-- **Summability-free alternating-series error bound.**
For an antitone, non-negative real sequence `f` whose *ordered* alternating partial sums
`∑_{i<n} (-1)^i f i` converge to `l`, the `n`-th partial sum approximates `l` with error at
most `f n`. Unlike `alternating_series_error_bound`, this needs only convergence of the
ordered partial sums (a `Tendsto` hypothesis), **not** `Summable f`; it therefore applies to
conditionally convergent series such as Leibniz's. The proof mirrors Mathlib's, replacing the
`tsum`-derived limit with the supplied `Tendsto`. -/
theorem alternating_error_bound_of_tendsto {f : ℕ → ℝ} (hfa : Antitone f)
    (hf0 : ∀ n, 0 ≤ f n) {l : ℝ}
    (hl : Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * f i) atTop (𝓝 l)) (n : ℕ) :
    |l - ∑ i ∈ range n, (-1 : ℝ) ^ i * f i| ≤ f n := by
  have upper := hfa.alternating_series_le_tendsto hl
  have lower := hfa.tendsto_le_alternating_series hl
  obtain (h | h) := Nat.even_or_odd n
  · -- even: n = 2 * m
    obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper m
    specialize lower m
    simp only [sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (hf0 (2 * m)))
  · -- odd: n = 2 * m + 1
    obtain ⟨m, rfl⟩ := h
    specialize upper (m + 1)
    specialize lower m
    rw [Nat.mul_add, sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (hf0 (2 * m + 1)))
    · simpa [sum_range_succ, add_comm, pow_add] using upper

/-- The Leibniz term sequence `f i = 1/(2i+1)`. -/
noncomputable def leibTerm (i : ℕ) : ℝ := 1 / (2 * i + 1)

theorem leibTerm_antitone : Antitone leibTerm := by
  intro a b hab
  simp only [leibTerm]
  apply one_div_le_one_div_of_le
  · positivity
  · have : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
    linarith

theorem leibTerm_nonneg (n : ℕ) : 0 ≤ leibTerm n := by
  simp only [leibTerm]; positivity

/-- The alternating partial sums `∑_{i<n} (-1)^i · leibTerm i` are Mathlib's Leibniz partial
sums `∑_{i<n} (-1)^i/(2i+1)`, hence converge to `π/4`. -/
theorem leibniz_partialSum_tendsto :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * leibTerm i) atTop (𝓝 (π / 4)) := by
  have heq : (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i * leibTerm i)
           = (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (2 * i + 1)) := by
    funext n
    apply sum_congr rfl
    intro i _
    simp only [leibTerm]
    ring
  rw [heq]
  exact tendsto_sum_pi_div_four

/-- **Explicit Leibniz error bound.** The `k`-th ordered partial sum of the Leibniz series
approximates `π/4` with error at most `1/(2k+1)`:
  |∑_{i<k} (-1)^i/(2i+1) − π/4| ≤ 1/(2k+1).
This is the quantitative form of the (only conditional) convergence
`BaselProblemOQ10.leibniz_tendsto_pi_div_four`. -/
theorem leibniz_error_bound (k : ℕ) :
    |(∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1)) - π / 4| ≤ 1 / (2 * k + 1) := by
  have key := alternating_error_bound_of_tendsto leibTerm_antitone leibTerm_nonneg
    leibniz_partialSum_tendsto k
  -- key : |π/4 - ∑ (-1)^i * leibTerm i| ≤ leibTerm k
  have hsum : (∑ i ∈ range k, (-1 : ℝ) ^ i * leibTerm i)
            = ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1) := by
    apply sum_congr rfl; intro i _; simp only [leibTerm]; ring
  rw [hsum] at key
  rw [abs_sub_comm] at key
  simpa only [leibTerm] using key

/-- Sanity corollary exhibiting the explicit `1/(2k+1)` decay rate: the error bound tends to
`0`, recovering convergence (qualitatively) from the quantitative bound. -/
theorem leibniz_error_tendsto_zero :
    Tendsto (fun k : ℕ => (1 : ℝ) / (2 * k + 1)) atTop (𝓝 0) := by
  have hden : Tendsto (fun k : ℕ => (2 * (k : ℝ) + 1)) atTop atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hden

end BaselOQ10OQ01

#check @BaselOQ10OQ01.alternating_error_bound_of_tendsto
#check @BaselOQ10OQ01.leibniz_error_bound
#check @BaselOQ10OQ01.leibniz_error_tendsto_zero
