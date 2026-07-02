import Mathlib

/-
# Basel Problem OQ-10·OQ-03: The alternating harmonic series — and why it is only conditional

## Open Question
The parent entry (`basel-problem-oq-10`) formalized Leibniz's series `∑ (-1)^k/(2k+1) = π/4`
and the cautionary fact that the naive `tsum` reading collapses to the junk value `0`. This
follow-up establishes the *analogous cautionary pair* for the **alternating harmonic series**

  1 − 1/2 + 1/3 − 1/4 + ⋯ = log 2,   i.e.  ∑_n (-1)^n/(n+1) = log 2,

and unifies the underlying conditional-convergence pitfall into a reusable lemma.

## The subtlety (identical to the Leibniz case)
The alternating harmonic series is only *conditionally* convergent: the terms `(-1)^n/(n+1)`
are not absolutely summable (their magnitudes `1/(n+1)` form the divergent harmonic series).
Mathlib's `Summable` demands *unconditional* convergence, so:

  * the family `fun n => (-1)^n/(n+1)` is **not** `Summable`, and consequently
  * `∑' n, (-1)^n/(n+1) = 0` (the junk value for non-summable families), which is `≠ log 2`.

The correct statement is the convergence of the **ordered** partial sums, a `Tendsto` of
`∑_{i<n}`.

## New content vs. the parent
Unlike the Leibniz case — where Mathlib already provides `Real.tendsto_sum_pi_div_four` — Mathlib
does **not** contain the value of the alternating harmonic series. So the ordered-limit theorem
`tendsto_alternating_harmonic_log_two` is proved here *from scratch*, by the same Abel-limit route
Mathlib uses for Leibniz:
  1. the alternating series test gives convergence to *some* limit `l`;
  2. Abel's limit theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) transfers that to the
     boundary behaviour of the power series `∑ (-1)^n/(n+1) · x^n = log(1+x)/x` as `x → 1⁻`;
  3. continuity of `x ↦ log(1+x)/x` at `1` pins the limit to `log 2 / 1 = log 2`.

## Contents
* `tendsto_alternating_harmonic_log_two` — the correct statement (ordered partial sums → log 2).
* `not_summable_alternating_harmonic` — the family is not `Summable` (conditional convergence).
* `tsum_alternating_harmonic_eq_zero` / `tsum_alternating_harmonic_ne_log_two` — the cautionary
  `tsum` corollaries.
* `ordered_ne_tsum_of_not_summable` — the *reusable* pitfall lemma: for any real family that is
  not `Summable`, the unordered `tsum` is `0`, so it differs from any nonzero ordered limit.
  Both this entry and the parent Leibniz entry are instances.

## Status
Fully machine-checked, 0 axioms, 0 sorries.
-/

namespace BaselOQ10OQ03

open Filter Topology BigOperators Real Finset

/-- **The alternating harmonic series (correct form).** The *ordered* partial sums
`∑_{i<n} (-1)^i/(i+1)` converge to `log 2`. This is the statement that actually holds — the
series is conditionally convergent.

Mathlib has no ready-made value for this series (contrast `Real.tendsto_sum_pi_div_four` for
Leibniz), so we reconstruct it via Abel's limit theorem: the alternating series test gives a
limit `l`, Abel transfers convergence to the boundary of the power series
`∑ (-1)^n/(n+1)·x^n = log(1+x)/x`, and continuity at `1` identifies `l = log 2`. -/
theorem tendsto_alternating_harmonic_log_two :
    Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 (Real.log 2)) := by
  -- The series is alternating with terms of decreasing magnitude, so it converges to some limit.
  obtain ⟨l, h⟩ :
      ∃ l, Tendsto (fun n => ∑ i ∈ range n, (-1 : ℝ) ^ i / (i + 1)) atTop (𝓝 l) := by
    apply Antitone.tendsto_alternating_series_of_tendsto_zero
    · exact antitone_iff_forall_lt.mpr fun _ _ _ => by gcongr
    · have : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact this.inv_tendsto_atTop
  -- Abel's limit theorem: the corresponding power series has the same limit as `x → 1⁻`.
  have abel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt h
  -- Identify the power-series function with `log(1+x)/x` on a left-neighbourhood of `1`.
  replace abel : Tendsto (fun x => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    apply abel.congr'
    rw [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨1, one_pos, ?_⟩
    intro y hy1 hy2
    rw [dist_eq, abs_sub_lt_iff] at hy1
    rw [Set.mem_Iio] at hy2
    have hy0 : (0 : ℝ) < y := by linarith [hy1.2]
    have ny : |y| < 1 := by rw [abs_lt]; exact ⟨by linarith, hy2⟩
    -- Power series of `log`: `∑ (-y)^(n+1)/(n+1) = -log(1+y)`.
    have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := -y) (by rwa [abs_neg])
    rw [sub_neg_eq_add] at hs
    -- Rewrite each term so the sum becomes `∑ (g n) * y` with `g n = (-1)^n/(n+1) · y^n`.
    have hfun : (fun n : ℕ => (-1 : ℝ) * ((-y) ^ (n + 1) / ((n : ℝ) + 1)))
              = (fun n : ℕ => ((-1 : ℝ) ^ n / ((n : ℝ) + 1) * y ^ n) * y) := by
      funext n; rw [neg_pow]; ring
    have hsy : HasSum (fun n : ℕ => ((-1 : ℝ) ^ n / ((n : ℝ) + 1) * y ^ n) * y)
        (Real.log (1 + y)) := by
      have hm := hs.mul_left (-1)
      rw [hfun] at hm
      convert hm using 1
      ring
    -- Divide out the common factor `y ≠ 0`.
    have hy0' : y ≠ 0 := hy0.ne'
    have hg : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) * y ^ n)
        (Real.log (1 + y) / y) := by
      apply (hasSum_mul_right_iff hy0').mp
      rwa [div_mul_cancel₀ _ hy0']
    exact hg.tsum_eq
  -- `x ↦ log(1+x)/x` is continuous at `1`, with value `log 2 / 1 = log 2`.
  have m : 𝓝[<] (1 : ℝ) ≤ 𝓝 1 := nhdsWithin_le_nhds
  have hcont : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.log 2)) := by
    have hct : ContinuousAt (fun x : ℝ => Real.log (1 + x) / x) 1 := by
      apply ContinuousAt.div
      · exact (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
      · fun_prop
      · norm_num
    simpa [one_add_one_eq_two] using hct.tendsto.mono_left m
  rwa [tendsto_nhds_unique abel hcont] at h

/-- **The alternating-harmonic family is not summable.** The terms `(-1)^n/(n+1)` are not
unconditionally summable: their absolute values `1/(n+1)` are the divergent harmonic series.
Hence the convergence above is *conditional*. -/
theorem not_summable_alternating_harmonic :
    ¬ Summable (fun n : ℕ => (-1 : ℝ) ^ n / (n + 1)) := by
  rw [← summable_abs_iff]
  have habs : (fun n : ℕ => |(-1 : ℝ) ^ n / (n + 1)|)
            = (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    funext n
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  rw [habs]
  intro h
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_congr (fun n => ?_)).mp h
    push_cast; ring
  exact not_summable_one_div_natCast hfull

/-- **Cautionary corollary.** Because the family is not summable, its `tsum` collapses to the
junk value `0` — it is *not* `log 2`. -/
theorem tsum_alternating_harmonic_eq_zero :
    ∑' n : ℕ, (-1 : ℝ) ^ n / (n + 1) = 0 :=
  tsum_eq_zero_of_not_summable not_summable_alternating_harmonic

/-- The `tsum` reading is `0 ≠ log 2`: the naive unconditional interpretation of the alternating
harmonic series is false. -/
theorem tsum_alternating_harmonic_ne_log_two :
    ∑' n : ℕ, (-1 : ℝ) ^ n / (n + 1) ≠ Real.log 2 := by
  rw [tsum_alternating_harmonic_eq_zero]
  exact (Real.log_pos (by norm_num)).ne

/-- **The reusable conditional-convergence pitfall.** For any real family `f` that is *not*
`Summable`, the unordered `tsum` is the junk value `0`. Hence it disagrees with any nonzero
ordered limit `L`: `∑' n, f n = 0 ≠ L`.

Both this entry (`L = log 2`) and the parent Leibniz entry (`L = π/4`) are instances: a
conditionally convergent series carries a meaningful *ordered* value that the `Summable`/`tsum`
machinery, being unconditional, discards. -/
theorem ordered_ne_tsum_of_not_summable {f : ℕ → ℝ} {L : ℝ}
    (hL : L ≠ 0) (hns : ¬ Summable f) : ∑' n, f n ≠ L := by
  rw [tsum_eq_zero_of_not_summable hns]
  exact fun h => hL h.symm

end BaselOQ10OQ03
