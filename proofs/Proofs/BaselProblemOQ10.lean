import Mathlib

/-
# Basel Problem OQ-10: Leibniz's series for π — and why it is only conditional

## Open Question
Formalize the Leibniz–Madhava–Gregory series
  1 − 1/3 + 1/5 − 1/7 + ⋯ = π/4,
i.e. ∑_k (-1)^k / (2k+1) = π/4.

## The subtlety
The naive `tsum` reading `∑' k, (-1)^k/(2k+1) = π/4` is **false**. The Leibniz
series is only *conditionally* convergent: the terms `(-1)^k/(2k+1)` are not
absolutely summable (their absolute values `1/(2k+1)` form a divergent
harmonic-type series). In Lean/Mathlib, `Summable` (and hence `tsum` / `HasSum`)
demands *unconditional* convergence, so:

  * the family `fun k => (-1)^k/(2k+1)` is **not** `Summable`, and consequently
  * `∑' k, (-1)^k/(2k+1) = 0` (the junk value for non-summable families),
    which is `≠ π/4`.

The correct statement is the convergence of the **ordered** partial sums, a
`Tendsto` of `∑_{i<k}`, which is exactly Mathlib's `tendsto_sum_pi_div_four`.

## Contents
* `leibniz_tendsto_pi_div_four` — the correct Leibniz statement (ordered partial sums → π/4).
* `not_summable_leibniz` — the Leibniz family is not `Summable` (conditional convergence).
* `tsum_leibniz_eq_zero` and `tsum_leibniz_ne_pi_div_four` — the cautionary `tsum` corollaries.

## Status
Fully machine-checked, 0 axioms, 0 sorries. The non-summability proof is the
substantive new content; the convergence itself is Mathlib's.
-/

namespace BaselOQ10

open Filter Topology BigOperators Real Finset

/-- **Leibniz's series for π (correct form).** The *ordered* partial sums
`∑_{i<k} (-1)^i/(2i+1)` converge to `π/4`. This is the statement that actually
holds — the series is conditionally convergent. (Mathlib: `tendsto_sum_pi_div_four`.) -/
theorem leibniz_tendsto_pi_div_four :
    Tendsto (fun k => ∑ i ∈ range k, (-1 : ℝ) ^ i / (2 * i + 1)) atTop (𝓝 (π / 4)) :=
  tendsto_sum_pi_div_four

/-- **The Leibniz family is not summable.** The terms `(-1)^k/(2k+1)` are not
unconditionally summable: their absolute values `1/(2k+1)` dominate the divergent
half-harmonic series `(1/2)·1/(k+1)`. Hence Leibniz convergence is *conditional*. -/
theorem not_summable_leibniz :
    ¬ Summable (fun k : ℕ => (-1 : ℝ) ^ k / (2 * k + 1)) := by
  rw [← summable_abs_iff]
  -- |(-1)^k/(2k+1)| = 1/(2k+1)
  have habs : (fun k : ℕ => |(-1 : ℝ) ^ k / (2 * k + 1)|)
            = (fun k : ℕ => 1 / (2 * (k : ℝ) + 1)) := by
    funext k
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
  rw [habs]
  intro h
  -- minorant: 1/(2k+2) ≤ 1/(2k+1), and 1/(2k+2) is half-harmonic, hence divergent
  have hmin : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 2)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hharm : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1)) := by
    have h2 := hmin.mul_left 2
    refine (summable_congr (fun k => ?_)).mp h2
    rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hfull : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    refine (summable_congr (fun n => ?_)).mp hharm
    push_cast; ring
  exact not_summable_one_div_natCast hfull

/-- **Cautionary corollary.** Because the Leibniz family is not summable, its
`tsum` collapses to the junk value `0` — it is *not* `π/4`. -/
theorem tsum_leibniz_eq_zero :
    ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * k + 1) = 0 :=
  tsum_eq_zero_of_not_summable not_summable_leibniz

/-- The `tsum` of the Leibniz family is `0 ≠ π/4`: the naive unconditional reading
of "1 − 1/3 + 1/5 − ⋯ = π/4" is false; only the ordered limit above is correct. -/
theorem tsum_leibniz_ne_pi_div_four :
    ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * k + 1) ≠ π / 4 := by
  rw [tsum_leibniz_eq_zero]
  have : (0 : ℝ) < π / 4 := by positivity
  linarith

end BaselOQ10

#check @BaselOQ10.leibniz_tendsto_pi_div_four
#check @BaselOQ10.not_summable_leibniz
#check @BaselOQ10.tsum_leibniz_eq_zero
#check @BaselOQ10.tsum_leibniz_ne_pi_div_four
