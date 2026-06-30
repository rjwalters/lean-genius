import Mathlib

/-!
# The Alternating Harmonic Series Sums to `log 2`

## What This Proves
Where the parent entry shows the *harmonic* series `∑ 1/n` diverges, this
companion settles its alternating cousin: the **alternating harmonic series**

  `1 - 1/2 + 1/3 - 1/4 + ⋯ = log 2`

converges, and its value is exactly `Real.log 2` (the Mercator / Mengoli
series). Inserting a sign turns a divergent series into a convergent one with a
clean closed form.

## Why this is not immediate from Mathlib
Mathlib provides the Mercator power series only on the *open* interval:
`Real.hasSum_pow_div_log_of_abs_lt_one` gives
`∑ x^(n+1)/(n+1) = -log(1-x)` for `|x| < 1`. The alternating harmonic series is
the **boundary value** `x → 1⁻`, which is *not* covered by that lemma — the
power series there is only conditionally convergent. Bridging the interior
series to the boundary requires **Abel's limit theorem**
(`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`), exactly as Mathlib's
`Real.tendsto_sum_pi_div_four` does for Leibniz's series for `π`.

## Approach (mirrors Mathlib's Leibniz proof)
1. **Convergence.** The terms `1/(n+1)` are antitone and tend to `0`, so the
   alternating series test gives convergence to *some* limit `l`.
2. **Generating function.** For `0 < x < 1`,
   `∑' n, (-1)^n/(n+1) · xⁿ = log(1+x)/x`, obtained from the Mercator series at
   `-x` by multiplying by `-1/x`.
3. **Abel.** Abel's theorem identifies the boundary limit of the power series
   with `l`, so `l = lim_{x→1⁻} log(1+x)/x`.
4. **Continuity.** `x ↦ log(1+x)/x` is continuous at `1` with value
   `log 2 / 1 = log 2`, pinning `l = log 2`.

## Status
- [x] Complete proof, 0 sorries
- [x] `altHarmonic_tendsto_log_two`: partial sums `→ log 2`
- [x] `not_summable_altTerm`: the series is only *conditionally* convergent
  (no `tsum`/`HasSum` value exists), justifying the ordered-limit formulation
- [x] Generating-function identity and convergence as reusable lemmas

## Mathlib Dependencies
- `Real.hasSum_pow_div_log_of_abs_lt_one` (Mercator series, `|x| < 1`)
- `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` (Abel's limit theorem)
- `Antitone.tendsto_alternating_series_of_tendsto_zero` (alternating series test)
-/

namespace HarmonicAlt

open Filter Finset
open scoped Topology

/-- The `n`-th term of the alternating harmonic series, `(-1)^n / (n+1)`.
Indexing from `0`, so `altTerm 0 = 1`, `altTerm 1 = -1/2`, `altTerm 2 = 1/3`, … -/
noncomputable def altTerm (n : ℕ) : ℝ := (-1) ^ n / (n + 1)

/-- The `N`-th partial sum `∑_{i<N} (-1)^i/(i+1)`. -/
noncomputable def altPartial (N : ℕ) : ℝ := ∑ i ∈ range N, altTerm i

/-- **Generating function of the alternating harmonic series.**
For `|x| < 1` and `x ≠ 0`, the power series `∑ (-1)^n/(n+1) · xⁿ` evaluates to
`log(1+x)/x`. Derived from the Mercator series `∑ y^(n+1)/(n+1) = -log(1-y)` at
`y = -x`, scaled by `-1/x`. -/
theorem hasSum_altTerm_mul_pow {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasSum (fun n => altTerm n * x ^ n) (Real.log (1 + x) / x) := by
  -- Mercator series at `-x`.
  have hbase : HasSum (fun n : ℕ => (-x) ^ (n + 1) / ((n : ℝ) + 1)) (-Real.log (1 - -x)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by rwa [abs_neg])
  -- Scale by `-1/x`.
  have hscaled := hbase.mul_left (-1 / x)
  -- Identify the value.
  have hval : (-1 / x) * (-Real.log (1 - -x)) = Real.log (1 + x) / x := by
    rw [show (1 : ℝ) - -x = 1 + x by ring]
    field_simp
  -- Identify the terms.
  have hterm : (fun n : ℕ => (-1 / x) * ((-x) ^ (n + 1) / ((n : ℝ) + 1)))
      = (fun n : ℕ => altTerm n * x ^ n) := by
    funext n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp only [altTerm]
    rw [neg_pow, pow_succ (-1 : ℝ) n, pow_succ x n]
    field_simp
  rw [hval, hterm] at hscaled
  exact hscaled

/-- **Convergence of the alternating harmonic series** via the alternating
series test: the terms `1/(n+1)` are antitone and tend to `0`. -/
theorem exists_tendsto_altPartial : ∃ l : ℝ, Tendsto altPartial atTop (𝓝 l) := by
  have hanti : Antitone (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
    intro a b hab
    exact one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hab 1)
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero hzero
  refine ⟨l, hl.congr fun n => ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [altTerm]
  ring

/-- **The alternating harmonic series sums to `log 2`** (partial-sum form):
`1 - 1/2 + 1/3 - 1/4 + ⋯ → log 2`. -/
theorem altHarmonic_tendsto_log_two :
    Tendsto altPartial atTop (𝓝 (Real.log 2)) := by
  obtain ⟨l, hl⟩ := exists_tendsto_altPartial
  -- Abel's limit theorem: the power series has boundary limit `l` as `x → 1⁻`.
  have abel : Tendsto (fun x => ∑' n, altTerm n * x ^ n) (𝓝[<] (1 : ℝ)) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  -- On `(0,1)` the power series equals `log(1+x)/x`.
  have hgen : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ)) (𝓝 l) := by
    refine abel.congr' ?_
    filter_upwards
      [(eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
       (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[<] (1 : ℝ), x ∈ Set.Iio (1 : ℝ))]
      with x hx0 hxlt
    have hax : |x| < 1 := by
      rw [abs_lt]; exact ⟨by linarith, hxlt⟩
    exact (hasSum_altTerm_mul_pow hax (ne_of_gt hx0)).tsum_eq
  -- Continuity pins the limit to `log 2`.
  have hcont : Tendsto (fun x : ℝ => Real.log (1 + x) / x) (𝓝[<] (1 : ℝ))
      (𝓝 (Real.log 2)) := by
    have hlog : Tendsto (fun x : ℝ => Real.log (1 + x)) (𝓝 (1 : ℝ)) (𝓝 (Real.log 2)) := by
      have : Real.log 2 = Real.log (1 + 1) := by norm_num
      rw [this]
      exact ((Real.continuousAt_log (by norm_num : (1 : ℝ) + 1 ≠ 0)).comp
        (by fun_prop : ContinuousAt (fun x : ℝ => 1 + x) 1)).tendsto
    have hden : Tendsto (fun x : ℝ => x) (𝓝 (1 : ℝ)) (𝓝 (1 : ℝ)) := tendsto_id
    have hdiv := hlog.div hden (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at hdiv
    exact hdiv.mono_left nhdsWithin_le_nhds
  -- Uniqueness of limits forces `l = log 2`.
  have : l = Real.log 2 := tendsto_nhds_unique hgen hcont
  rwa [this] at hl

/-- **The alternating harmonic series is not (unconditionally) summable.**
Although the partial sums converge to `log 2`, the convergence is only
*conditional*: `∑ |(-1)^n/(n+1)| = ∑ 1/(n+1)` diverges. Over `ℝ` (a
finite-dimensional space) unconditional summability coincides with absolute
summability, so `altTerm` is not `Summable`. This is exactly why the value
must be defined via the *ordered* limit of partial sums (and reached through
Abel's theorem), not via `tsum`. -/
theorem not_summable_altTerm : ¬ Summable altTerm := by
  rw [← summable_norm_iff]
  have hnorm : (fun n => ‖altTerm n‖) = (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    funext n
    simp only [altTerm, norm_div, norm_pow, norm_neg, norm_one, one_pow]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm]
  have h := mt (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
    Real.not_summable_one_div_natCast
  simpa using h
