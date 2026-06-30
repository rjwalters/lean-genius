import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-
# Egorov's Theorem: a.e. Convergence is "Almost" Uniform Convergence

## What This Proves

**Egorov's theorem** (Egorov 1911, Severini 1910) is a cornerstone of real
analysis bridging two notions of convergence. On a set `s` of *finite* measure,
if a sequence of (strongly) measurable functions `fₙ → g` almost everywhere,
then for every `ε > 0` there is a measurable subset `t ⊆ s` with `μ t ≤ ε` on
which we may *throw away*, so that `fₙ → g` **uniformly** on `s \ t`. In other
words, almost-everywhere convergence is uniform convergence off an arbitrarily
small set.

The general theorem is `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto` in
Mathlib; we restate it cleanly for the sequential (`ℕ`-indexed) case as
`egorov_uniform_off_small_set`.

The mathematical substance of this file is the **canonical worked example** that
makes Egorov's theorem vivid, together with the matching **sharpness** result:

* `pow_ae_tendsto_zero_on_Icc` — the sequence `fₙ(x) = xⁿ` on `[0,1]` converges
  to `0` Lebesgue-almost-everywhere (the only exceptional point is `x = 1`).

* `pow_egorov_on_Icc` — Egorov applied to `xⁿ` on `[0,1]`: for every `ε > 0`
  there is a measurable `t ⊆ [0,1]` of measure `≤ ε` with `xⁿ → 0` uniformly on
  `[0,1] \ t`.

* `pow_not_tendstoUniformlyOn_Ico` — **necessity of removing a set**: `xⁿ` does
  *not* converge uniformly to `0` on the half-open interval `[0,1)`, even though
  it converges there *everywhere* pointwise. This is exactly the phenomenon
  Egorov tames: the convergence is genuinely non-uniform, and no countable
  amount of pointwise control prevents `supₓ xⁿ = 1` for every `n`.

Together these show Egorov's theorem is not vacuous on this example: uniform
convergence on the whole interval fails, but uniform convergence off a small
set holds.

## Why It Is Not in Mathlib

Mathlib contains the abstract theorem but no formalized instance demonstrating
its non-vacuity, and no statement that `xⁿ` fails to converge uniformly on
`[0,1)`. The example, the a.e.-convergence verification, and the non-uniformity
witness are the new content.

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies
only on Mathlib's measure theory and the foundational axioms `propext`,
`Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace EgorovTheorem

/-! ## The general theorem (sequential form) -/

/-- **Egorov's theorem**, stated for sequences (`ℕ`-indexed). If `fₙ → g`
almost everywhere on a measurable set `s` of finite measure, then for every
`ε > 0` there is a measurable `t ⊆ s` with `μ t ≤ ε` such that `fₙ → g`
uniformly on `s \ t`. This is `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`
specialized to the index type `ℕ`. -/
theorem egorov_uniform_off_small_set
    {α β : Type*} [MeasurableSpace α] {μ : Measure α} [PseudoEMetricSpace β]
    {f : ℕ → α → β} {g : α → β} {s : Set α}
    (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hsm : MeasurableSet s) (hs : μ s ≠ ∞)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧
      TendstoUniformlyOn f g atTop (s \ t) :=
  tendstoUniformlyOn_of_ae_tendsto hf hg hsm hs hfg hε

/-! ## The canonical example: `xⁿ` on the unit interval -/

/-- The sequence `xⁿ` converges to `0` Lebesgue-almost-everywhere on `[0,1]`:
the only point of `[0,1]` at which it fails to tend to `0` is `x = 1`, a null
set. -/
theorem pow_ae_tendsto_zero_on_Icc :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
      Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [ae_iff]
  refine measure_mono_null (t := ({1} : Set ℝ)) ?_ Real.volume_singleton
  intro x hx
  rw [mem_setOf_eq, _root_.not_imp] at hx
  obtain ⟨hmem, hlim⟩ := hx
  rw [mem_Icc] at hmem
  rw [mem_singleton_iff]
  by_contra hne
  exact hlim (tendsto_pow_atTop_nhds_zero_of_lt_one hmem.1 (lt_of_le_of_ne hmem.2 hne))

/-- **Egorov's theorem applied to `xⁿ` on `[0,1]`.** For every `ε > 0` there is
a measurable set `t ⊆ [0,1]` with Lebesgue measure `≤ ε` such that `xⁿ → 0`
uniformly on `[0,1] \ t`. -/
theorem pow_egorov_on_Icc {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ Set.Icc (0 : ℝ) 1, MeasurableSet t ∧ volume t ≤ ENNReal.ofReal ε ∧
      TendstoUniformlyOn (fun n x => x ^ n) (fun _ => 0) atTop (Set.Icc 0 1 \ t) := by
  apply tendstoUniformlyOn_of_ae_tendsto
  · exact fun n => (continuous_pow n).stronglyMeasurable
  · exact stronglyMeasurable_const
  · exact measurableSet_Icc
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · exact pow_ae_tendsto_zero_on_Icc
  · exact hε

/-! ## Sharpness: the convergence is genuinely non-uniform -/

/-- For every exponent `N` there is a point `x ∈ [0,1)` with `xᴺ ≥ 1/2`. This is
the key obstruction to uniform convergence: no matter how large `N` is, `xⁿ`
stays bounded away from `0` somewhere in `[0,1)`. -/
theorem exists_pow_ge_half (N : ℕ) : ∃ x ∈ Set.Ico (0 : ℝ) 1, (1 / 2 : ℝ) ≤ x ^ N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨0, ⟨le_refl 0, by norm_num⟩, ?_⟩
    rw [hN, pow_zero]; norm_num
  · have hcont : ContinuousOn (fun x : ℝ => x ^ N) (Set.Icc 0 1) :=
      (continuous_pow N).continuousOn
    have himg := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hcont
    have hmem : (1 / 2 : ℝ) ∈ Set.Icc ((0 : ℝ) ^ N) ((1 : ℝ) ^ N) := by
      rw [zero_pow hN.ne', one_pow, mem_Icc]; norm_num
    obtain ⟨x, hxmem, hxval⟩ := himg hmem
    dsimp only at hxval
    rw [mem_Icc] at hxmem
    refine ⟨x, ⟨hxmem.1, ?_⟩, le_of_eq hxval.symm⟩
    rcases hxmem.2.eq_or_lt with h | h
    · rw [h, one_pow] at hxval; norm_num at hxval
    · exact h

/-- **Necessity of Egorov's exceptional set.** The sequence `xⁿ` does *not*
converge uniformly to `0` on `[0,1)`, despite converging to `0` at *every* point
of `[0,1)`. Thus the small set removed by Egorov's theorem cannot in general be
omitted: pointwise (indeed everywhere) convergence does not upgrade to uniform
convergence. -/
theorem pow_not_tendstoUniformlyOn_Ico :
    ¬ TendstoUniformlyOn (fun n x => x ^ n) (fun _ => (0 : ℝ)) atTop (Set.Ico (0 : ℝ) 1) := by
  intro h
  rw [Metric.tendstoUniformlyOn_iff] at h
  have key := h (1 / 2) (by norm_num)
  rw [eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  obtain ⟨x, hx, hxpow⟩ := exists_pow_ge_half N
  have hlt := hN N (le_refl N) x hx
  simp only at hlt
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (pow_nonneg hx.1 N)] at hlt
  linarith

end EgorovTheorem
