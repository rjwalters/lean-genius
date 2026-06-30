/-
  Lebesgue Measure OQ-04
  ----------------------
  Cantor Set: an uncountable, Lebesgue-null subset of [0, 1].

  The ternary Cantor set `C` is the prototypical example of a set that is
  "large" in the topological / cardinality sense (uncountable, in fact of the
  cardinality of the continuum) yet "small" in the measure-theoretic sense
  (Lebesgue measure zero).  This file proves both of these defining
  properties from Mathlib's `cantorSet` infrastructure
  (`Mathlib.Topology.Instances.CantorSet`):

    * `volume_cantorSet : volume cantorSet = 0`
        Each pre-Cantor set `preCantorSet n` has measure `(2/3)^n` because it
        is obtained by two ratio-`1/3` homotheties of the previous stage; the
        Cantor set is contained in every stage, so its measure is bounded by
        `(2/3)^n → 0`.

    * `not_countable_cantorSet : ¬ cantorSet.Countable`
        Mathlib provides `cantorSetEquivNatToBool : cantorSet ≃ (ℕ → Bool)`,
        and `ℕ → Bool` has cardinality `2 ^ ℵ₀ > ℵ₀`, hence is uncountable.

  The "paradox" is genuine: `C` has empty interior and measure zero, yet has
  the same cardinality as the whole interval `[0, 1]`.

  Everything here is fully verified: no axioms, no sorries.
-/
import Mathlib

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace LebesgueMeasureOQ04

/-! ## The Cantor set is Lebesgue-null

Each stage of the Cantor construction is two scaled copies of the previous
stage, each scaled by `1/3`.  We compute the measure of a ratio-`1/3`
homothety image, bound the measure of stage `n` by `(2/3)^n`, and take the
limit. -/

/-- The Lebesgue measure of a ratio-`1/3` homothety image of `s` is `(1/3) * volume s`.
This is the one-dimensional instance of `addHaar_image_homothety` (`finrank ℝ ℝ = 1`). -/
lemma volume_homothety_third_image (c : ℝ) (s : Set ℝ) :
    volume (AffineMap.homothety c (1 / 3 : ℝ) '' s) = ENNReal.ofReal (1 / 3) * volume s := by
  rw [Measure.addHaar_image_homothety]
  congr 1
  rw [Module.finrank_self]
  norm_num

/-- `x ↦ x / 3` is the homothety centred at `0` with ratio `1/3`. -/
lemma volume_div_three_image (s : Set ℝ) :
    volume ((fun x : ℝ => x / 3) '' s) = ENNReal.ofReal (1 / 3) * volume s := by
  have h : (fun x : ℝ => x / 3) = AffineMap.homothety (0 : ℝ) (1 / 3 : ℝ) := by
    funext x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  rw [h, volume_homothety_third_image]

/-- `x ↦ (2 + x) / 3` is the homothety centred at `1` with ratio `1/3`. -/
lemma volume_two_add_div_three_image (s : Set ℝ) :
    volume ((fun x : ℝ => (2 + x) / 3) '' s) = ENNReal.ofReal (1 / 3) * volume s := by
  have h : (fun x : ℝ => (2 + x) / 3) = AffineMap.homothety (1 : ℝ) (1 / 3 : ℝ) := by
    funext x
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  rw [h, volume_homothety_third_image]

/-- The order-`n` pre-Cantor set has Lebesgue measure at most `(2/3)^n`. -/
lemma volume_preCantorSet_le (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
  induction n with
  | zero => simp [preCantorSet_zero, Real.volume_Icc]
  | succ n ih =>
    rw [preCantorSet_succ]
    refine le_trans (measure_union_le _ _) ?_
    rw [volume_div_three_image, volume_two_add_div_three_image]
    calc
      ENNReal.ofReal (1 / 3) * volume (preCantorSet n)
            + ENNReal.ofReal (1 / 3) * volume (preCantorSet n)
          = ENNReal.ofReal (2 / 3) * volume (preCantorSet n) := by
            rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
            rw [show (1 / 3 : ℝ) + 1 / 3 = 2 / 3 by norm_num]
      _ ≤ ENNReal.ofReal (2 / 3) * ENNReal.ofReal ((2 / 3 : ℝ) ^ n) :=
            mul_le_mul' le_rfl ih
      _ = ENNReal.ofReal ((2 / 3 : ℝ) ^ (n + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 / 3)]
            congr 1
            rw [pow_succ]
            ring

/-- **The ternary Cantor set has Lebesgue measure zero.** -/
theorem volume_cantorSet : volume cantorSet = 0 := by
  refine le_antisymm ?_ (zero_le _)
  -- For every `n`, `volume cantorSet ≤ (2/3)^n` since `cantorSet ⊆ preCantorSet n`.
  have hbound : ∀ n : ℕ, volume cantorSet ≤ ENNReal.ofReal ((2 / 3 : ℝ) ^ n) := by
    intro n
    have hsub : cantorSet ⊆ preCantorSet n := Set.iInter_subset _ n
    exact le_trans (measure_mono hsub) (volume_preCantorSet_le n)
  -- The bound `(2/3)^n → 0`.
  have htend : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal ((2 / 3 : ℝ) ^ n))
      Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun n : ℕ => (2 / 3 : ℝ) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hr
    simpa using this
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hbound

/-! ## The Cantor set is uncountable

Mathlib gives a bijection `cantorSet ≃ (ℕ → Bool)`; the latter has cardinality
`2 ^ ℵ₀`, which exceeds `ℵ₀`. -/

/-- `ℕ → Bool` is uncountable: it has cardinality `2 ^ ℵ₀ > ℵ₀`. -/
instance : Uncountable (ℕ → Bool) := by
  rw [← Cardinal.aleph0_lt_mk_iff, ← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat]
  exact Cardinal.cantor _

/-- The ternary Cantor set is uncountable (as a subtype). -/
theorem uncountable_cantorSet : Uncountable cantorSet :=
  cantorSetEquivNatToBool.symm.injective.uncountable

/-- **The ternary Cantor set is uncountable.** -/
theorem not_countable_cantorSet : ¬ cantorSet.Countable := by
  rw [← Set.countable_coe_iff, not_countable_iff]
  exact uncountable_cantorSet

/-! ## Summary

Together, `volume_cantorSet` and `not_countable_cantorSet` exhibit `cantorSet`
as an uncountable null set: measure-theoretically negligible, yet of the
cardinality of the continuum. -/

/-- The Cantor set is a null set that is nonetheless uncountable. -/
theorem cantorSet_null_and_uncountable :
    volume cantorSet = 0 ∧ ¬ cantorSet.Countable :=
  ⟨volume_cantorSet, not_countable_cantorSet⟩

end LebesgueMeasureOQ04
