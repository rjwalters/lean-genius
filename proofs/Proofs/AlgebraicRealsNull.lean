import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountable

/-!
# The Algebraic Reals are Lebesgue-Null (Measure Zero)

## Open Question (algebraic-numbers-countable-oq-07)

The companion entry `algebraic-numbers-countable` proves the algebraic reals
`{x : ℝ | IsAlgebraic ℚ x}` are *countable*, and `algebraic-reals-meager`
strengthens "countable" to the topological statement that they are *meagre*
(first category in `ℝ`). Both of those entries explicitly invoke a third,
*measure-theoretic*, notion of smallness that they leave unformalized:

> "Topological smallness sits alongside the measure-theoretic smallness
>  (the algebraic reals are Lebesgue-null) and the cardinality smallness
>  (they are countable)."

This entry closes that gap. It supplies the **measure** pillar of the
trichotomy:

    algebraic reals  ⊆  ℝ        are simultaneously
      • countable          (cardinality:  ℵ₀ < 𝔠)           — algebraic-numbers-countable
      • meagre             (Baire category: first category) — algebraic-reals-meager
      • Lebesgue-null      (measure:       μ = 0)           — THIS ENTRY

Dually, the **transcendental** reals are co-small in all three senses: they
have full measure, so *almost every real number is transcendental*. This is
the measure-theoretic counterpart of Cantor's cardinality argument
("almost all reals are transcendental" in the sense of ℵ₀ < 𝔠) and of the
Baire-category argument (the transcendentals are comeagre, hence dense).

The mathematics is short — a countable set is null because Lebesgue measure
has no atoms — but the three small/co-small dichotomies (cardinality,
category, measure) are genuinely independent notions, and only this one was
missing from the gallery. A measure-theoretic *existence* corollary
(`exists_transcendental_of_pos_measure`) is included: any set of positive
Lebesgue measure must contain a transcendental number. This complements the
two classical existence proofs already in the gallery — Cantor's
counting argument and Liouville's explicit construction — with a third,
measure-theoretic, route to the existence of transcendentals.

## Main results

* `algebraic_reals_null`           : `volume {x : ℝ | IsAlgebraic ℚ x} = 0`
* `ae_transcendental`              : almost every real is transcendental
* `transcendental_reals_conull`    : the transcendentals have full (conull) measure
* `transcendental_full_on_interval`: transcendentals fill almost all of any interval
* `exists_transcendental_of_pos_measure`
                                   : a positive-measure set contains a transcendental
* `algebraic_complex_null`         : `volume {z : ℂ | IsAlgebraic ℚ z} = 0`

0 sorries, 0 axioms (no `native_decide`).
-/

open MeasureTheory Set

namespace AlgebraicRealsNull

-- ============================================================================
-- § 1. The algebraic reals are null
-- ============================================================================

/-- **The algebraic reals have Lebesgue measure zero.**

A countable set is null for any measure without atoms, and Lebesgue measure on
`ℝ` has no atoms (`noAtoms_volume`). The countability of `{x | IsAlgebraic ℚ x}`
is the parent result `AlgebraicNumbersCountable.algebraic_reals_countable`. -/
theorem algebraic_reals_null :
    volume {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  (AlgebraicNumbersCountable.algebraic_reals_countable).measure_zero volume

/-- The algebraic reals of degree `≤ d` are null (a subset of a null set). -/
theorem algebraicRealsOfBoundedDegree_null (d : ℕ) :
    volume (AlgebraicNumbersCountable.algebraicRealsOfBoundedDegree d) = 0 :=
  (AlgebraicNumbersCountable.algebraicRealsOfBoundedDegree_countable d).measure_zero volume

-- ============================================================================
-- § 2. The transcendentals are conull: almost every real is transcendental
-- ============================================================================

/-- The complement of the transcendentals is exactly the algebraic reals.

`Transcendental ℚ x` is by definition `¬ IsAlgebraic ℚ x`, so the set of
transcendentals is the complement of the algebraic set, and taking the
complement again returns the algebraic set. -/
theorem compl_transcendental_eq_algebraic :
    {x : ℝ | Transcendental ℚ x}ᶜ = {x : ℝ | IsAlgebraic ℚ x} := by
  ext x
  simp only [mem_compl_iff, mem_setOf_eq, Transcendental, not_not]

/-- **The transcendental reals are conull**: their complement (the algebraic
reals) has measure zero. Equivalently, the transcendentals have full measure. -/
theorem transcendental_reals_conull :
    volume {x : ℝ | Transcendental ℚ x}ᶜ = 0 := by
  rw [compl_transcendental_eq_algebraic]
  exact algebraic_reals_null

/-- **Almost every real number is transcendental.**

Restated as an almost-everywhere statement for the Lebesgue measure: the set of
`x` with `Transcendental ℚ x` is conull. -/
theorem ae_transcendental :
    ∀ᵐ x : ℝ ∂volume, Transcendental ℚ x := by
  have hset : {x : ℝ | Transcendental ℚ x} = {x : ℝ | IsAlgebraic ℚ x}ᶜ := by
    ext x; simp only [mem_setOf_eq, mem_compl_iff, Transcendental]
  rw [Filter.eventually_iff, hset]
  exact compl_mem_ae_iff.mpr algebraic_reals_null

-- ============================================================================
-- § 3. Transcendentals fill almost all of every interval
-- ============================================================================

/-- The algebraic reals contribute nothing to the measure of any interval:
`volume (Ioo a b ∩ algebraic) = 0`. -/
theorem algebraic_inter_interval_null (a b : ℝ) :
    volume (Ioo a b ∩ {x : ℝ | IsAlgebraic ℚ x}) = 0 :=
  measure_mono_null (inter_subset_right) algebraic_reals_null

/-- **The transcendentals fill almost all of any interval**: the part of
`Ioo a b` consisting of transcendental numbers has the full measure of the
interval, `ENNReal.ofReal (b - a)`. -/
theorem transcendental_full_on_interval (a b : ℝ) :
    volume (Ioo a b ∩ {x : ℝ | Transcendental ℚ x}) = ENNReal.ofReal (b - a) := by
  have hset : Ioo a b ∩ {x : ℝ | Transcendental ℚ x}
      = Ioo a b \ {x : ℝ | IsAlgebraic ℚ x} := by
    ext x
    simp only [mem_inter_iff, mem_diff, mem_setOf_eq, Transcendental]
  rw [hset, measure_diff_null algebraic_reals_null, Real.volume_Ioo]

-- ============================================================================
-- § 4. Measure-theoretic existence of transcendentals
-- ============================================================================

/-- **Any set of positive Lebesgue measure contains a transcendental number.**

If `s` had no transcendental element, then `s ⊆ {algebraic}`, forcing
`volume s ≤ volume {algebraic} = 0`, contradicting `0 < volume s`.

This is a third, measure-theoretic, existence proof for transcendentals,
alongside Cantor's counting argument and Liouville's explicit construction. -/
theorem exists_transcendental_of_pos_measure {s : Set ℝ} (hs : 0 < volume s) :
    ∃ x ∈ s, Transcendental ℚ x := by
  by_contra h
  push_neg at h
  -- `h : ∀ x ∈ s, ¬ Transcendental ℚ x`, i.e. every point of `s` is algebraic.
  have hsub : s ⊆ {x : ℝ | IsAlgebraic ℚ x} := by
    intro x hx
    have := h x hx
    simpa only [mem_setOf_eq, Transcendental, not_not] using this
  have : volume s = 0 := measure_mono_null hsub algebraic_reals_null
  rw [this] at hs
  exact lt_irrefl 0 hs

/-- Every interval `Ioo a b` with `a < b` contains a transcendental number —
the special case of `exists_transcendental_of_pos_measure` for intervals. -/
theorem exists_transcendental_mem_Ioo {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Ioo a b, Transcendental ℚ x := by
  apply exists_transcendental_of_pos_measure
  rw [Real.volume_Ioo]
  simp [ENNReal.ofReal_pos, sub_pos, hab]

-- ============================================================================
-- § 5. The complex algebraic numbers are null
-- ============================================================================

/-- Lebesgue measure on `ℂ` has no atoms.

Transport the singleton `{z}` through the measure-preserving identification
`ℂ ≃ᵐ ℝ × ℝ`; its image is a single point of `ℝ × ℝ`, which is null because
the planar Lebesgue measure has no atoms. -/
instance : NoAtoms (volume : Measure ℂ) := by
  have hpair : NoAtoms (volume : Measure (ℝ × ℝ)) := Measure.prod.instNoAtoms_fst
  refine ⟨fun z => ?_⟩
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hpre : ({z} : Set ℂ)
      = Complex.measurableEquivRealProd ⁻¹' {Complex.measurableEquivRealProd z} := by
    ext w
    simp only [mem_preimage, mem_singleton_iff, Complex.measurableEquivRealProd_apply,
      Prod.mk.injEq, Complex.ext_iff]
  rw [hpre, hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet]
  exact measure_singleton _

/-- **The complex algebraic numbers have (planar) Lebesgue measure zero.**

Same argument as on `ℝ`: the set `{z : ℂ | IsAlgebraic ℚ z}` is countable
(`AlgebraicNumbersCountable.algebraic_complex_countable`) and `volume` on `ℂ`
has no atoms. -/
theorem algebraic_complex_null :
    volume {z : ℂ | IsAlgebraic ℚ z} = 0 :=
  (AlgebraicNumbersCountable.algebraic_complex_countable).measure_zero volume

/-- Almost every complex number is transcendental. -/
theorem ae_transcendental_complex :
    ∀ᵐ z : ℂ ∂volume, Transcendental ℚ z := by
  have hset : {z : ℂ | Transcendental ℚ z} = {z : ℂ | IsAlgebraic ℚ z}ᶜ := by
    ext z; simp only [mem_setOf_eq, mem_compl_iff, Transcendental]
  rw [Filter.eventually_iff, hset]
  exact compl_mem_ae_iff.mpr algebraic_complex_null

-- ============================================================================
-- § 6. Hausdorff dimension zero — a sharpening of Lebesgue-null
-- ============================================================================

/-!
Lebesgue-null (`algebraic_reals_null`) is the order-`1` slice of a much stronger
statement: the algebraic reals have **Hausdorff dimension zero**.  A countable set
has Hausdorff dimension `0` (`Set.Countable.dimH_zero`), and dimension `0` forces
*every* positive-order Hausdorff measure to vanish, not merely the order-`1`
(Lebesgue) one.  So the algebraic reals are null for the entire one-parameter
family of Hausdorff gauges `μH[d]`, `d > 0` — an infinitely stronger form of
metric smallness than the single Lebesgue-null fact.

A purely dimensional corollary also recovers the topological largeness of the
transcendentals: since `dimH {algebraic} = 0 < finrank ℝ ℝ`, the complement is
dense (`dense_compl_of_dimH_lt_finrank`) — the transcendentals are dense in `ℝ`
(and, by the same argument with `finrank ℝ ℂ = 2`, in `ℂ`), obtained here from the
dimension bound rather than from the Baire-category argument.
-/

/-- **The algebraic reals have Hausdorff dimension zero.**  Sharper than
Lebesgue-null: a countable set has Hausdorff dimension `0` (`Set.Countable.dimH_zero`),
and dimension `0` kills every positive-order Hausdorff measure at once. -/
theorem algebraic_reals_dimH_zero :
    dimH {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  (AlgebraicNumbersCountable.algebraic_reals_countable).dimH_zero

/-- **Every positive-order Hausdorff measure of the algebraic reals vanishes.**
For each `d > 0`, `μH[d] {algebraic} = 0`.  The order-`d = 1` case is exactly
`algebraic_reals_null` (Lebesgue-null); dimension zero delivers the whole scale
`d > 0`, so the algebraic reals are null for *every* Hausdorff gauge, not just
Lebesgue measure. -/
theorem algebraic_reals_hausdorffMeasure_zero {d : NNReal} (hd : 0 < d) :
    μH[(d : ℝ)] {x : ℝ | IsAlgebraic ℚ x} = 0 :=
  hausdorffMeasure_of_dimH_lt (by
    rw [algebraic_reals_dimH_zero]; exact_mod_cast hd)

/-- **The complex algebraic numbers have Hausdorff dimension zero.**  Same
countable-set argument as on `ℝ`. -/
theorem algebraic_complex_dimH_zero :
    dimH {z : ℂ | IsAlgebraic ℚ z} = 0 :=
  (AlgebraicNumbersCountable.algebraic_complex_countable).dimH_zero

/-- **The transcendental reals are dense**, obtained from the dimensional bound:
`dimH {algebraic} = 0 < 1 = finrank ℝ ℝ`, so the complement of the algebraic reals
is dense (`dense_compl_of_dimH_lt_finrank`).  A dimension-theoretic route to the
topological largeness of the transcendentals, independent of Baire category. -/
theorem transcendental_reals_dense :
    Dense {x : ℝ | Transcendental ℚ x} := by
  have hcompl : {x : ℝ | Transcendental ℚ x} = {x : ℝ | IsAlgebraic ℚ x}ᶜ := by
    ext x; simp only [mem_setOf_eq, mem_compl_iff, Transcendental]
  rw [hcompl]
  apply dense_compl_of_dimH_lt_finrank
  rw [algebraic_reals_dimH_zero]
  exact_mod_cast Module.finrank_pos

/-- **The transcendental complex numbers are dense**, by the same dimensional
argument with `finrank ℝ ℂ = 2 > 0 = dimH {algebraic}`. -/
theorem transcendental_complex_dense :
    Dense {z : ℂ | Transcendental ℚ z} := by
  have hcompl : {z : ℂ | Transcendental ℚ z} = {z : ℂ | IsAlgebraic ℚ z}ᶜ := by
    ext z; simp only [mem_setOf_eq, mem_compl_iff, Transcendental]
  rw [hcompl]
  apply dense_compl_of_dimH_lt_finrank
  rw [algebraic_complex_dimH_zero]
  exact_mod_cast Module.finrank_pos

end AlgebraicRealsNull
