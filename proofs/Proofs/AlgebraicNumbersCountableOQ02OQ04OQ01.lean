import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Tactic
import Proofs.AlgebraicNumbersCountableOQ02OQ04

/-!
# The Computable Reals are Lebesgue-Null (oq-02-oq-04-oq-01)

## Open Question (algebraic-numbers-countable-oq-02-oq-04-oq-01)

The parent entry `AlgebraicNumbersCountableOQ02OQ04` established that the
**computable** real numbers form a set that is, simultaneously:

* **countable** (`ℵ₀`, cardinality) — `computable_reals_countable`;
* **meagre** (first Baire category) — `computable_reals_meagre`;
* yet **dense** — `computable_reals_dense`.

The one classical notion of "negligible" it never addressed is the
**measure-theoretic** one. This entry closes that gap: the computable reals are a
**Lebesgue-null** set, and their complement — the non-computable reals — carries
the *full* Lebesgue measure of the line. Concretely, "a real chosen uniformly at
random is, almost surely, non-computable".

This completes the negligibility profile of `{r | IsComputable r}` across the
three independent lenses that classical analysis uses to say a subset of `ℝ` is
"small":

    cardinality   : ℵ₀      (countable)            OQ04 S2–S4
    category      : meagre  (1st Baire category)   OQ04 S8
    measure       : null    (Lebesgue measure 0)   THIS FILE

— all three hold at once, while the set remains topologically **dense**. This is
exactly the profile carried by `ℚ` itself, now transported to the strictly finer
computable/non-computable partition. Dually, the non-computable reals are of full
cardinality `𝔠`, comeagre (residual), and of full Lebesgue measure: "generic" in
all three senses.

## Main Results

* `computable_reals_null` — `volume {r | IsComputable r} = 0`.
* `ae_not_isComputable` — `∀ᵐ r, ¬ IsComputable r` (almost every real is
  non-computable).
* `ae_mem_nonComputableReals` — the measure-theoretic restatement.
* `volume_restrict_nonComputableReals` — the non-computable reals carry the full
  Lebesgue measure: `volume.restrict nonComputableReals = volume`.
* `volume_Ioo_inter_nonComputableReals` / `..._eq` — the non-computable reals
  fill *every* interval in measure: `volume (Ioo a b ∩ nonComputableReals)
  = volume (Ioo a b) = ofReal (b - a)`.
* `computable_reals_null_meagre_dense` — the triple-negligibility-yet-dense
  capstone for the computable reals.
* `nonComputableReals_full_measure_residual_continuum` — the dual: full measure,
  residual, and cardinality `𝔠` for the non-computable reals.

## Proof Strategy

Everything rests on one Mathlib fact: in a measure space with **no atoms**, every
countable set is null (`Set.Countable.measure_zero`), and Lebesgue measure on `ℝ`
is atomless (`MeasureTheory.Real.noAtoms_volume`). The upper cardinality/category
work is entirely inherited from OQ04; this file only adds the measure layer and
the two capstones bundling measure with the pre-existing lenses.

* Null: `computable_reals_countable.measure_zero volume`.
* Almost-everywhere non-computability: `Set.Countable.ae_notMem`.
* Full measure of the complement: `Set.Countable.measure_restrict_compl`.
* Interval-filling: `measure_diff_null` applied to `Ioo a b`, exactly as in
  Mathlib's `Portmanteau` development.

## References

- Mathlib `Set.Countable.measure_zero`, `Set.Countable.ae_notMem`,
  `Set.Countable.measure_restrict_compl` — `MeasureTheory.Measure.Typeclasses.NoAtoms`.
- Mathlib `Real.noAtoms_volume`, `Real.volume_Ioo` — `MeasureTheory.Measure.Lebesgue.Basic`.
- Oxtoby, *Measure and Category* (1980) — the measure/category duality this file
  instantiates for the computable reals.
- Turing, "On Computable Numbers" (1936).

Tags: set-theory, measure-theory, real-analysis, computability, cardinality
-/

namespace AlgebraicNumbersCountableOQ02OQ04OQ01

open MeasureTheory Filter Cardinal
open AlgebraicNumbersCountableOQ02OQ04

/-! ## The measure layer: computable reals are Lebesgue-null -/

/-- **The computable reals are Lebesgue-null.**

    Lebesgue measure on `ℝ` has no atoms (`Real.noAtoms_volume`), and every
    countable set in an atomless measure space is null
    (`Set.Countable.measure_zero`). Since the computable reals are countable
    (OQ04 `computable_reals_countable`), they have Lebesgue measure zero.

    This is the measure-theoretic counterpart of OQ04's `computable_reals_meagre`
    (category) and `computable_reals_countable` (cardinality): the computable
    reals are negligible in *every* classical sense. -/
theorem computable_reals_null :
    volume {r : ℝ | IsComputable r} = 0 :=
  computable_reals_countable.measure_zero volume

/-- **Almost every real number is non-computable.**

    A `volume`-almost-everywhere statement: the set of computable reals being
    null (`computable_reals_null`), its complement is conull, so for almost every
    `r : ℝ`, `r` fails to be computable. This is the sharp measure-theoretic form
    of Turing's negative observation `exists_non_computable_real`: not merely that
    *some* real is non-computable, but that *almost all* are. -/
theorem ae_not_isComputable :
    ∀ᵐ r : ℝ, ¬ IsComputable r := by
  simpa using computable_reals_countable.ae_notMem (volume : Measure ℝ)

/-- **Almost every real lies in the non-computable reals** — the same statement
    as `ae_not_isComputable`, phrased with the `nonComputableReals` set of OQ04. -/
theorem ae_mem_nonComputableReals :
    ∀ᵐ r : ℝ, r ∈ nonComputableReals := by
  simpa [nonComputableReals] using ae_not_isComputable

/-- **The non-computable reals carry the full Lebesgue measure.**

    Restricting Lebesgue measure to the non-computable reals changes nothing:
    `volume.restrict nonComputableReals = volume`. This is
    `Set.Countable.measure_restrict_compl` applied to the countable computable
    reals (`nonComputableReals` is their complement). It is the exact
    measure-theoretic dual of OQ04's `card_nonComputableReals_eq_continuum`
    (the complement keeps *all* of the line's cardinality) and
    `nonComputableReals_residual` (the complement keeps *all* of the line's Baire
    category). -/
theorem volume_restrict_nonComputableReals :
    (volume : Measure ℝ).restrict nonComputableReals = volume := by
  have h : nonComputableReals = ({r : ℝ | IsComputable r})ᶜ := by ext r; rfl
  rw [h]
  exact computable_reals_countable.measure_restrict_compl volume

/-! ## The non-computable reals fill every interval in measure -/

/-- **The non-computable reals fill every open interval in measure.**

    For any `a b : ℝ`, `volume (Ioo a b ∩ nonComputableReals) = volume (Ioo a b)`:
    removing the (null) computable reals from an interval does not change its
    measure. Proof: `Ioo a b ∩ nonComputableReals = Ioo a b \ {computable}`, and
    `measure_diff_null` discards the null computable part. -/
theorem volume_Ioo_inter_nonComputableReals (a b : ℝ) :
    volume (Set.Ioo a b ∩ nonComputableReals) = volume (Set.Ioo a b) := by
  have h : nonComputableReals = ({r : ℝ | IsComputable r})ᶜ := by ext r; rfl
  rw [h, ← Set.diff_eq]
  exact measure_diff_null computable_reals_null

/-- **Quantitative interval-filling.** The non-computable reals occupy an interval
    `Ioo a b` with its full length `b - a`:
    `volume (Ioo a b ∩ nonComputableReals) = ENNReal.ofReal (b - a)`. -/
theorem volume_Ioo_inter_nonComputableReals_eq (a b : ℝ) :
    volume (Set.Ioo a b ∩ nonComputableReals) = ENNReal.ofReal (b - a) := by
  rw [volume_Ioo_inter_nonComputableReals, Real.volume_Ioo]

/-! ## Capstones: negligibility and genericity across all three lenses -/

/-- **Capstone (computable side): countable, null, meagre — yet dense.**

    Bundles the three independent notions of "negligible" for the computable
    reals — cardinality (`countable`), measure (`null`), category (`meagre`) —
    together with the fact that the set is nonetheless topologically `Dense`.
    This is the canonical signature of a countable dense set (the same profile
    as `ℚ`), now established for the strictly finer set of computable reals. -/
theorem computable_reals_null_meagre_dense :
    Set.Countable {r : ℝ | IsComputable r} ∧
      volume {r : ℝ | IsComputable r} = 0 ∧
      IsMeagre {r : ℝ | IsComputable r} ∧
      Dense {r : ℝ | IsComputable r} :=
  ⟨computable_reals_countable, computable_reals_null,
   computable_reals_meagre, computable_reals_dense⟩

/-- **Capstone (non-computable side): full measure, residual, cardinality `𝔠`.**

    The measure-theoretic dual of the computable side. The non-computable reals
    are "generic" in all three classical senses: they carry the full Lebesgue
    measure of the line (`volume.restrict nonComputableReals = volume`), they are
    comeagre (`residual`), and they have full cardinality `𝔠`. A real drawn at
    random — whether "random" is read as measure-theoretic, Baire-generic, or
    merely cardinality-typical — is non-computable. -/
theorem nonComputableReals_full_measure_residual_continuum :
    (volume : Measure ℝ).restrict nonComputableReals = volume ∧
      nonComputableReals ∈ residual ℝ ∧
      (#(↑nonComputableReals : Set ℝ) : Cardinal) = 𝔠 :=
  ⟨volume_restrict_nonComputableReals, nonComputableReals_residual,
   card_nonComputableReals_eq_continuum⟩

end AlgebraicNumbersCountableOQ02OQ04OQ01
