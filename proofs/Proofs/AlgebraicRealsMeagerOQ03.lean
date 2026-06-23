import Proofs.AlgebraicRealsMeager
import Proofs.AlgebraicRealsMeagerOQ02

/-!
# The Cardinality Axis: Measure-Small and Category-Small Sets Need Not Be Countable

## Open Question (algebraic-reals-meager — OQ-03)

The parent `algebraic-reals-meager` records *three* independent notions under which a
subset of `ℝ` can be "small":

* **cardinality-small** — countable;
* **measure-small** — Lebesgue-null;
* **category-small** — meagre (first Baire category).

The companion `algebraic-reals-meager-oq-02` settles the **measure ⊥ category** axis: the
Liouville numbers are comeagre yet null (category-large but measure-small), so neither of
those two notions implies the other.

This entry settles the remaining axis — **cardinality vs the other two** — which oq-02 does
not address. The point is that the separating examples are *uncountable*:

* a **meagre** set can be **uncountable** (category-small ⇏ countable), and
* a **null** set can be **uncountable** (measure-small ⇏ countable).

Equivalently, while every *countable* set is automatically both meagre and null
(`countable_isMeagre_and_null`), the converse fails badly in both directions. So
cardinality-smallness is strictly stronger than — and independent of — measure- and
category-smallness. Together with oq-02 this completes the pairwise independence of all
three notions.

The witnesses are the complementary pair `(𝓛ᶜ, 𝓛)` for `𝓛 =` the Liouville numbers:

* `𝓛` is null (Mathlib, via oq-02) yet uncountable — were it countable it would be meagre,
  contradicting its comeagreness (`not_isMeagre_of_mem_residual`);
* `𝓛ᶜ` is meagre yet of full Lebesgue measure (so uncountable, since countable sets are
  null). The full-measure step uses only countable subadditivity of the outer measure, so
  no measurability hypothesis is needed.

## Main Results

* `meagre_conull_compl_of_residual_null` — abstract engine: the complement of a residual
  null set is meagre and has full measure (measurability-free).
* `countable_isMeagre_and_null` — every countable subset of `ℝ` is *both* meagre and null:
  the "aligned" case from which the separating examples must therefore be uncountable.
* `exists_meagre_uncountable` — **category-small ⇏ countable**: a meagre set that is
  uncountable (the non-Liouville reals, uncountable because they have full measure).
* `exists_null_uncountable` — **measure-small ⇏ countable**: a null set that is uncountable
  (the Liouville numbers, uncountable because countable would force meagreness).
* `oq03_resolution` — the cardinality axis as a single statement, completing the three-way
  independence begun in oq-02.
-/

open MeasureTheory Filter Set AlgebraicRealsMeager AlgebraicRealsMeagerOQ02

namespace AlgebraicRealsMeagerOQ03

/-- Shorthand for the Liouville numbers, our separating set. -/
abbrev 𝓛 : Set ℝ := {x : ℝ | Liouville x}

/-! ## The abstract orthogonality engine -/

/-- **The complement of a residual null set is meagre and of full measure.** If `S` is
residual (comeagre) and Lebesgue-null, then `Sᶜ` is meagre and `volume Sᶜ = volume univ`.
The full-measure claim uses only countable subadditivity of the outer measure
(`measure_union_le`, valid for *all* sets), so no measurability hypothesis on `S` is
required. This is the engine behind the uncountability of the meagre witness below. -/
theorem meagre_conull_compl_of_residual_null {S : Set ℝ}
    (hres : S ∈ residual ℝ) (hnull : volume S = 0) :
    IsMeagre Sᶜ ∧ volume Sᶜ = volume (univ : Set ℝ) := by
  refine ⟨?_, ?_⟩
  · -- `IsMeagre Sᶜ` unfolds to `Sᶜᶜ ∈ residual`, i.e. `S ∈ residual`.
    simpa [IsMeagre, compl_compl] using hres
  · refine le_antisymm (measure_mono (subset_univ _)) ?_
    have hcov : (univ : Set ℝ) = Sᶜ ∪ S := by rw [Set.compl_union_self]
    calc volume (univ : Set ℝ)
        = volume (Sᶜ ∪ S) := by rw [hcov]
      _ ≤ volume Sᶜ + volume S := measure_union_le _ _
      _ = volume Sᶜ := by rw [hnull, add_zero]

/-! ## The aligned case: countable ⇒ small in both senses -/

/-- **Every countable subset of `ℝ` is both meagre and Lebesgue-null.** Topologically,
a countable set is a countable union of singletons, each nowhere dense because `ℝ` is a
perfect `T1` space (`countable_isMeagre`); measure-theoretically it is null because
`volume` is atomless. Hence cardinality-smallness implies *both* of the other two notions —
so any set separating them must be uncountable. -/
theorem countable_isMeagre_and_null {s : Set ℝ} (hs : s.Countable) :
    IsMeagre s ∧ volume s = 0 :=
  ⟨countable_isMeagre hs, hs.measure_zero volume⟩

/-! ## The cardinality axis: the separating examples are uncountable -/

/-- **Category-small ⇏ cardinality-small.** There is a meagre subset of `ℝ` that is
uncountable: the complement of the Liouville numbers. It is meagre (its complement, the
Liouville set, is comeagre) yet has full Lebesgue measure, and a countable set would be
null — so it cannot be countable. -/
theorem exists_meagre_uncountable :
    ∃ A : Set ℝ, IsMeagre A ∧ ¬ A.Countable := by
  obtain ⟨hmeagre, hfull⟩ :=
    meagre_conull_compl_of_residual_null liouville_residual liouville_null
  refine ⟨𝓛ᶜ, hmeagre, fun hc => ?_⟩
  have hz : volume (𝓛ᶜ) = 0 := hc.measure_zero volume
  rw [hfull, Real.volume_univ] at hz
  exact ENNReal.top_ne_zero hz

/-- **Measure-small ⇏ cardinality-small.** There is a Lebesgue-null subset of `ℝ` that is
uncountable: the Liouville numbers. They are null (Mathlib, via oq-02) yet uncountable —
were they countable they would be meagre (`countable_isMeagre`), contradicting their
comeagreness (`not_isMeagre_of_mem_residual`). -/
theorem exists_null_uncountable :
    ∃ B : Set ℝ, volume B = 0 ∧ ¬ B.Countable :=
  ⟨𝓛, liouville_null, fun hc =>
    not_isMeagre_of_mem_residual liouville_residual (countable_isMeagre hc)⟩

/-! ## OQ-03 resolution -/

/-- **OQ-03 resolution: the cardinality axis.** Cardinality-smallness (countability) is
independent of both measure-smallness and category-smallness on `ℝ`:

1. every countable set is both meagre and null (`countable_isMeagre_and_null`), but
2. a meagre set can be uncountable (category-small ⇏ countable), and
3. a null set can be uncountable (measure-small ⇏ countable).

Combined with oq-02's measure ⊥ category, this completes the pairwise independence of all
three notions of smallness. The witnesses are the complementary pair `(𝓛ᶜ, 𝓛)`. -/
theorem oq03_resolution :
    (∀ s : Set ℝ, s.Countable → IsMeagre s ∧ volume s = 0) ∧
    (∃ A : Set ℝ, IsMeagre A ∧ ¬ A.Countable) ∧
    (∃ B : Set ℝ, volume B = 0 ∧ ¬ B.Countable) :=
  ⟨fun _ hs => countable_isMeagre_and_null hs, exists_meagre_uncountable, exists_null_uncountable⟩

#check @meagre_conull_compl_of_residual_null
#check @countable_isMeagre_and_null
#check @exists_meagre_uncountable
#check @exists_null_uncountable
#check @oq03_resolution

end AlgebraicRealsMeagerOQ03
