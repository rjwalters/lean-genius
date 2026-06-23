import Mathlib

/-!
# The Baire category theorem and its consequences

**Baire's category theorem** (Baire 1899) is the backbone of functional analysis and
descriptive set theory: a complete (pseudo)metric space — or more generally any
`BaireSpace` — cannot be "small" in a topological sense. Mathlib packages the abstract
theorem through several named lemmas, which this file re-exports (hence the `mathlib`
badge):

* `dense_iInter_of_isOpen` — the **dense-Gδ form**: a countable intersection of dense
  open sets is dense;
* `nonempty_interior_of_iUnion_of_closed` — the **category form**: if countably many
  closed sets cover a nonempty space, one of them has nonempty interior;
* `not_isMeagre_of_isOpen` — every nonempty open set is non-meagre;
* `BaireSpace.of_completelyPseudoMetrizable` — the **instance**: every complete
  metrizable space (in particular `ℝ`) is a `BaireSpace`.

On top of these we record the genuine content absent from the gallery: the
**contrapositive category form** (a nonempty Baire space is *not* a countable union of
closed sets all with empty interior, `baire_not_iUnion_empty_interior`), the fact that
the whole space is non-meagre (`baire_univ_not_meagre`), and — as the concrete witness —
the classical **uncountability of `ℝ`** derived from Baire:

* every singleton in `ℝ` is meagre (`isMeagre_singleton_real`), hence every countable
  subset is meagre (`isMeagre_of_countable_real`);
* since the whole space is non-meagre, `ℝ` is uncountable (`real_uncountable`); concretely
  `ℝ` is never the union of countably many singletons (`real_not_iUnion_singletons`).

All results are fully machine-checked with no `sorry` and no extra axioms (no
`native_decide`).
-/

namespace BaireCategoryTheoremOQ01

open Set Topology

/-! ## Part (a): the abstract Baire category theorem -/

/-- **Baire category theorem, dense-Gδ form.** In any `BaireSpace`, a countable
intersection of dense open sets is dense. (Re-export of `dense_iInter_of_isOpen`.) -/
theorem baire_dense_iInter {X : Type*} [TopologicalSpace X] [BaireSpace X]
    {ι : Type*} [Countable ι] {f : ι → Set X}
    (ho : ∀ i, IsOpen (f i)) (hd : ∀ i, Dense (f i)) : Dense (⋂ i, f i) :=
  dense_iInter_of_isOpen ho hd

/-- **Baire category theorem, category form.** If a countable family of closed sets covers
a nonempty Baire space, then at least one of them has nonempty interior. (Re-export of
`nonempty_interior_of_iUnion_of_closed`.) -/
theorem baire_nonempty_interior {X : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] {f : ι → Set X}
    (hc : ∀ i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : ∃ i, (interior (f i)).Nonempty :=
  nonempty_interior_of_iUnion_of_closed hc hU

/-- **Contrapositive category form.** A nonempty Baire space is *not* the union of a
countable family of closed sets all having empty interior. This is the precise sense in
which a complete metric space "is not meagre in itself": it cannot be exhausted by
countably many nowhere-dense closed pieces. -/
theorem baire_not_iUnion_empty_interior {X : Type*} [TopologicalSpace X] [BaireSpace X]
    [Nonempty X] {ι : Type*} [Countable ι] {f : ι → Set X}
    (hc : ∀ i, IsClosed (f i)) (he : ∀ i, interior (f i) = ∅) : ⋃ i, f i ≠ univ := by
  intro hU
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  rw [he i] at hi
  exact not_nonempty_empty hi

/-- **Meagre form.** In a nonempty Baire space the whole space is non-meagre: it is not a
countable union of nowhere-dense sets. -/
theorem baire_univ_not_meagre {X : Type*} [TopologicalSpace X] [BaireSpace X] [Nonempty X] :
    ¬ IsMeagre (univ : Set X) :=
  not_isMeagre_of_isOpen isOpen_univ univ_nonempty

/-! ## Part (b): the Baire space instance -/

/-- Every complete metrizable space is a Baire space; in particular `ℝ` is a `BaireSpace`,
resolved automatically from `BaireSpace.of_completelyPseudoMetrizable`. -/
theorem baireSpace_real : BaireSpace ℝ := inferInstance

/-! ## Part (c): concrete consequence — `ℝ` is uncountable

The classical application of Baire's theorem: a nonempty complete metric space with no
isolated points is uncountable. We carry this out for `ℝ`, whose points are non-isolated
(`interior {x} = ∅`), so every countable subset is meagre while the whole line is not. -/

/-- A singleton in `ℝ` is meagre: it is closed with empty interior, hence nowhere dense. -/
theorem isMeagre_singleton_real (x : ℝ) : IsMeagre ({x} : Set ℝ) := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨{({x} : Set ℝ)}, ?_, countable_singleton _, ?_⟩
  · intro t ht
    rw [mem_singleton_iff] at ht; subst ht
    rw [(isClosed_singleton).isNowhereDense_iff]
    exact interior_singleton x
  · simp

/-- Every countable subset of `ℝ` is meagre: write it as a countable union of singletons,
each nowhere dense. -/
theorem isMeagre_of_countable_real {s : Set ℝ} (hs : s.Countable) : IsMeagre s := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨(fun x => ({x} : Set ℝ)) '' s, ?_, hs.image _, ?_⟩
  · rintro t ⟨x, _, rfl⟩
    rw [(isClosed_singleton).isNowhereDense_iff]
    exact interior_singleton x
  · intro x hx
    exact mem_sUnion.2 ⟨{x}, ⟨x, hx, rfl⟩, rfl⟩

/-- **Uncountability of `ℝ` via Baire.** If `ℝ` were countable it would be meagre in
itself, contradicting that a nonempty Baire space is non-meagre. -/
theorem real_uncountable : ¬ (univ : Set ℝ).Countable := by
  intro h
  exact baire_univ_not_meagre (isMeagre_of_countable_real h)

/-- A concrete restatement of uncountability through the category form: `ℝ` is never the
union of countably many singletons. (Each `{g n}` is closed with empty interior.) -/
theorem real_not_iUnion_singletons (g : ℕ → ℝ) : ⋃ n, ({g n} : Set ℝ) ≠ univ :=
  baire_not_iUnion_empty_interior (fun _ => isClosed_singleton)
    (fun n => interior_singleton (g n))

end BaireCategoryTheoremOQ01
