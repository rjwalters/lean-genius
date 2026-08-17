import Proofs.Erdos85SevenRegularNearTwinNeighborhoods

/-! # No-rainbow saturation around a near-twin edge

The complement-common six-core of a defect near-twin pair produces six
triangles through the pair.  If the pair's owner color can occur at most once
more at either endpoint, absence of a rainbow forces at least four of those
triangles to use the same color on their two remaining edges.
-/

namespace Erdos85

noncomputable section

/-- Abstract six-core counting lemma underlying the near-twin owner-color
argument. -/
theorem card_filter_eq_ge_four_of_six_noRainbow
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (hcard : S.card = 6)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base) :
    (S.filter fun r => left r = right r).card ≥ 4 := by
  let E := S.filter fun r => left r = right r
  let L := S.filter fun r => left r = base
  let T := S.filter fun r => right r = base
  have hsub : S ⊆ E ∪ (L ∪ T) := by
    intro r hr
    have hrCases := hno r hr
    simp only [E, L, T, Finset.mem_union, Finset.mem_filter]
    rcases hrCases with he | hl | ht
    · exact Or.inl ⟨hr, he⟩
    · exact Or.inr (Or.inl ⟨hr, hl⟩)
    · exact Or.inr (Or.inr ⟨hr, ht⟩)
  have htotal := Finset.card_le_card hsub
  have houter := Finset.card_union_le E (L ∪ T)
  have hinner := Finset.card_union_le L T
  change L.card ≤ 1 at hleft
  change T.card ≤ 1 at hright
  change S.card = 6 at hcard
  change E.card ≥ 4
  omega

/-- Equivalent exceptional-set form: at most two of the six triangles can
have unequal side colors. -/
theorem card_filter_ne_le_two_of_six_noRainbow
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (hcard : S.card = 6)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base) :
    (S.filter fun r => left r ≠ right r).card ≤ 2 := by
  have heq := card_filter_eq_ge_four_of_six_noRainbow
    S left right base hcard hleft hright hno
  have hpartition :
      (S.filter fun r => left r = right r).card +
        (S.filter fun r => left r ≠ right r).card = S.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext r
      by_cases h : left r = right r <;> simp [h]
    · rw [Finset.disjoint_left]
      intro r he hn
      exact (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp he).2
  omega

/-- In fact at least four triangles have a repeated color different from the
base-edge color.  A base-colored equality is charged to both of the two
one-element exceptional budgets. -/
theorem card_filter_eq_ne_base_ge_four_of_six_noRainbow
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (hcard : S.card = 6)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base) :
    (S.filter fun r => left r = right r ∧ left r ≠ base).card ≥ 4 := by
  let E := S.filter fun r => left r = right r ∧ left r ≠ base
  let L := S.filter fun r => left r = base
  let T := S.filter fun r => right r = base
  have hsub : S ⊆ E ∪ (L ∪ T) := by
    intro r hr
    have hrCases := hno r hr
    simp only [E, L, T, Finset.mem_union, Finset.mem_filter]
    by_cases hb : left r = base
    · exact Or.inr (Or.inl ⟨hr, hb⟩)
    rcases hrCases with he | hl | ht
    · exact Or.inl ⟨hr, he, hb⟩
    · exact (hb hl).elim
    · exact Or.inr (Or.inr ⟨hr, ht⟩)
  have htotal := Finset.card_le_card hsub
  have houter := Finset.card_union_le E (L ∪ T)
  have hinner := Finset.card_union_le L T
  change L.card ≤ 1 at hleft
  change T.card ≤ 1 at hright
  change S.card = 6 at hcard
  change E.card ≥ 4
  omega

/-- Three-color pigeonhole conclusion: among the four forced non-base
repetitions, two distinct six-core vertices use the same repeated color. -/
theorem exists_two_repeated_same_nonbase_color_of_six_noRainbow
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (hpalette : palette.card = 3)
    (hcard : S.card = 6)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base)
    (hmem : ∀ r ∈ S, left r = right r → left r ≠ base →
      left r ∈ palette) :
    ∃ c r₁ r₂, c ≠ base ∧ r₁ ≠ r₂ ∧ r₁ ∈ S ∧ r₂ ∈ S ∧
      left r₁ = c ∧ right r₁ = c ∧
      left r₂ = c ∧ right r₂ = c := by
  let E := S.filter fun r => left r = right r ∧ left r ≠ base
  have hE : E.card ≥ 4 :=
    card_filter_eq_ne_base_ge_four_of_six_noRainbow
      S left right base hcard hleft hright hno
  have hlt : palette.card < E.card := by omega
  have hmaps : Set.MapsTo left E palette := by
    intro r hr
    have hrdata := Finset.mem_filter.mp hr
    exact hmem r hrdata.1 hrdata.2.1 hrdata.2.2
  obtain ⟨r₁, hr₁, r₂, hr₂, hrne, hcolor⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hr₁data := Finset.mem_filter.mp hr₁
  have hr₂data := Finset.mem_filter.mp hr₂
  refine ⟨left r₁, r₁, r₂, hr₁data.2.2, hrne,
    hr₁data.1, hr₂data.1, rfl, ?_, hcolor.symm, ?_⟩
  · exact hr₁data.2.1.symm
  · exact hr₂data.2.1.symm.trans hcolor.symm

end

end Erdos85
