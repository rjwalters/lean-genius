import Proofs.Erdos85SevenRegularNearTwinLite

/-! # No-rainbow saturation for a codegree-five core -/

namespace Erdos85

noncomputable section

/-- Five-core analogue of the near-twin count: after charging the base owner
at most once at each endpoint, at least three closures repeat a non-base
owner on their two side edges. -/
theorem card_filter_eq_ne_base_ge_three_of_five_noRainbow
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (hcard : S.card = 5)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base) :
    (S.filter fun r => left r = right r ∧ left r ≠ base).card ≥ 3 := by
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
  change S.card = 5 at hcard
  change E.card ≥ 3
  omega

/-- With exactly three available non-base colors, a five-core either already
forces a repeated-owner fork, or it lies on the sharp three-repetition
boundary. -/
theorem fiveCore_repeated_color_or_exact_three
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (hpalette : palette.card = 3)
    (hcard : S.card = 5)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base)
    (hmem : ∀ r ∈ S, left r = right r → left r ≠ base →
      left r ∈ palette) :
    (∃ c r₁ r₂, c ≠ base ∧ r₁ ≠ r₂ ∧ r₁ ∈ S ∧ r₂ ∈ S ∧
      left r₁ = c ∧ right r₁ = c ∧
      left r₂ = c ∧ right r₂ = c) ∨
      (S.filter fun r => left r = right r ∧ left r ≠ base).card = 3 := by
  let E := S.filter fun r => left r = right r ∧ left r ≠ base
  have hE : E.card ≥ 3 :=
    card_filter_eq_ne_base_ge_three_of_five_noRainbow
      S left right base hcard hleft hright hno
  by_cases heq : E.card = 3
  · exact Or.inr heq
  have hlt : palette.card < E.card := by omega
  have hmaps : Set.MapsTo left E palette := by
    intro r hr
    have hrdata := Finset.mem_filter.mp hr
    exact hmem r hrdata.1 hrdata.2.1 hrdata.2.2
  obtain ⟨r₁, hr₁, r₂, hr₂, hrne, hcolor⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hr₁data := Finset.mem_filter.mp hr₁
  have hr₂data := Finset.mem_filter.mp hr₂
  left
  refine ⟨left r₁, r₁, r₂, hr₁data.2.2, hrne,
    hr₁data.1, hr₂data.1, rfl, ?_, hcolor.symm, ?_⟩
  · exact hr₁data.2.1.symm
  · exact hr₂data.2.1.symm.trans hcolor.symm

/-- Fully rigid sharp boundary: if there is no repeated-color fork, the
three non-base repetitions use the three non-base colors bijectively. -/
theorem fiveCore_repeated_color_or_bijective_boundary
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (hpalette : palette.card = 3)
    (hcard : S.card = 5)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base)
    (hmem : ∀ r ∈ S, left r = right r → left r ≠ base →
      left r ∈ palette) :
    (∃ c r₁ r₂, c ≠ base ∧ r₁ ≠ r₂ ∧ r₁ ∈ S ∧ r₂ ∈ S ∧
      left r₁ = c ∧ right r₁ = c ∧
      left r₂ = c ∧ right r₂ = c) ∨
      let E := S.filter fun r => left r = right r ∧ left r ≠ base
      E.card = 3 ∧
        (∀ r₁ ∈ E, ∀ r₂ ∈ E, left r₁ = left r₂ → r₁ = r₂) ∧
        E.image left = palette := by
  classical
  let E := S.filter fun r => left r = right r ∧ left r ≠ base
  let Fork : Prop := ∃ c r₁ r₂, c ≠ base ∧ r₁ ≠ r₂ ∧
    r₁ ∈ S ∧ r₂ ∈ S ∧ left r₁ = c ∧ right r₁ = c ∧
      left r₂ = c ∧ right r₂ = c
  by_cases hfork : Fork
  · exact Or.inl hfork
  right
  have hE : E.card = 3 := by
    rcases fiveCore_repeated_color_or_exact_three
      S left right base palette hpalette hcard hleft hright hno hmem with hf | he
    · exact (hfork hf).elim
    · exact he
  have hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      left r₁ = left r₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ hc
    by_contra hrne
    have hr₁data := Finset.mem_filter.mp hr₁
    have hr₂data := Finset.mem_filter.mp hr₂
    apply hfork
    exact ⟨left r₁, r₁, r₂, hr₁data.2.2, hrne,
      hr₁data.1, hr₂data.1, rfl, hr₁data.2.1.symm,
      hc.symm, hr₂data.2.1.symm.trans hc.symm⟩
  have himageSub : E.image left ⊆ palette := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hc
    have hrdata := Finset.mem_filter.mp hr
    exact hmem r hrdata.1 hrdata.2.1 hrdata.2.2
  have himageCard : (E.image left).card = 3 := by
    rw [Finset.card_image_iff.mpr]
    · exact hE
    · exact fun r₁ hr₁ r₂ hr₂ hc => hinj r₁ hr₁ r₂ hr₂ hc
  refine ⟨hE, hinj, Finset.eq_of_subset_of_card_le himageSub ?_⟩
  rw [himageCard, hpalette]

end

end Erdos85
