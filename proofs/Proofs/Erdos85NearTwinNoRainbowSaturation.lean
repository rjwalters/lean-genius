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

end

end Erdos85
