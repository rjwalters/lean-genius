import Proofs.Erdos85NearTwinLiteNoRainbowSaturation

/-! # Rigidity of the codegree-five exact-three boundary -/

namespace Erdos85

noncomputable section

/-- On the sharp boundary of the five-core no-rainbow count, the three
equal-nonbase closures and the two base-charged closures form a disjoint
`3+1+1` partition.  In particular one remaining closure uses the base on the
left, the other uses it on the right, and no closure uses it on both sides. -/
theorem fiveCore_exactThree_forces_disjoint_three_one_one
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S : Finset R) (left right : R → C) (base : C)
    (hcard : S.card = 5)
    (hleft : (S.filter fun r => left r = base).card ≤ 1)
    (hright : (S.filter fun r => right r = base).card ≤ 1)
    (hno : ∀ r ∈ S,
      left r = right r ∨ left r = base ∨ right r = base)
    (hexact : (S.filter fun r =>
      left r = right r ∧ left r ≠ base).card = 3) :
    let E := S.filter fun r => left r = right r ∧ left r ≠ base
    let L := S.filter fun r => left r = base
    let T := S.filter fun r => right r = base
    E.card = 3 ∧ L.card = 1 ∧ T.card = 1 ∧
      Disjoint E L ∧ Disjoint E T ∧ Disjoint L T ∧
      S = E ∪ (L ∪ T) := by
  classical
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
  have hback : E ∪ (L ∪ T) ⊆ S := by
    intro r hr
    simp only [Finset.mem_union] at hr
    rcases hr with hr | hr | hr
    · exact (Finset.mem_filter.mp hr).1
    · exact (Finset.mem_filter.mp hr).1
    · exact (Finset.mem_filter.mp hr).1
  have hpartition : S = E ∪ (L ∪ T) :=
    Finset.Subset.antisymm hsub hback
  have hLcard : L.card = 1 := by
    have htotal := Finset.card_le_card hsub
    have houter := Finset.card_union_le E (L ∪ T)
    have hinner := Finset.card_union_le L T
    change L.card ≤ 1 at hleft
    change T.card ≤ 1 at hright
    change E.card = 3 at hexact
    change S.card = 5 at hcard
    omega
  have hTcard : T.card = 1 := by
    have htotal := Finset.card_le_card hsub
    have houter := Finset.card_union_le E (L ∪ T)
    have hinner := Finset.card_union_le L T
    change L.card ≤ 1 at hleft
    change T.card ≤ 1 at hright
    change E.card = 3 at hexact
    change S.card = 5 at hcard
    omega
  have hEL : Disjoint E L := by
    apply Finset.disjoint_left.mpr
    intro r hrE hrL
    have he := (Finset.mem_filter.mp hrE).2
    have hl := (Finset.mem_filter.mp hrL).2
    exact he.2 hl
  have hET : Disjoint E T := by
    apply Finset.disjoint_left.mpr
    intro r hrE hrT
    have he := (Finset.mem_filter.mp hrE).2
    have ht := (Finset.mem_filter.mp hrT).2
    exact he.2 (he.1.trans ht)
  have hErest : Disjoint E (L ∪ T) :=
    Finset.disjoint_union_right.mpr ⟨hEL, hET⟩
  have hLTcard : (L ∪ T).card = 2 := by
    have hsum := Finset.card_union_of_disjoint hErest
    rw [← hpartition, hcard, hexact] at hsum
    omega
  have hLT : Disjoint L T := by
    apply Finset.disjoint_left.mpr
    intro r hrL hrT
    have hinterPos : 0 < (L ∩ T).card :=
      Finset.card_pos.mpr ⟨r, Finset.mem_inter.mpr ⟨hrL, hrT⟩⟩
    have hsum := Finset.card_union_add_card_inter L T
    omega
  exact ⟨hexact, hLcard, hTcard, hEL, hET, hLT, hpartition⟩

end

end Erdos85
