import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Disjoint two-factors on four points

On a four-point shore, a two-element fiber disjoint from another
two-element fiber is its exact complement.  This makes the hole factor rigid
on the triangle-bearing `4 × 4` block of the mixed `C8 + C8` sector.
-/

namespace Erdos85

theorem twoFibers_eq_compl_on_card_four
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H K : Y → Prop) [DecidablePred H] [DecidablePred K]
    (hcard : Fintype.card Y = 4)
    (hH : ((Finset.univ : Finset Y).filter H).card = 2)
    (hK : ((Finset.univ : Finset Y).filter K).card = 2)
    (hdisj : ∀ y, H y → ¬ K y) (y : Y) :
    K y ↔ ¬ H y := by
  let HF := (Finset.univ : Finset Y).filter H
  let KF := (Finset.univ : Finset Y).filter K
  let HC := (Finset.univ : Finset Y).filter fun z => ¬ H z
  have hsub : KF ⊆ HC := by
    intro z hz
    have hzK : K z := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, fun hzH => hdisj z hzH hzK⟩
  have hHC : HC.card = 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Y)) (p := H)
    simp only [Finset.card_univ, hcard] at hpartition
    change HF.card + HC.card = 4 at hpartition
    rw [hH] at hpartition
    omega
  have hKF : KF.card = 2 := by simpa [KF] using hK
  have heq : KF = HC := Finset.eq_of_subset_of_card_le hsub (by omega)
  constructor
  · intro hyK
    have : y ∈ KF := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyK⟩
    rw [heq] at this
    exact (Finset.mem_filter.mp this).2
  · intro hyH
    have : y ∈ HC := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyH⟩
    rw [← heq] at this
    exact (Finset.mem_filter.mp this).2

/-- Relation form: rowwise two-regular disjoint relations on a four-element
right shore are complementary. -/
theorem relation_eq_compl_of_disjoint_twoRegular_on_right_card_four
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcard : Fintype.card Y = 4)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) (x : X) (y : Y) :
    K x y ↔ ¬ H x y := by
  exact twoFibers_eq_compl_on_card_four (H x) (K x) hcard
    (hH.1 x) (hK.1 x) (hdisj x) y

end Erdos85

#print axioms Erdos85.relation_eq_compl_of_disjoint_twoRegular_on_right_card_four
