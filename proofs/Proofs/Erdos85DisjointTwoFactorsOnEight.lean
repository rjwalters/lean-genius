import Proofs.Erdos85MuThreeMixedGridCode

/-! # The four-regular complement of two factors on eight points -/

namespace Erdos85

def RelationFourRegular {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [DecidableRel R] : Prop :=
  (∀ x, ((Finset.univ : Finset Y).filter fun y => R x y).card = 4) ∧
  (∀ y, ((Finset.univ : Finset X).filter fun x => R x y).card = 4)

theorem complement_of_disjoint_twoFibers_card_four
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H K : Y → Prop) [DecidablePred H] [DecidablePred K]
    (hcard : Fintype.card Y = 8)
    (hH : ((Finset.univ : Finset Y).filter H).card = 2)
    (hK : ((Finset.univ : Finset Y).filter K).card = 2)
    (hdisj : ∀ y, H y → ¬ K y) :
    ((Finset.univ : Finset Y).filter fun y => ¬ H y ∧ ¬ K y).card = 4 := by
  let HF := (Finset.univ : Finset Y).filter H
  let KF := (Finset.univ : Finset Y).filter K
  let L := (Finset.univ : Finset Y).filter fun y => ¬ H y ∧ ¬ K y
  have hd : Disjoint HF KF := by
    rw [Finset.disjoint_left]
    intro y hyH hyK
    exact hdisj y (Finset.mem_filter.mp hyH).2
      (Finset.mem_filter.mp hyK).2
  have hunion : (HF ∪ KF).card = 4 := by
    rw [Finset.card_union_of_disjoint hd]
    simpa [HF, KF, hH, hK]
  have hL : L = (Finset.univ : Finset Y) \ (HF ∪ KF) := by
    ext y
    simp [L, HF, KF]
  change L.card = 4
  rw [hL, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    Finset.card_univ, hcard, hunion]

/-- On eight-element shores, the entries outside two disjoint two-factors
form a four-regular bipartite relation. -/
theorem complement_of_disjoint_twoRegular_relations_is_fourRegular
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 8) (hcardY : Fintype.card Y = 8)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    RelationFourRegular (fun x y => ¬ H x y ∧ ¬ K x y) := by
  constructor
  · intro x
    exact complement_of_disjoint_twoFibers_card_four (H x) (K x)
      hcardY (hH.1 x) (hK.1 x) (hdisj x)
  · intro y
    exact complement_of_disjoint_twoFibers_card_four
      (fun x => H x y) (fun x => K x y)
      hcardX (hH.2 y) (hK.2 y) (fun x => hdisj x y)

end Erdos85

#print axioms Erdos85.complement_of_disjoint_twoRegular_relations_is_fourRegular
