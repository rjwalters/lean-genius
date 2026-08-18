import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Disjoint two-factors on five points

On a five-point shore, the complement of two disjoint two-element fibers is
a singleton.  Thus the free hole factor in the triangle-bearing `5 × 5`
block is the complement of a perfect matching inside `K₅,₅ \ H`.
-/

namespace Erdos85

def RelationOneRegular {X Y : Type*} [Fintype X] [Fintype Y]
    (R : X → Y → Prop) [DecidableRel R] : Prop :=
  (∀ x, ((Finset.univ : Finset Y).filter fun y => R x y).card = 1) ∧
  (∀ y, ((Finset.univ : Finset X).filter fun x => R x y).card = 1)

theorem complement_of_disjoint_twoFibers_card_one
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H K : Y → Prop) [DecidablePred H] [DecidablePred K]
    (hcard : Fintype.card Y = 5)
    (hH : ((Finset.univ : Finset Y).filter H).card = 2)
    (hK : ((Finset.univ : Finset Y).filter K).card = 2)
    (hdisj : ∀ y, H y → ¬ K y) :
    ((Finset.univ : Finset Y).filter fun y => ¬ H y ∧ ¬ K y).card = 1 := by
  let HF := (Finset.univ : Finset Y).filter H
  let KF := (Finset.univ : Finset Y).filter K
  let M := (Finset.univ : Finset Y).filter fun y => ¬ H y ∧ ¬ K y
  have hd : Disjoint HF KF := by
    rw [Finset.disjoint_left]
    intro y hyH hyK
    exact hdisj y (Finset.mem_filter.mp hyH).2
      (Finset.mem_filter.mp hyK).2
  have hunion : (HF ∪ KF).card = 4 := by
    rw [Finset.card_union_of_disjoint hd]
    simpa [HF, KF, hH, hK]
  have hM : M = (Finset.univ : Finset Y) \ (HF ∪ KF) := by
    ext y
    simp [M, HF, KF, and_left_comm, and_comm]
  change M.card = 1
  rw [hM, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    Finset.card_univ, hcard, hunion]

/-- Relation form: the entries unused by two disjoint two-regular relations
on five-element shores form a one-regular relation, i.e. a perfect matching. -/
theorem complement_of_disjoint_twoRegular_relations_is_oneRegular
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 5) (hcardY : Fintype.card Y = 5)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    RelationOneRegular (fun x y => ¬ H x y ∧ ¬ K x y) := by
  constructor
  · intro x
    exact complement_of_disjoint_twoFibers_card_one (H x) (K x)
      hcardY (hH.1 x) (hK.1 x) (hdisj x)
  · intro y
    exact complement_of_disjoint_twoFibers_card_one
      (fun x => H x y) (fun x => K x y)
      hcardX (hH.2 y) (hK.2 y) (fun x => hdisj x y)

end Erdos85

#print axioms Erdos85.complement_of_disjoint_twoRegular_relations_is_oneRegular
