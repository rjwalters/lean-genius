import Proofs.Erdos85DisjointTwoFactorsOnFive

/-!
# Disjoint two-factors on six points

On a six-point shore, the entries unused by two disjoint two-element fibers
again form a two-element fiber.  Hence two disjoint bipartite two-factors on
six-by-six shores canonically extend to a partition into three two-factors.
-/

namespace Erdos85

theorem complement_of_disjoint_twoFibers_card_two
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H K : Y → Prop) [DecidablePred H] [DecidablePred K]
    (hcard : Fintype.card Y = 6)
    (hH : ((Finset.univ : Finset Y).filter H).card = 2)
    (hK : ((Finset.univ : Finset Y).filter K).card = 2)
    (hdisj : ∀ y, H y → ¬ K y) :
    ((Finset.univ : Finset Y).filter fun y => ¬ H y ∧ ¬ K y).card = 2 := by
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
    simp [L, HF, KF, and_left_comm, and_comm]
  change L.card = 2
  rw [hL, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
    Finset.card_univ, hcard, hunion]

/-- On six-element shores, the complement of two disjoint two-regular
relations is itself two-regular. -/
theorem complement_of_disjoint_twoRegular_relations_is_twoRegular
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 6) (hcardY : Fintype.card Y = 6)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    RelationTwoRegular (fun x y => ¬ H x y ∧ ¬ K x y) := by
  constructor
  · intro x
    exact complement_of_disjoint_twoFibers_card_two (H x) (K x)
      hcardY (hH.1 x) (hK.1 x) (hdisj x)
  · intro y
    exact complement_of_disjoint_twoFibers_card_two
      (fun x => H x y) (fun x => K x y)
      hcardX (hH.2 y) (hK.2 y) (fun x => hdisj x y)

/-- The three relations `H`, `K`, and their common complement partition every
entry of the six-by-six bipartite grid, and all three are two-regular. -/
theorem disjoint_twoRegular_relations_on_six_extend_to_threeFactor_partition
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 6) (hcardY : Fintype.card Y = 6)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    let L := fun x y => ¬ H x y ∧ ¬ K x y
    RelationTwoRegular L ∧
      (∀ x y, H x y ∨ K x y ∨ L x y) ∧
      (∀ x y, H x y → ¬ K x y ∧ ¬ L x y) ∧
      (∀ x y, K x y → ¬ L x y) := by
  dsimp only
  refine ⟨complement_of_disjoint_twoRegular_relations_is_twoRegular
    H K hcardX hcardY hH hK hdisj, ?_, ?_, ?_⟩
  · intro x y
    by_cases hHx : H x y
    · exact Or.inl hHx
    by_cases hKx : K x y
    · exact Or.inr (Or.inl hKx)
    · exact Or.inr (Or.inr ⟨hHx, hKx⟩)
  · intro x y hHx
    exact ⟨hdisj x y hHx, fun hL => hL.1 hHx⟩
  · intro x y hKx hL
    exact hL.2 hKx

end Erdos85

#print axioms Erdos85.complement_of_disjoint_twoRegular_relations_is_twoRegular
#print axioms Erdos85.disjoint_twoRegular_relations_on_six_extend_to_threeFactor_partition
