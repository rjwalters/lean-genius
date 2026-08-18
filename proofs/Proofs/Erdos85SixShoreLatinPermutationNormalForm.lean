import Proofs.Erdos85SixShoreThreeFactorMatchingCoordinates

/-! # Latin permutation normal form on a six-point shore -/

namespace Erdos85

noncomputable section

/-- Normalize the first of the six matching coordinates to the identity.
The resulting six permutations act regularly pointwise: for each `x`, their
values at `x` enumerate the whole six-element shore. -/
theorem disjoint_twoRegular_relations_on_six_exists_latinPermutation_normalForm
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 6) (hcardY : Fintype.card Y = 6)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    ∃ f : X ≃ Y, ∃ P : Fin 6 → Equiv.Perm X,
      P 0 = 1 ∧
      (∀ x y, H x y ↔ f.symm y = P 0 x ∨ f.symm y = P 1 x) ∧
      (∀ x y, K x y ↔ f.symm y = P 2 x ∨ f.symm y = P 3 x) ∧
      (∀ x y, (¬ H x y ∧ ¬ K x y) ↔
        f.symm y = P 4 x ∨ f.symm y = P 5 x) ∧
      (∀ x, Function.Bijective (fun i => P i x)) ∧
      (∀ i j, i ≠ j → ∀ x, P i x ≠ P j x) := by
  obtain ⟨F, hHcoord, hKcoord, hLcoord, hFbij⟩ :=
    disjoint_twoRegular_relations_on_six_exists_sixMatching_coordinates
      H K hcardX hcardY hH hK hdisj
  let f : X ≃ Y := F 0
  let P : Fin 6 → Equiv.Perm X := fun i => (F i).trans f.symm
  refine ⟨f, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext x
    simp [P, f]
  · intro x y
    rw [hHcoord]
    simp only [P, Equiv.trans_apply]
    constructor
    · rintro (rfl | rfl) <;> simp [f]
    · rintro (hy | hy)
      · left
        exact f.symm.injective hy
      · right
        exact f.symm.injective hy
  · intro x y
    rw [hKcoord]
    simp only [P, Equiv.trans_apply]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (hy | hy)
      · left; exact f.symm.injective hy
      · right; exact f.symm.injective hy
  · intro x y
    rw [hLcoord]
    simp only [P, Equiv.trans_apply]
    constructor
    · rintro (rfl | rfl) <;> simp
    · rintro (hy | hy)
      · left; exact f.symm.injective hy
      · right; exact f.symm.injective hy
  · intro x
    have hbij := hFbij x
    constructor
    · intro i j hij
      apply hbij.1
      apply f.symm.injective
      simpa [P] using hij
    · intro y
      obtain ⟨i, hi⟩ := hbij.2 (f y)
      refine ⟨i, ?_⟩
      simpa [P] using congrArg f.symm hi
  · intro i j hij x heq
    exact hij ((hFbij x).1 (by
      apply f.symm.injective
      simpa [P] using heq))

end

end Erdos85

#print axioms Erdos85.disjoint_twoRegular_relations_on_six_exists_latinPermutation_normalForm
