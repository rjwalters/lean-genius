import Proofs.Erdos85DisjointTwoFactorsOnSix
import Proofs.Erdos85DisjointTwoFactorsMatchingNormalForm

/-! # Six matching coordinates for a six-shore three-factorization -/

namespace Erdos85

noncomputable section

/-- The three two-factors which partition a six-by-six relation can be
coordinatized by six perfect matchings.  At each left vertex, evaluating the
six matchings enumerates the entire right shore bijectively. -/
theorem disjoint_twoRegular_relations_on_six_exists_sixMatching_coordinates
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcardX : Fintype.card X = 6) (hcardY : Fintype.card Y = 6)
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (hdisj : ∀ x y, H x y → ¬ K x y) :
    ∃ F : Fin 6 → (X ≃ Y),
      (∀ x y, H x y ↔ y = F 0 x ∨ y = F 1 x) ∧
      (∀ x y, K x y ↔ y = F 2 x ∨ y = F 3 x) ∧
      (∀ x y, (¬ H x y ∧ ¬ K x y) ↔
        y = F 4 x ∨ y = F 5 x) ∧
      (∀ x, Function.Bijective (fun i => F i x)) := by
  let L : X → Y → Prop := fun x y => ¬ H x y ∧ ¬ K x y
  letI : DecidableRel L := fun x y => inferInstanceAs (Decidable (¬ H x y ∧ ¬ K x y))
  have hL : RelationTwoRegular L :=
    complement_of_disjoint_twoRegular_relations_is_twoRegular
      H K hcardX hcardY hH hK hdisj
  obtain ⟨fH, pH⟩ := twoRegularBipartite_exists_afterMatching H hH.1 hH.2
  obtain ⟨fK, pK⟩ := twoRegularBipartite_exists_afterMatching K hK.1 hK.2
  obtain ⟨fL, pL⟩ := twoRegularBipartite_exists_afterMatching L hL.1 hL.2
  let gH : X ≃ Y := pH.residualEquiv
  let gK : X ≃ Y := pK.residualEquiv
  let gL : X ≃ Y := pL.residualEquiv
  let F : Fin 6 → (X ≃ Y) := ![fH, gH, fK, gK, fL, gL]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro x y
    simpa [F, gH] using pH.rel_iff_matching_or_residual x y
  · intro x y
    simpa [F, gK] using pK.rel_iff_matching_or_residual x y
  · intro x y
    simpa [F, gL, L] using pL.rel_iff_matching_or_residual x y
  · intro x
    apply (Fintype.bijective_iff_surjective_and_card (fun i => F i x)).2
    constructor
    · intro y
      by_cases hyH : H x y
      · rcases (pH.rel_iff_matching_or_residual x y).1 hyH with hy | hy
        · exact ⟨0, by simpa [F] using hy.symm⟩
        · exact ⟨1, by simpa [F, gH] using hy.symm⟩
      by_cases hyK : K x y
      · rcases (pK.rel_iff_matching_or_residual x y).1 hyK with hy | hy
        · exact ⟨2, by simpa [F] using hy.symm⟩
        · exact ⟨3, by simpa [F, gK] using hy.symm⟩
      · have hyL : L x y := ⟨hyH, hyK⟩
        rcases (pL.rel_iff_matching_or_residual x y).1 hyL with hy | hy
        · exact ⟨4, by simpa [F] using hy.symm⟩
        · exact ⟨5, by simpa [F, gL] using hy.symm⟩
    · simpa [hcardY]

end

end Erdos85

#print axioms Erdos85.disjoint_twoRegular_relations_on_six_exists_sixMatching_coordinates
