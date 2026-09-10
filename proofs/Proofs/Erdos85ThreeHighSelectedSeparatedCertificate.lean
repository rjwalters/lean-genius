import Proofs.Erdos85ThreeHighSeparatedJointSearch

namespace Erdos85

/-- A finite check that supplied lists include every initially eligible block-capped triple. -/
def threeHighInitialTripleCoverChecked (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) : Bool :=
  (List.finRange 3).all fun k => (threeHighCanonicalTripleShapes k).all fun S =>
    !threeHighTripleNoCommonNeighbor B S || decide (S ∈ D k)

/-- A selected separated set after one support pass is a small rejection certificate. -/
theorem threeHighSelectedSeparatedCertificate_no_joint
    (B : Fin 24 → Fin 24 → Bool) (D : Fin 3 → List (Finset (Fin 24)))
    (hD : threeHighInitialTripleCoverChecked B D = true)
    (k : Fin 3) (X : Finset (Fin 24)) (hX : X ⊆ threeHighCanonicalResidual k)
    (hsize : 6 < X.card)
    (hsep : listedSeparatedCap (threeHighTripleSupportPass B D k) X = true) :
    ¬ ThreeHighJointWitness B := by
  rintro ⟨F,hF,hblocks,hcompat,hcap⟩
  have hmem : ∀ i S, S ∈ F i → S ∈ D i := by
    intro i S hS
    have hi : S ∈ (threeHighCanonicalTripleShapes i).filter
        (threeHighTripleNoCommonNeighbor B) := by
      rw [threeHighCanonicalTripleShapes_filter]
      apply List.mem_filter.mpr
      refine ⟨?_, hblocks i S hS⟩
      rw [threeHighDirectTripleList_eq]
      exact (mem_threeHighEligibleTripleList B _ S).mpr
        (((mem_threeHighResolutionDomain B _ (F i)).mp (hF i)).1 hS)
    have hc := List.all_eq_true.mp
      (List.all_eq_true.mp hD i (List.mem_finRange i)) S (List.mem_filter.mp hi).1
    simpa only [(List.mem_filter.mp hi).2, Bool.not_true, Bool.false_or,
      decide_eq_true_eq] using hc
  have hpass := threeHighTripleSupportPass_preserves B D F hmem
    (fun i j _ => hcompat i j)
  have hr := (mem_threeHighResolutionDomain B _ (F k)).mp (hF k)
  have hb := card_le_covering_family_of_inter_card_le_one X (F k)
    (by simpa only [hr.2.2.2] using hX)
    (fun S hS => of_decide_eq_true (List.all_eq_true.mp hsep S (hpass k S hS)))
  rw [hr.2.1] at hb
  exact (Nat.not_lt_of_ge hb) hsize

end Erdos85
#print axioms Erdos85.threeHighSelectedSeparatedCertificate_no_joint
