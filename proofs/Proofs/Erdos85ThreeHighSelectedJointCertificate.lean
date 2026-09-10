import Proofs.Erdos85ThreeHighSelectedSeparatedCertificate

namespace Erdos85

/-- A supplied eligible-triple cover with a false joint search rejects a joint witness. -/
theorem threeHighSelectedJointCertificate_no_joint
    (B : Fin 24 → Fin 24 → Bool) (D : Fin 3 → List (Finset (Fin 24)))
    (hD : threeHighInitialTripleCoverChecked B D = true)
    (hfalse : threeHighListedJointSearch B D threeHighCanonicalResidual = false) :
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
  have htrue := threeHighListedJointSearch_of_families B D threeHighCanonicalResidual F
    hF hmem (fun i j _ => hcompat i j) hcap
  rw [hfalse] at htrue
  contradiction

end Erdos85
#print axioms Erdos85.threeHighSelectedJointCertificate_no_joint
