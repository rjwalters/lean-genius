import Proofs.Erdos85ThreeHighPrunedJointResolution
import Proofs.Erdos85ColorTripleSupportPruning
import Proofs.Erdos85ThreeHighCanonicalTripleShapes

namespace Erdos85

/-- The caller supplies triple lists, allowing sound filters before exact cover. -/
def threeHighListedJointSearch (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (R : Fin 3 → Finset (Fin 24)) : Bool :=
  finitePivotFamilySearch (D 0) (fun F =>
    finitePrunedFamilySearch (D 1) (fun K => encodedFamilyIntersectionCap K F)
      (fun K => threeHighFamilyPairCompatible B F K &&
        finitePrunedFamilySearch (D 2) (fun L => encodedFamilyIntersectionCap L (F ∪ K))
          (fun L => threeHighFamilyPairCompatible B F L && threeHighFamilyPairCompatible B K L)
          6 (R 2) ∅) 6 (R 1) ∅) 6 (R 0) ∅

private theorem listed_pivot_of_resolution
    (B : Fin 24 → Fin 24 → Bool) (D : List (Finset (Fin 24)))
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) (hD : ∀ S ∈ F, S ∈ D)
    (accept : Finset (Finset (Fin 24)) → Bool) (ha : accept F = true) :
    finitePivotFamilySearch D accept 6 R ∅ = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePivotFamilySearch_of_family D accept 6 R F ∅ hD hcard ?_ hdis hcover
    (by simpa using ha)
  intro S hS
  apply Finset.card_pos.mp
  have hc := ((mem_threeHighEligibleTriples B R S).mp (hsub hS)).2.1
  omega

private theorem listed_pruned_of_resolution
    (B : Fin 24 → Fin 24 → Bool) (D : List (Finset (Fin 24)))
    (R : Finset (Fin 24)) (F prior : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) (hD : ∀ S ∈ F, S ∈ D)
    (hprior : encodedFamilyIntersectionCap F prior = true)
    (accept : Finset (Finset (Fin 24)) → Bool) (ha : accept F = true) :
    finitePrunedFamilySearch D (fun K => encodedFamilyIntersectionCap K prior) accept 6 R ∅ = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePrunedFamilySearch_of_family D _ accept 6 R F ∅ hD hcard ?_ hdis hcover ?_
    (by simpa using ha)
  · intro S hS
    apply Finset.card_pos.mp
    have hc := ((mem_threeHighEligibleTriples B R S).mp (hsub hS)).2.1
    omega
  · intro K hK
    exact encodedFamilyIntersectionCap_mono K prior F prior
      (by simpa using hK) (Finset.Subset.refl _) hprior

theorem threeHighListedJointSearch_of_families
    (B : Fin 24 → Fin 24 → Bool)
    (D : Fin 3 → List (Finset (Fin 24))) (R : Fin 3 → Finset (Fin 24))
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hF : ∀ k, F k ∈ threeHighResolutionDomain B (R k))
    (hD : ∀ k S, S ∈ F k → S ∈ D k)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighListedJointSearch B D R = true := by
  have hp (i j : Fin 3) (hij : i ≠ j) : threeHighFamilyPairCompatible B (F i) (F j) = true := by
    simp only [threeHighFamilyPairCompatible, Bool.and_eq_true]
    exact ⟨⟨hcompat i j hij, hcompat j i hij.symm⟩,hcap i j hij⟩
  unfold threeHighListedJointSearch
  apply listed_pivot_of_resolution B _ _ (F 0) (hF 0) (hD 0)
  apply listed_pruned_of_resolution B _ _ (F 1) (F 0) (hF 1) (hD 1)
    (hcap 1 0 (by decide))
  simp only [Bool.and_eq_true]
  refine ⟨hp 0 1 (by decide), ?_⟩
  apply listed_pruned_of_resolution B _ _ (F 2) (F 0 ∪ F 1) (hF 2) (hD 2)
    (encodedFamilyIntersectionCap_union_right _ _ _ (hcap 2 0 (by decide)) (hcap 2 1 (by decide)))
  simp only [Bool.and_eq_true]
  exact ⟨hp 0 2 (by decide), hp 1 2 (by decide)⟩

/-- Apply a caller-selected number of support passes before joint exact cover. -/
def threeHighSupportedJointSearch (B : Fin 24 → Fin 24 → Bool) (n : Nat) : Bool :=
  threeHighListedJointSearch B
    (threeHighTripleSupportRounds B
      (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) n)
    threeHighCanonicalResidual

theorem threeHighSupportedJointSearch_of_families
    (B : Fin 24 → Fin 24 → Bool) (n : Nat)
    (F : Fin 3 → ThreeHighResolutionFamily)
    (hF : ∀ k, F k ∈ threeHighResolutionDomain B (threeHighCanonicalResidual k))
    (hblocks : ∀ k S, S ∈ F k → encodedTripleBlockCap threeHighCanonicalRow S = true)
    (hcompat : ∀ i j, i ≠ j → encodedFamilyCompatibility B (F i) (F j) = true)
    (hcap : ∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true) :
    threeHighSupportedJointSearch B n = true := by
  apply threeHighListedJointSearch_of_families B _ _ F hF _ hcompat hcap
  apply threeHighTripleSupportRounds_preserves B _ F _ hcompat n
  intro k S hS
  rw [threeHighCanonicalTripleShapes_filter]
  apply List.mem_filter.mpr
  refine ⟨?_,hblocks k S hS⟩
  rw [threeHighDirectTripleList_eq]
  exact (mem_threeHighEligibleTripleList B _ S).mpr
    (((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).1 hS)

end Erdos85
#print axioms Erdos85.threeHighListedJointSearch_of_families

#print axioms Erdos85.threeHighSupportedJointSearch_of_families
