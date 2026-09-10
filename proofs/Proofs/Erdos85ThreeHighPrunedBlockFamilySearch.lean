import Proofs.Erdos85ThreeHighBlockFamilySearch
import Proofs.Erdos85FinitePrunedFamilySearch
import Proofs.Erdos85FamilyIntersectionPruning

namespace Erdos85

def threeHighPrunedBlockFamilySearch (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24))
    (prior : Finset (Finset (Fin 24))) (accept : Finset (Finset (Fin 24)) → Bool) : Bool :=
  finitePrunedFamilySearch (threeHighBlockTripleList B R blocks)
    (fun chosen => encodedFamilyIntersectionCap chosen prior) accept 6 R ∅

theorem threeHighPrunedBlockFamilySearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24))
    (prior : Finset (Finset (Fin 24))) (accept : Finset (Finset (Fin 24)) → Bool)
    (F : Finset (Finset (Fin 24))) (hF : F ∈ threeHighResolutionDomain B R)
    (hcap : ∀ S ∈ F, encodedTripleBlockCap blocks S = true)
    (hprior : encodedFamilyIntersectionCap F prior = true) (ha : accept F = true) :
    threeHighPrunedBlockFamilySearch B R blocks prior accept = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePrunedFamilySearch_of_family _ _ accept 6 R F ∅ ?_ hcard ?_ hdis hcover ?_
    (by simpa using ha)
  · intro S hS
    apply List.mem_filter.mpr
    refine ⟨?_,hcap S hS⟩
    rw [threeHighDirectTripleList_eq]
    exact (mem_threeHighEligibleTripleList B R S).mpr (hsub hS)
  · intro S hS
    apply Finset.card_pos.mp
    have hc := ((mem_threeHighEligibleTriples B R S).mp (hsub hS)).2.1
    omega
  · intro K hK
    apply encodedFamilyIntersectionCap_mono K prior F prior
      (by simpa using hK) (Finset.Subset.refl _) hprior

theorem encodedFamilyIntersectionCap_union_right
    (F K L : Finset (Finset (Fin 24)))
    (hK : encodedFamilyIntersectionCap F K = true)
    (hL : encodedFamilyIntersectionCap F L = true) :
    encodedFamilyIntersectionCap F (K ∪ L) = true := by
  have hk := of_decide_eq_true hK
  have hl := of_decide_eq_true hL
  apply decide_eq_true_iff.mpr
  intro S hS T hT
  rcases Finset.mem_union.mp hT with hT | hT
  · exact hk S hS T hT
  · exact hl S hS T hT

end Erdos85
#print axioms Erdos85.threeHighPrunedBlockFamilySearch_of_mem
#print axioms Erdos85.encodedFamilyIntersectionCap_union_right
