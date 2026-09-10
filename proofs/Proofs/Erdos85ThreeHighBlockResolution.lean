import Proofs.Erdos85ThreeHighDirectEligibility
import Proofs.Erdos85OrderFortyNineThreeHighTripleCoordinateBlockCap

namespace Erdos85

def threeHighBlockTripleList (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24)) : List (Finset (Fin 24)) :=
  (threeHighDirectTripleList B R).filter (encodedTripleBlockCap blocks)

def threeHighBlockResolutionSearch (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24)) : Bool :=
  finitePivotCoverSearch (threeHighBlockTripleList B R blocks) 6 R

theorem threeHighBlockResolutionSearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24))
    (F : Finset (Finset (Fin 24))) (hF : F ∈ threeHighResolutionDomain B R)
    (hcap : ∀ S ∈ F, encodedTripleBlockCap blocks S = true) :
    threeHighBlockResolutionSearch B R blocks = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePivotCoverSearch_of_family _ 6 R F ?_ hcard ?_ hdis hcover
  · intro S hS
    apply List.mem_filter.mpr
    refine ⟨?_,hcap S hS⟩
    rw [threeHighDirectTripleList_eq]
    exact (mem_threeHighEligibleTripleList B R S).mpr (hsub hS)
  · intro S hS
    apply Finset.card_pos.mp
    have hc := ((mem_threeHighEligibleTriples B R S).mp (hsub hS)).2.1
    omega

end Erdos85
#print axioms Erdos85.threeHighBlockResolutionSearch_of_mem
