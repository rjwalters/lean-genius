import Proofs.Erdos85ThreeHighBlockResolution
import Proofs.Erdos85FinitePivotFamilySearch

namespace Erdos85

def threeHighBlockFamilySearch (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24))
    (accept : Finset (Finset (Fin 24)) → Bool) : Bool :=
  finitePivotFamilySearch (threeHighBlockTripleList B R blocks) accept 6 R ∅

theorem threeHighBlockFamilySearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (blocks : Fin 3 → Finset (Fin 24))
    (accept : Finset (Finset (Fin 24)) → Bool)
    (F : Finset (Finset (Fin 24))) (hF : F ∈ threeHighResolutionDomain B R)
    (hcap : ∀ S ∈ F, encodedTripleBlockCap blocks S = true) (ha : accept F = true) :
    threeHighBlockFamilySearch B R blocks accept = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePivotFamilySearch_of_family _ accept 6 R F ∅ ?_ hcard ?_ hdis hcover
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

end Erdos85
#print axioms Erdos85.threeHighBlockFamilySearch_of_mem
