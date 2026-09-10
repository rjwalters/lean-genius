import Proofs.Erdos85FinitePivotCoverSearch
import Proofs.Erdos85ThreeHighTripleList
import Proofs.Erdos85OrderFortyNineThreeHighTripleResolution

namespace Erdos85
open SimpleGraph

def threeHighPivotResolutionSearch (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24)) : Bool :=
  finitePivotCoverSearch (threeHighEligibleTripleList B R) 6 R

theorem threeHighPivotResolutionSearch_of_mem (B : Fin 24 → Fin 24 → Bool)
    (R : Finset (Fin 24)) (F : Finset (Finset (Fin 24)))
    (hF : F ∈ threeHighResolutionDomain B R) : threeHighPivotResolutionSearch B R = true := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply finitePivotCoverSearch_of_family _ 6 R F
    (fun S hS => (mem_threeHighEligibleTripleList B R S).mpr (hsub hS)) hcard ?_ hdis hcover
  intro S hS
  apply Finset.card_pos.mp
  have hc := ((mem_threeHighEligibleTriples B R S).mp (hsub hS)).2.1
  omega

noncomputable section
theorem threeHigh_triple_actual_pivot_resolution_search
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    let C := fun x => threeHighSingletonCoordinates G e x
    threeHighPivotResolutionSearch B (Finset.univ \ (C z ∪ C s)) = true := by
  exact threeHighPivotResolutionSearch_of_mem B _ _
    (threeHigh_triple_coordinate_resolution_mem G hfree hmin hHigh hone z h s hz hh hs hsz e B hB)

end
end Erdos85
#print axioms Erdos85.threeHighPivotResolutionSearch_of_mem
#print axioms Erdos85.threeHigh_triple_actual_pivot_resolution_search
