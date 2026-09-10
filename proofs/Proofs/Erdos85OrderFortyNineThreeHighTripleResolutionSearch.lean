import Proofs.Erdos85ThreeHighTripleList
import Proofs.Erdos85OrderFortyNineThreeHighTripleResolution

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_actual_resolution_search
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
    threeHighResolutionSearch B (Finset.univ \ (C z ∪ C s)) = true := by
  exact threeHighResolutionSearch_of_mem B _ _
    (threeHigh_triple_coordinate_resolution_mem G hfree hmin hHigh hone z h s hz hh hs hsz e B hB)

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_actual_resolution_search
