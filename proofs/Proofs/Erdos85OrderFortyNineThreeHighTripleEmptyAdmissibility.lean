import Proofs.Erdos85EncodedDegreeFilter
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCoordinateDegrees

namespace Erdos85
open SimpleGraph
noncomputable section

/-- Every exact encoding of the actual empty graph passes both executable gates. -/
theorem threeHigh_triple_empty_encoding_admissible
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u)
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ p q, decide (G.Adj (e p).val (e q).val) = B p q) :
    encodedC4Free B = true ∧
      encodedDegreeProfile B (fun i => if i = 23 then 6 else 4) = true := by
  classical
  constructor
  · exact encodedC4Free_of_injective_graph G hfree (fun p => (e p).val)
      (fun _ _ h => e.injective (Subtype.ext h)) B hB
  · let H := SimpleGraph.comap e
      (G.induce (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    apply encodedDegreeProfile_of_graph H B
    · exact hB
    · exact threeHigh_triple_empty_coordinate_degrees G hfree hmin hHigh hone z hz hu huz e heu

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_encoding_admissible
