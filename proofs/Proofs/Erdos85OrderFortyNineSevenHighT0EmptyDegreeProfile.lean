import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine
import Proofs.Erdos85SevenVertexSubcubicEquality

/-!
# Degree counts in the actual H7 nine-edge empty-support endpoint

The generic subcubic equality theorem determines the induced degree counts
without enumerating the two possible shapes. This file supplies its actual
order49 graph hypotheses from the existing H7 support quotient.
-/

namespace Erdos85
open SimpleGraph
noncomputable section

/-- At the nine-edge endpoint, exactly three empty vertices have two empty
neighbors and four have three empty neighbors. -/
theorem sevenHigh_t0_nine_empty_edges_degree_counts
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (hedges : sevenHighT0InternalEdgeCount G 0 = 9) :
    let H := G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))
    (Finset.univ.filter (fun x => H.degree x = 2)).card = 3 ∧
      (Finset.univ.filter (fun x => H.degree x = 3)).card = 4 := by
  classical
  dsimp only
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcardZero : (sevenHighT0LowSupportFiber G 0).card = 7 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) = 7 := by
    simpa using hcardZero
  exact sevenVertex_subcubic_nine_edges_degree_counts
    (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (not_containsC4_induce_finset G hfree (sevenHighT0LowSupportFiber G 0)) hcard
    (sevenHigh_t0_empty_induce_degree_le_three G hfree hmin hHigh hzero) hedges

end
end Erdos85

#print axioms Erdos85.sevenHigh_t0_nine_empty_edges_degree_counts
