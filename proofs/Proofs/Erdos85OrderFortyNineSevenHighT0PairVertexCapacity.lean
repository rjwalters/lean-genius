import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity
import Proofs.Erdos85OrderFortyNineSevenHighT0PairVertices

/-!
# Empty-neighbor capacity of each actual pair-support vertex

The twenty-one canonical pair-support vertices are genuine low vertices.
Consequently the graph-facing local quotient capacity applies to each one:
it has at most one low empty-support neighbor.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem sevenHighT0PairVertex_degree_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : SevenHighT0PairIndex) :
    G.degree (sevenHighT0PairVertex
      G hfree hmin hzero e key) = 7 := by
  let p := sevenHighT0PairVertex G hfree hmin hzero e key
  have hpSupport : (orderFortyNineHighSupport G p).card = 2 := by
    rw [← sevenHighLabeledSupport_card G e]
    change (sevenHighLabeledSupport G e
      (sevenHighT0PairVertex G hfree hmin hzero e key)).card = 2
    rw [sevenHighT0PairVertex_support]
    simp [ne_of_lt key.2]
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) p with hp7 | hp8
  · exact hp7
  · have hpHigh : p ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hp8]
    have hpZero := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin (Fintype.card_fin 49) hpHigh
    change (orderFortyNineHighSupport G p).card = 0 at hpZero
    omega

/-- Each of the twenty-one actual pair-support vertices is adjacent to at most
one actual low empty-support vertex. -/
theorem sevenHighT0PairVertex_lowEmptyNeighbor_bound
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (key : SevenHighT0PairIndex) :
    (((G.neighborFinset (sevenHighT0PairVertex
      G hfree hmin hzero e key)).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0).filter fun x =>
          x ∉ orderFortyNineHighVertices G).card ≤ 1 := by
  have hp7 := sevenHighT0PairVertex_degree_eq_seven
    G hfree hmin hzero e key
  have hpSupport : (orderFortyNineHighSupport G
      (sevenHighT0PairVertex G hfree hmin hzero e key)).card = 2 := by
    rw [← sevenHighLabeledSupport_card G e]
    rw [sevenHighT0PairVertex_support]
    simp [ne_of_lt key.2]
  exact sevenHigh_t0_pairRoot_lowEmptyNeighbor_bound
    G hfree hmin hHigh hzero hp7 hpSupport

end

end Erdos85

#print axioms Erdos85.sevenHighT0PairVertex_lowEmptyNeighbor_bound
