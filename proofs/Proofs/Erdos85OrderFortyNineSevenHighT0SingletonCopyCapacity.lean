import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity
import Proofs.Erdos85OrderFortyNineSevenHighT0SingletonCopies

/-!
# Empty-neighbor capacity of each actual singleton copy

The corrected finite quotient model needs more than two copies per high
label: every actual singleton-support vertex has at most two empty-support
low neighbors.  This file derives that copywise capacity directly from the
graph-facing local quotient theorem.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem sevenHighT0SingletonVertex_degree_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (copy : Fin 2) :
    G.degree (sevenHighT0SingletonVertex
      G hfree hmin hHigh hzero e w copy) = 7 := by
  let s := sevenHighT0SingletonVertex
    G hfree hmin hHigh hzero e w copy
  have hsSupport : (orderFortyNineHighSupport G s).card = 1 := by
    rw [← sevenHighLabeledSupport_card G e]
    change (sevenHighLabeledSupport G e
      (sevenHighT0SingletonVertex
        G hfree hmin hHigh hzero e w copy)).card = 1
    rw [sevenHighT0SingletonVertex_support]
    simp
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) s with hs7 | hs8
  · exact hs7
  · have hsHigh : s ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hs8]
    have hsZero := orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin (Fintype.card_fin 49) hsHigh
    change (orderFortyNineHighSupport G s).card = 0 at hsZero
    omega

/-- Each of the fourteen actual singleton copies is adjacent to at most two
actual low empty-support vertices. -/
theorem sevenHighT0SingletonVertex_lowEmptyNeighbor_bound
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (w : Fin 7) (copy : Fin 2) :
    (((G.neighborFinset (sevenHighT0SingletonVertex
      G hfree hmin hHigh hzero e w copy)).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0).filter fun x =>
          x ∉ orderFortyNineHighVertices G).card ≤ 2 := by
  have hs7 := sevenHighT0SingletonVertex_degree_eq_seven
    G hfree hmin hHigh hzero e w copy
  have hsSupport : (orderFortyNineHighSupport G
      (sevenHighT0SingletonVertex
        G hfree hmin hHigh hzero e w copy)).card = 1 := by
    rw [← sevenHighLabeledSupport_card G e]
    rw [sevenHighT0SingletonVertex_support]
    simp
  exact sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
    G hfree hmin hHigh hzero hs7 hsSupport

end

end Erdos85

#print axioms Erdos85.sevenHighT0SingletonVertex_lowEmptyNeighbor_bound
