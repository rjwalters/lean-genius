import Proofs.Erdos85SevenVertexSubcubicBound
import Proofs.Erdos85ThreeLevelEigenSupportC4Bound
import Proofs.Erdos85OrderFortyNineSevenHighT0GlobalQuotientParity
import Proofs.Erdos85OrderFortyNineSevenHighT0LocalQuotientCapacity

/-!
# Nine-edge bound for the actual H7 empty-support induced graph

The existing local quotient gives maximum induced degree three and seven
empty-support vertices. The generic C4-free seven-vertex bound removes the
old ten-edge case, tightening the actual graph parameter from 6..10 to 6..9.
-/

set_option maxHeartbeats 2000000

namespace Erdos85
open SimpleGraph
noncomputable section

/-- Transfer the actual empty-neighbor capacity to the induced graph. -/
theorem sevenHigh_t0_empty_induce_degree_le_three
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (y : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))) :
    (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).degree y ≤ 3 := by
  classical
  have hyLow := (Finset.mem_filter.mp y.property).1
  have hyNotHigh := (Finset.mem_sdiff.mp hyLow).2
  have hy7 : G.degree y.val = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (Fintype.card_fin 49) y.val with h7 | h8
    · exact h7
    · exact False.elim (hyNotHigh (by simp [orderFortyNineHighVertices, h8]))
  have hbound := sevenHigh_t0_emptyRoot_lowEmptyNeighbor_bound
    G hfree hmin hHigh hzero hy7
  have hdeg : (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).degree y =
      (((G.neighborFinset y.val).filter fun x =>
        (orderFortyNineHighSupport G x).card = 0).filter fun x =>
          x ∉ orderFortyNineHighVertices G).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      have hp := x.property
      have ha : G.Adj y.val x.val := by simpa using hx
      simpa [sevenHighT0LowSupportFiber, orderFortyNineLowVertices,
        SimpleGraph.mem_neighborFinset, and_assoc, and_left_comm, and_comm] using And.intro ha hp
    · intro x _ z _ hxz
      exact Subtype.ext hxz
    · intro z hz
      have hp : z ∈ sevenHighT0LowSupportFiber G 0 := by
        simpa [sevenHighT0LowSupportFiber, orderFortyNineLowVertices,
          and_assoc, and_left_comm, and_comm] using And.intro (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2 (Finset.mem_filter.mp hz).2
      refine ⟨⟨z, hp⟩, ?_, rfl⟩
      simpa using (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  exact hdeg.le.trans hbound

/-- The actual H7/T0 empty-support induced graph has between six and nine edges. -/
theorem sevenHigh_t0_internalEmptyEdge_parameter_bounds_nine
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    6 ≤ sevenHighT0InternalEdgeCount G 0 ∧
      sevenHighT0InternalEdgeCount G 0 ≤ 9 := by
  classical
  refine ⟨(sevenHigh_t0_internalEmptyEdge_parameter_bounds G hfree hmin hHigh hzero).1, ?_⟩
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hcardZero : (sevenHighT0LowSupportFiber G 0).card = 7 := by
    simpa [sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) = 7 := by
    simpa using hcardZero
  exact sevenVertex_subcubic_card_edges_le_nine
    (G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (not_containsC4_induce_finset G hfree (sevenHighT0LowSupportFiber G 0)) hcard
    (sevenHigh_t0_empty_induce_degree_le_three G hfree hmin hHigh hzero)

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_empty_induce_degree_le_three

#print axioms Erdos85.sevenHigh_t0_internalEmptyEdge_parameter_bounds_nine
