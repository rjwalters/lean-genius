import Proofs.Erdos85ExteriorPairEdgeLowerBound
import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine

/-! Actual H7 singleton incidences force at least35-4a exterior-pair edges.
This supplies the graph-valid lower bound used by the finite capacity cuts. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem sevenHigh_t0_exteriorPair_edges_add_four_empty_edges_ge_thirtyFive
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
      (exteriorPairGraph G (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).edgeFinset.card := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let S := sevenHighT0LowSupportFiber G 1
  have hcardS : S.card = 14 := by
    have h := (sevenHigh_t0_global_incidence G hfree hmin hHigh hzero).2.1
    simpa [S, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using h
  have hdis : Disjoint S E := by
    apply Finset.disjoint_left.mpr
    intro z hzS hzE
    have h1 := (Finset.mem_filter.mp hzS).2
    have h0 := (Finset.mem_filter.mp hzE).2
    omega
  have htwo : ∀ z ∈ S, (G.neighborFinset z ∩ E).card ≤ 2 := by
    intro z hz
    have hp := Finset.mem_filter.mp hz
    have hznot := (Finset.mem_sdiff.mp hp.1).2
    have hz7 : G.degree z = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (by decide) z with h7 | h8
      · exact h7
      · exact False.elim (hznot (by simp [orderFortyNineHighVertices, h8]))
    have h := sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
      G hfree hmin hHigh hzero hz7 hp.2
    have heq : G.neighborFinset z ∩ E =
        (((G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 0).filter
          fun x => x ∉ orderFortyNineHighVertices G) := by
      ext x
      simp [E, sevenHighT0LowSupportFiber, orderFortyNineLowVertices,
        and_assoc, and_left_comm, and_comm]
    simpa only [heq] using h
  have hbound := exteriorPair_incidence_le_vertices_add_edges G hfree E S hdis htwo
  have hsum : (∑ z ∈ S, (G.neighborFinset z ∩ E).card) =
      sevenHighT0DirectedIncidence G 1 0 := by
    unfold sevenHighT0DirectedIncidence
    apply Finset.sum_congr rfl
    intro z hz
    congr 1
  rw [hsum, hcardS] at hbound
  have hquot := sevenHigh_t0_directed_quotient_one_parameter G hfree hmin hHigh hzero
  dsimp only at hquot
  have hdouble := sevenHighT0DirectedIncidence_self_eq_twice_internalEdges G 0
  change 35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
      (exteriorPairGraph G (↑E : Set (Fin 49))).edgeFinset.card
  omega

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_exteriorPair_edges_add_four_empty_edges_ge_thirtyFive
