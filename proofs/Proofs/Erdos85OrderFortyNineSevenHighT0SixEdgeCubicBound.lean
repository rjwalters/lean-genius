import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality
import Proofs.Erdos85EdgesAvoidingSubsetBound

/-!
# A six-edge H7 empty graph has at most two cubic vertices

Three cubic empty vertices leave capacity one each. The four remaining
vertices allow at most six exterior-pair edges, contradicting the lower
bound eleven. This excludes the triangle with three pendant leaves and an
isolated vertex without a finite isomorphism classification or spectrum.
-/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem sevenHigh_t0_six_empty_edges_no_three_cubic
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 6)
    (U : Finset (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (hU : U.card = 3)
    (hdeg : ∀ v ∈ U,
      (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3) : False := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hE : E.card = 7 := by
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hE
  have hsum : (∑ v ∈ U,
      (7 - 2 * (G.neighborFinset v.val ∩ E).card)) = 3 := by
    calc
      _ = ∑ _v ∈ U, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [hdeg v hv]
      _ = 3 := by simp [hU]
  have hupper := edges_avoiding_subset_card_le_choose (insideCommonFreeGraph G E) U
  rw [hcard, hU] at hupper
  rw [show Nat.choose (7 - 3) 2 = 6 from by decide] at hupper
  have h := sevenHigh_t0_vertex_subset_exterior_capacity_inequality
    G hfree hmin hHigh hzero U
  change 35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
    (∑ v ∈ U, (7 - 2 * (G.neighborFinset v.val ∩ E).card)) +
    ((insideCommonFreeGraph G E).edgeFinset.filter (fun e => ∀ v ∈ U, v ∉ e)).card at h
  rw [ha, hsum] at h
  have hfinal := h.trans (Nat.add_le_add_left hupper (4 * 6 + 3))
  norm_num at hfinal

theorem sevenHigh_t0_six_empty_edges_cubic_count_le_two
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 6) :
    (Finset.univ.filter fun v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) =>
      (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3).card ≤ 2 := by
  classical
  by_contra h
  have hthree : 3 ≤ (Finset.univ.filter
      fun v : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) =>
        (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card = 3).card := by omega
  obtain ⟨U, hsub, hU⟩ := Finset.exists_subset_card_eq hthree
  apply sevenHigh_t0_six_empty_edges_no_three_cubic G hfree hmin hHigh hzero ha U hU
  intro v hv
  exact (Finset.mem_filter.mp (hsub hv)).2

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_six_empty_edges_no_three_cubic
#print axioms Erdos85.sevenHigh_t0_six_empty_edges_cubic_count_le_two
