import Proofs.Erdos85ExteriorPairDegreeCapacity
import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine

/-! The actual H7/T0 exterior-pair graph obeys degree capacity7-2d_E.
Every outside common neighbor is routed to the singleton-support class
using the actual low-empty quotient capacity. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem sevenHigh_t0_exteriorPair_degree_add_two_empty_neighbors_le_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (u : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))) :
    (exteriorPairGraph G (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))).degree u +
      2 * (G.neighborFinset u.val ∩ sevenHighT0LowSupportFiber G 0).card ≤ 7 := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let S := sevenHighT0LowSupportFiber G 1
  have hcount : ∀ z, G.neighborFinset z ∩ E =
      (((G.neighborFinset z).filter fun x => (orderFortyNineHighSupport G x).card = 0).filter
        fun x => x ∉ orderFortyNineHighVertices G) := by
    intro z
    ext x
    simp [E, sevenHighT0LowSupportFiber, orderFortyNineLowVertices,
      and_assoc, and_left_comm, and_comm]
  have hlow : ∀ z ∈ orderFortyNineLowVertices G, G.degree z = 7 := by
    intro z hz
    have hnot := (Finset.mem_sdiff.mp hz).2
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (by decide) z with h7 | h8
    · exact h7
    · exact False.elim (hnot (by simp [orderFortyNineHighVertices, h8]))
  have hroute : ∀ (x y : (↑E : Set (Fin 49))) (z : Fin 49), x ≠ y → z ∉ E →
      G.Adj x.val z → G.Adj y.val z → z ∈ S := by
    intro x y z hxy hz hxz hyz
    have hzNotHigh : z ∉ orderFortyNineHighVertices G := by
      intro hzHigh
      have hxzero := (Finset.mem_filter.mp x.property).2
      have hempty := Finset.card_eq_zero.mp hxzero
      have hmem : z ∈ orderFortyNineHighSupport G x.val :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz, hzHigh⟩
      rw [hempty] at hmem
      exact Finset.notMem_empty _ hmem
    have hzLow : z ∈ orderFortyNineLowVertices G :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzNotHigh⟩
    have hcap := sevenHigh_t0_lowEmptyNeighborCount_add_support_le_three
      G hfree hmin hHigh hzero (hlow z hzLow)
    rw [← hcount z] at hcap
    have htwo : 2 ≤ (G.neighborFinset z ∩ E).card := by
      have hsub : ({x.val,y.val} : Finset (Fin 49)) ⊆ G.neighborFinset z ∩ E := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxz.symm, x.property⟩
        · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hyz.symm, y.property⟩
      have hne : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
      simpa [hne] using Finset.card_le_card hsub
    have hpos : (orderFortyNineHighSupport G z).card ≠ 0 := by
      intro h0
      exact hz (Finset.mem_filter.mpr ⟨hzLow,h0⟩)
    have hone : (orderFortyNineHighSupport G z).card = 1 := by omega
    exact Finset.mem_filter.mpr ⟨hzLow,hone⟩
  have htwo : ∀ z ∈ S, (G.neighborFinset z ∩ E).card ≤ 2 := by
    intro z hz
    have hp := Finset.mem_filter.mp hz
    rw [hcount z]
    exact sevenHigh_t0_singletonRoot_lowEmptyNeighbor_bound
      G hfree hmin hHigh hzero (hlow z hp.1) hp.2
  have hbound := exteriorPair_degree_le_routed_neighbor_count G E S hroute htwo u
  have hsub : G.neighborFinset u.val ∩ S ⊆
      (G.neighborFinset u.val).filter (fun x => (orderFortyNineHighSupport G x).card = 1) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hz).1,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2⟩
  have hsle := Finset.card_le_card hsub
  have hu := Finset.mem_filter.mp u.property
  have hprofile := sevenHigh_t0_emptyRoot_lowEmpty_singleton_profile
    G hfree hmin hHigh hzero (hlow u.val hu.1) hu.2
  rw [← hcount u.val] at hprofile
  change (exteriorPairGraph G (↑E : Set (Fin 49))).degree u +
      2 * (G.neighborFinset u.val ∩ E).card ≤ 7
  omega

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_exteriorPair_degree_add_two_empty_neighbors_le_seven
