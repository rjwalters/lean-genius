import Proofs.Erdos85OrderFortyNineSevenHighT0SixEdgeDegreePattern

/-! Deleting the unique cubic root leaves a graph of degree one. -/
set_option maxHeartbeats 2000000
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem residual_neighbor_card_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (hcard : Fintype.card V = 7)
    (h1 : (Finset.univ.filter fun v => G.degree v = 1).card = 3)
    (h2 : (Finset.univ.filter fun v => G.degree v = 2).card = 3)
    (hn : G.neighborFinset u = (Finset.univ.filter fun v => G.degree v = 2)) :
    ∀ v, v ≠ u → ((G.neighborFinset v).erase u).card = 1 := by
  classical
  let L1 := Finset.univ.filter fun v => G.degree v = 1
  let L2 := Finset.univ.filter fun v => G.degree v = 2
  have hu : G.degree u = 3 := by rw [← G.card_neighborFinset_eq_degree, hn, h2]
  have hdis : Disjoint L1 L2 := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have ha := (Finset.mem_filter.mp hv).2
    have hb := (Finset.mem_filter.mp hw).2
    omega
  have huL : u ∉ L1 ∪ L2 := by simp [L1,L2,hu]
  have hsize : (insert u (L1 ∪ L2)).card = 7 := by
    rw [Finset.card_insert_of_notMem huL, Finset.card_union_of_disjoint hdis]
    change (Finset.univ.filter fun v => G.degree v = 1).card +
      (Finset.univ.filter fun v => G.degree v = 2).card + 1 = 7
    rw [h1,h2]
  have hfull : insert u (L1 ∪ L2) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [hsize,hcard])
  intro v hv
  have hmem : v ∈ insert u (L1 ∪ L2) := by rw [hfull]; exact Finset.mem_univ _
  have hL : v ∈ L1 ∪ L2 := (Finset.mem_insert.mp hmem).resolve_left hv
  rcases Finset.mem_union.mp hL with hv1 | hv2
  · have hd : G.degree v = 1 := (Finset.mem_filter.mp hv1).2
    have hnot : u ∉ G.neighborFinset v := by
      intro hm
      have hrev : v ∈ G.neighborFinset u :=
        (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hm).symm
      rw [hn] at hrev
      have := (Finset.mem_filter.mp hrev).2
      omega
    rw [Finset.erase_eq_of_notMem hnot, G.card_neighborFinset_eq_degree, hd]
  · have hd : G.degree v = 2 := (Finset.mem_filter.mp hv2).2
    have hmem : u ∈ G.neighborFinset v := by
      have hvN : v ∈ G.neighborFinset u := by rw [hn]; exact hv2
      exact (G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp hvN).symm
    rw [Finset.card_erase_of_mem hmem, G.card_neighborFinset_eq_degree, hd]


/-- The six vertices other than a cubic empty root have exactly one
remaining empty neighbor after that root is removed. -/
theorem sevenHigh_t0_six_empty_edges_residual_matching
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (ha : sevenHighT0InternalEdgeCount G 0 = 6)
    (u : (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (hu : (G.neighborFinset u.val ∩ sevenHighT0LowSupportFiber G 0).card = 3) :
    let A := G.induce (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))
    ∀ v, v ≠ u → ((A.neighborFinset v).erase u).card = 1 := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let A := G.induce (↑E : Set (Fin 49))
  obtain ⟨_,h1,h2,hn⟩ := sevenHigh_t0_six_empty_edges_one_cubic_degree_pattern
    G hfree hmin hHigh hzero ha u hu
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hE : E.card = 7 := by
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hE
  exact residual_neighbor_card_one A u hcard h1 h2 hn

end
end Erdos85

#print axioms Erdos85.sevenHigh_t0_six_empty_edges_residual_matching
