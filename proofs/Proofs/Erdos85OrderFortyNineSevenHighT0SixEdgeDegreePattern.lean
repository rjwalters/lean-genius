import Proofs.Erdos85OrderFortyNineSevenHighT0CubicDegreeTwoAdjacency
import Proofs.Erdos85OrderFortyNineSevenHighT0SixEdgeOneCubic
import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine

set_option maxHeartbeats 2000000

namespace Erdos85
open SimpleGraph
noncomputable section

private theorem seven_degree_count_pattern
    {V : Type*} [Fintype V] [DecidableEq V] (d : V → ℕ)
    (hcard : Fintype.card V = 7) (hmax : ∀ v, d v ≤ 3)
    (hsum : ∑ v, d v = 12)
    (hthree : (Finset.univ.filter fun v => d v = 3).card = 1)
    (htwo : (Finset.univ.filter fun v => d v = 2).card ≤ 3) :
    (Finset.univ.filter fun v => d v = 0).card = 0 ∧
    (Finset.univ.filter fun v => d v = 1).card = 3 ∧
    (Finset.univ.filter fun v => d v = 2).card = 3 := by
  classical
  have hi (j k : ℕ) : (∑ v, if d v = j then k else 0) =
      k * (Finset.univ.filter fun v => d v = j).card := by
    rw [← Finset.sum_filter]
    simp [Nat.mul_comm]
  have hc : (∑ v, ((if d v = 0 then 1 else 0) + (if d v = 1 then 1 else 0) +
      (if d v = 2 then 1 else 0) + (if d v = 3 then 1 else 0))) = 7 := by
    calc
      _ = ∑ _v : V, 1 := Finset.sum_congr rfl (by
        intro v _
        have := hmax v
        split_ifs <;> omega)
      _ = 7 := by simp [hcard]
  have hw : (∑ v, ((if d v = 1 then 1 else 0) + (if d v = 2 then 2 else 0) +
      (if d v = 3 then 3 else 0))) = 12 := by
    calc
      _ = ∑ v, d v := Finset.sum_congr rfl (by
        intro v _
        have := hmax v
        split_ifs <;> omega)
      _ = 12 := hsum
  simp only [Finset.sum_add_distrib, hi, Nat.one_mul] at hc hw
  omega


/-- The degree count forced by a unique cubic root adjacent to every
vertex of degree two in a seven-vertex, six-edge subcubic graph. -/
theorem sevenVertex_sixEdge_one_cubic_degree_pattern
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 7) (hedges : G.edgeFinset.card = 6)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hthree : (Finset.univ.filter fun v => G.degree v = 3).card = 1)
    (u : V) (hu : G.degree u = 3)
    (hadj : ∀ v, G.degree v = 2 → G.Adj u v) :
    (Finset.univ.filter fun v => G.degree v = 0).card = 0 ∧
    (Finset.univ.filter fun v => G.degree v = 1).card = 3 ∧
    (Finset.univ.filter fun v => G.degree v = 2).card = 3 ∧
    G.neighborFinset u = (Finset.univ.filter fun v => G.degree v = 2) := by
  classical
  have hsub : (Finset.univ.filter fun v => G.degree v = 2) ⊆ G.neighborFinset u := by
    intro v hv
    exact (G.mem_neighborFinset _ _).mpr (hadj v (Finset.mem_filter.mp hv).2)
  have hN : (G.neighborFinset u).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hu]
  have htwo : (Finset.univ.filter fun v => G.degree v = 2).card ≤ 3 :=
    (Finset.card_le_card hsub).trans_eq hN
  have hsum : ∑ v, G.degree v = 12 := by
    rw [G.sum_degrees_eq_twice_card_edges, hedges]
  obtain ⟨h0,h1,h2⟩ := seven_degree_count_pattern (V := V) (fun v : V => G.degree v) hcard hmax hsum hthree htwo
  refine ⟨h0,h1,h2, ?_⟩
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm


/-- In the actual H7 six-edge case, existence of a cubic empty vertex
forces degree pattern (3,2,2,2,1,1,1) and identifies its neighbors. -/
theorem sevenHigh_t0_six_empty_edges_one_cubic_degree_pattern
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
    (Finset.univ.filter fun v => A.degree v = 0).card = 0 ∧
    (Finset.univ.filter fun v => A.degree v = 1).card = 3 ∧
    (Finset.univ.filter fun v => A.degree v = 2).card = 3 ∧
    A.neighborFinset u = (Finset.univ.filter fun v => A.degree v = 2) := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let A := G.induce (↑E : Set (Fin 49))
  have hdeg (v : (↑E : Set (Fin 49))) :
      A.degree v = (G.neighborFinset v.val ∩ E).card := by
    rw [← A.card_neighborFinset_eq_degree]
    have h := congrArg Finset.card (G.map_neighborFinset_induce (s := (↑E : Set (Fin 49))) v)
    simp only [Finset.card_map, Finset.toFinset_coe] at h
    convert h using 1
    congr 1
    ext x
    simp only [SimpleGraph.mem_neighborFinset]
    rfl
  have hcensus := sevenHigh_t0_global_incidence G hfree hmin hHigh hzero
  have hE : E.card = 7 := by
    simpa [E, sevenHighT0LowSupportFiber, orderFortyNineHighSupport,
      orderFortyNineHighIncidenceCount] using hcensus.1
  have hcard : Fintype.card (↑E : Set (Fin 49)) = 7 := by simpa using hE
  have hmax := sevenHigh_t0_empty_induce_degree_le_three G hfree hmin hHigh hzero
  have hle : (Finset.univ.filter fun v => A.degree v = 3).card ≤ 1 := by
    simpa only [hdeg] using sevenHigh_t0_six_empty_edges_cubic_count_le_one
      G hfree hmin hHigh hzero ha
  have hpos : 0 < (Finset.univ.filter fun v => A.degree v = 3).card := by
    apply Finset.card_pos.mpr
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hdeg u).trans hu⟩⟩
  have hthree : (Finset.univ.filter fun v => A.degree v = 3).card = 1 := by omega
  apply sevenVertex_sixEdge_one_cubic_degree_pattern A hcard ha hmax hthree u ((hdeg u).trans hu)
  intro v hv
  exact sevenHigh_t0_six_empty_edges_cubic_adj_degree_two
    G hfree hmin hHigh hzero ha u v hu ((hdeg v).symm.trans hv)

end
end Erdos85

#print axioms Erdos85.sevenVertex_sixEdge_one_cubic_degree_pattern

#print axioms Erdos85.sevenHigh_t0_six_empty_edges_one_cubic_degree_pattern
