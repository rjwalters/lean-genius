import Proofs.Erdos85PureEndpointCenterPrivateIntersection

/-!
# Isolation of off-shore full centers at the pure endpoint

The degree-one full centers are exactly those occurring in the private-point
transversal.  Every point of that transversal lies on the occupied shore,
because its owner is full.  The endpoint internal-degree profile then rules
out degree one off shore, leaving degree zero.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every full center outside `S` is isolated in the graph induced by the
full-center family. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_fullCenter_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∀ v ∈ fullLineCenters G S q, v ∉ S →
      (G.neighborFinset v ∩ fullLineCenters G S q).card = 0 := by
  classical
  obtain ⟨p, _hpInj, hp, hpRange⟩ :=
    c4Free_binarySquare_pureEndpoint_center_mem_privateRange_iff_degree_one
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  intro v hvFull hvOff
  rcases
      (c4Free_binarySquare_pureEndpoint_fullCenter_internalDegree_profile
        G hfree hq hqm hreg hcard S hempty hshore htri v hvFull).2 hvOff with
    hzero | hone
  · exact hzero
  · have hvRange : v ∈ Finset.univ.image p :=
      (hpRange v hvFull).2 hone
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvRange
    have hiFull := (mem_fullLineCenters G S q i.1).mp i.2
    have hiNeighbors : G.neighborFinset i.1 ∩ S = G.neighborFinset i.1 := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
    have hpN : p i ∈ G.neighborFinset i.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using (hp i).1
    have hpS : p i ∈ S := by
      have : p i ∈ G.neighborFinset i.1 ∩ S := by
        rw [hiNeighbors]
        exact hpN
      exact (Finset.mem_inter.mp this).2
    exact (hvOff hpS).elim

/-- Consequently every edge between two full centers has both endpoints on
the occupied shore. -/
theorem c4Free_binarySquare_pureEndpoint_fullCenter_edge_insideShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∀ {u v}, u ∈ fullLineCenters G S q →
      v ∈ fullLineCenters G S q → G.Adj u v → u ∈ S ∧ v ∈ S := by
  classical
  intro u v hu hv huv
  have hiso := c4Free_binarySquare_pureEndpoint_offShore_fullCenter_isolated
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huS : u ∈ S := by
    by_contra huOff
    have hvMem : v ∈ G.neighborFinset u ∩ fullLineCenters G S q :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr huv, hv⟩
    have hzero := hiso u hu huOff
    rw [Finset.card_eq_zero.mp hzero] at hvMem
    simp at hvMem
  have hvS : v ∈ S := by
    by_contra hvOff
    have huMem : u ∈ G.neighborFinset v ∩ fullLineCenters G S q :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr huv.symm, hu⟩
    have hzero := hiso v hv hvOff
    rw [Finset.card_eq_zero.mp hzero] at huMem
    simp at huMem
  exact ⟨huS, hvS⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_offShore_fullCenter_isolated
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_fullCenter_edge_insideShore
