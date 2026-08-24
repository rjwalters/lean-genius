import Proofs.Erdos85PureEndpointNeighborOwnerDeficit

/-!
# Full-center defect neighbors of the forced half-occupancy vertex

An unused owner has no common graph neighbor with the half-occupancy vertex:
all neighbors of a full center lie on the shore, where unusedness was defined.
Thus every unused owner is a second-order defect neighbor.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A preconnected pure endpoint has a half-occupancy vertex with at least two
full-center neighbors in the second-order defect graph. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_two_defectCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ w,
      (G.neighborFinset w ∩ S).card = m ∧
      2 ≤ ((secondOrderDefectGraph G).neighborFinset w ∩
        fullLineCenters G S q).card := by
  classical
  let F := fullLineCenters G S q
  let B := fun w => G.neighborFinset w ∩ S
  let U := fun w => (B w).biUnion fun y => G.neighborFinset y ∩ F
  obtain ⟨w, hwOcc, _hUnionLe, hUnused⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerDeficit
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hwNotFull : w ∉ F := by
    intro hwF
    have hwq := (mem_fullLineCenters G S q w).mp hwF
    rw [hwOcc, hqm] at hwq
    omega
  have hsub : F \ U w ⊆
      (secondOrderDefectGraph G).neighborFinset w ∩ F := by
    intro i hi
    have hiData := mem_sdiff.mp hi
    have hwi : w ≠ i := fun h => hwNotFull (h ▸ hiData.1)
    apply mem_inter.mpr
    refine ⟨((secondOrderDefectGraph G).mem_neighborFinset w i).mpr ?_, hiData.1⟩
    apply (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hwi).mpr
    apply card_eq_zero.mpr
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    have hzData := mem_inter.mp hz
    have hiFull := (mem_fullLineCenters G S q i).mp hiData.1
    have hiNeighbors : G.neighborFinset i ∩ S = G.neighborFinset i := by
      apply eq_of_subset_of_card_le inter_subset_left
      rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
    have hzS : z ∈ S := by
      have : z ∈ G.neighborFinset i ∩ S := by
        rw [hiNeighbors]
        exact hzData.2
      exact (mem_inter.mp this).2
    apply hiData.2
    apply mem_biUnion.mpr
    refine ⟨z, ?_, ?_⟩
    · exact mem_inter.mpr ⟨hzData.1, hzS⟩
    · exact mem_inter.mpr
        ⟨by simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hzData.2,
          hiData.1⟩
  have htwo : 2 ≤
      ((secondOrderDefectGraph G).neighborFinset w ∩ F).card :=
    le_trans hUnused (card_le_card hsub)
  exact ⟨w, hwOcc, by simpa [F] using htwo⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_two_defectCenters
