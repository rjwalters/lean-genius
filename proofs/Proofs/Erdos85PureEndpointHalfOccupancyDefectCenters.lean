import Proofs.Erdos85PureEndpointNeighborOwnerDeficit
import Proofs.Erdos85PureEndpointHalfOccupancyDefectOwners

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
    rw [c4Free_fullCenter_defectNeighbors_eq_unusedOwners
      G hfree S hreg hwNotFull]
    apply mem_filter.mpr
    refine ⟨hiData.1, ?_⟩
    intro y hy hiOwner
    apply hiData.2
    apply mem_biUnion.mpr
    exact ⟨y, hy, mem_inter.mpr ⟨hiOwner, hiData.1⟩⟩
  have htwo : 2 ≤
      ((secondOrderDefectGraph G).neighborFinset w ∩ F).card :=
    le_trans hUnused (card_le_card hsub)
  exact ⟨w, hwOcc, by simpa [F] using htwo⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_two_defectCenters
