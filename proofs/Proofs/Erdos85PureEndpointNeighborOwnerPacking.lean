import Proofs.Erdos85PureEndpointPrivateCollisionHalfOccupancy
import Proofs.Erdos85SecondOrderDefectOwnerDisjointness

/-!
# Local owner packing around a non-center

Distinct neighbors of a vertex outside the chosen center family cannot share
an owner: otherwise they have both that vertex and the owner as common graph
neighbors, producing a four-cycle.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Owner sets of distinct neighbors of a non-center are disjoint. -/
theorem c4Free_neighbor_ownerSets_disjoint_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (C : Finset V)
    {w x y : V} (hwC : w ∉ C) (hxy : x ≠ y)
    (hxw : G.Adj x w) (hyw : G.Adj y w) :
    Disjoint (G.neighborFinset x ∩ C) (G.neighborFinset y ∩ C) := by
  classical
  rw [Finset.disjoint_left]
  intro i hix hiy
  have hxi : G.Adj x i := (G.mem_neighborFinset x i).mp (mem_inter.mp hix).1
  have hyi : G.Adj y i := (G.mem_neighborFinset y i).mp (mem_inter.mp hiy).1
  have hiC : i ∈ C := (mem_inter.mp hix).2
  have hwi : w ≠ i := fun h => hwC (h ▸ hiC)
  apply hfree
  exact containsC4_of_two_common hxy hwi
    hxw.symm hyw.symm hxi.symm hyi.symm

/-- The forced half-occupancy collision supplies an `m`-element local packing
of pairwise disjoint nonempty owner sets, including two singleton-owner
neighbors. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
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
    ∃ x x' w,
      x ∈ S ∧ x' ∈ S ∧ x ≠ x' ∧
      (G.neighborFinset x ∩ fullLineCenters G S q).card = 1 ∧
      (G.neighborFinset x' ∩ fullLineCenters G S q).card = 1 ∧
      G.Adj x w ∧ G.Adj x' w ∧
      (G.neighborFinset w ∩ S).card = m ∧
      w ∉ fullLineCenters G S q ∧
      (∀ y ∈ G.neighborFinset w ∩ S,
        (G.neighborFinset y ∩ fullLineCenters G S q).card = 1 ∨
        (G.neighborFinset y ∩ fullLineCenters G S q).card = 2) ∧
      (∀ y ∈ G.neighborFinset w ∩ S,
        ∀ z ∈ G.neighborFinset w ∩ S, y ≠ z →
          Disjoint
            (G.neighborFinset y ∩ fullLineCenters G S q)
            (G.neighborFinset z ∩ fullLineCenters G S q)) := by
  classical
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, _hcommon, hwOcc⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_halfOccupancy_collision
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hwNotFull : w ∉ fullLineCenters G S q := by
    intro hwFull
    have hwq := (mem_fullLineCenters G S q w).mp hwFull
    rw [hwOcc, hqm] at hwq
    omega
  have hprofile :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  refine ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
    hxw, hx'w, hwOcc, hwNotFull, ?_, ?_⟩
  · intro y hy
    exact (hprofile y).mp (mem_inter.mp hy).2
  intro y hy z hz hyz
  apply c4Free_neighbor_ownerSets_disjoint_of_not_mem
      G hfree (fullLineCenters G S q) hwNotFull hyz
  · exact (G.mem_neighborFinset w y).mp (mem_inter.mp hy).1 |>.symm
  · exact (G.mem_neighborFinset w z).mp (mem_inter.mp hz).1 |>.symm

end

end Erdos85

#print axioms Erdos85.c4Free_neighbor_ownerSets_disjoint_of_not_mem
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
