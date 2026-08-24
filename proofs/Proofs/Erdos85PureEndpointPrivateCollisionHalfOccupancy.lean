import Proofs.Erdos85PureEndpointPrivateCollision
import Proofs.Erdos85PureEndpointCanonicalPrivatePoints

/-!
# The private collision has half occupancy

The common neighbor forced between two private shore points already has two
shore neighbors, so it is not empty.  It cannot be a full center either:
the private-point bijection would identify both points with that center's
unique private point.  The endpoint trichotomy therefore makes it an
ordinary half-occupancy vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A preconnected pure endpoint contains two distinct private points with
a common neighbor of shore occupancy exactly `m=q/2`. -/
theorem c4Free_binarySquare_pureEndpoint_exists_private_halfOccupancy_collision
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
      (G.neighborFinset w ∩ S).card = m := by
  classical
  obtain ⟨x, hxR₁, x', hx'R₁, hxx', w, hxw, hx'w⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_commonNeighbor
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hxData := Finset.mem_filter.mp hxR₁
  have hx'Data := Finset.mem_filter.mp hx'R₁
  have hocc : (G.neighborFinset w ∩ S).card = m := by
    rcases htri w with hzero | hm | hfull
    · have hxMem : x ∈ G.neighborFinset w ∩ S :=
        Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxData.1⟩
      rw [Finset.card_eq_zero.mp hzero] at hxMem
      simp at hxMem
    · exact hm
    · have hwFull : w ∈ fullLineCenters G S q :=
        (mem_fullLineCenters G S q w).mpr hfull
      obtain ⟨p, _hpInj, hp, hpSurj⟩ :=
        c4Free_binarySquare_pureEndpoint_privatePoint_bijection
          G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      obtain ⟨i, hi⟩ := hpSurj x hxData.1 hxData.2
      obtain ⟨j, hj⟩ := hpSurj x' hx'Data.1 hx'Data.2
      have hwOwnerI : w ∈
          G.neighborFinset (p i) ∩ fullLineCenters G S q := by
        apply Finset.mem_inter.mpr
        constructor
        · rw [hi]
          exact (G.mem_neighborFinset x w).mpr hxw
        · exact hwFull
      have hwOwnerJ : w ∈
          G.neighborFinset (p j) ∩ fullLineCenters G S q := by
        apply Finset.mem_inter.mpr
        constructor
        · rw [hj]
          exact (G.mem_neighborFinset x' w).mpr hx'w
        · exact hwFull
      rw [(hp i).2.2] at hwOwnerI
      rw [(hp j).2.2] at hwOwnerJ
      have hwi : w = i.1 := Finset.mem_singleton.mp hwOwnerI
      have hwj : w = j.1 := Finset.mem_singleton.mp hwOwnerJ
      have hij : i = j := Subtype.ext (hwi.symm.trans hwj)
      have : x = x' := by
        calc
          x = p i := hi.symm
          _ = p j := congrArg p hij
          _ = x' := hj
      exact (hxx' this).elim
  exact ⟨x, x', w, hxData.1, hx'Data.1, hxx',
    hxData.2, hx'Data.2, hxw, hx'w, hocc⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_private_halfOccupancy_collision
