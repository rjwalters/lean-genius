import Proofs.Erdos85PureEndpointUniversalPrivateDefectConservation

/-!
# The exterior near-parallel design

At the pure endpoint every vertex outside the full-center family has half
occupancy.  Thus the local conservation/partition law holds simultaneously
on every exterior row.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every exterior vertex has half occupancy, exact private/defect incidence
conservation, and a near-parallel owner partition of the full centers. -/
theorem c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
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
    let F := fullLineCenters G S q
    let owner := fun y => G.neighborFinset y ∩ F
    let R₁ := S.filter fun y => (owner y).card = 1
    ∀ w ∉ F,
      let B := G.neighborFinset w ∩ S
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      B.card = m ∧
      K.card = (G.neighborFinset w ∩ R₁).card ∧
      (((B : Finset V) : Set V).PairwiseDisjoint owner) ∧
      B.biUnion owner = F \ K := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  intro w hwNotFull
  have hwHalf : (G.neighborFinset w ∩ S).card = m := by
    rcases htri w with hzero | hm | hfull
    · have hwEmpty : w ∈ emptyLineCenters G S :=
        (mem_emptyLineCenters G S w).mpr hzero
      rw [hempty] at hwEmpty
      simp at hwEmpty
    · exact hm
    · exact (hwNotFull ((mem_fullLineCenters G S q w).mpr hfull)).elim
  have hcons :=
    c4Free_binarySquare_pureEndpoint_halfOccupancy_privateDefect_conservation
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      w hwNotFull hwHalf
  refine ⟨hwHalf, ?_, ?_, ?_⟩
  · simpa [F, owner, R₁] using hcons.1
  · simpa [F, owner] using hcons.2.1
  · simpa [F, owner] using hcons.2.2

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
