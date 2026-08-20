import Proofs.Erdos85C4FreeRectangularTwoWalkBound
import Proofs.Erdos85MuNegThreeZeroFiveGraphProfileLedger

/-! # Cross-shore-type two-walk bound for h305 service -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem serviceTypeCount_eq_neighbor_inter_type
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) (t : ℕ) :
    serviceNeighborShoreTypeCount R Cedge a S t =
      (Cedge.neighborFinset a ∩ shoreTypeEdgeFinset R S t).card := by
  classical
  unfold serviceNeighborShoreTypeCount shoreTypeEdgeFinset
  congr 1
  ext b
  simp [and_comm]

/-- The twelve type-two and twelve type-zero edge populations are disjoint;
C4-freeness therefore bounds their rectangular common-neighbor moment by
`12·12=144`. -/
theorem h305_typeTwo_typeZero_serviceNeighbor_product_sum_le_144
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hRreg : ∀ x, R.degree x = 6) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ a : R.edgeFinset,
      serviceNeighborShoreTypeCount R Cedge a U 2 *
        serviceNeighborShoreTypeCount R Cedge a U 0) ≤ 144 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let E2 := shoreTypeEdgeFinset R U 2
  let E0 := shoreTypeEdgeFinset R U 0
  have hE : Disjoint E2 E0 := by
    rw [Finset.disjoint_left]
    intro a ha2 ha0
    simp only [E2, E0, shoreTypeEdgeFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at ha2 ha0
    omega
  have hbound :=
    sum_neighbor_inter_card_mul_le_card_mul_card_of_not_containsC4
      Cedge hfree E2 E0 hE
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hE2 : E2.card = 12 := by simpa [E2, U] using hpop.1
  have hE0 : E0.card = 12 := by simpa [E0, U] using hpop.2.2
  rw [hE2, hE0] at hbound
  norm_num at hbound
  change (∑ a : R.edgeFinset,
    serviceNeighborShoreTypeCount R Cedge a U 2 *
      serviceNeighborShoreTypeCount R Cedge a U 0) ≤ 144
  simpa [E2, E0, serviceTypeCount_eq_neighbor_inter_type] using hbound

end

end Erdos85

#print axioms
  Erdos85.h305_typeTwo_typeZero_serviceNeighbor_product_sum_le_144
