import Proofs.Erdos85C4FreeSubsetCherryBound
import Proofs.Erdos85MuNegThreeZeroFiveGraphProfileLedger

/-! # C4-free cherry bounds for the h305 shore-type populations -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem serviceNeighborShoreTypeCount_eq_neighbor_inter_type
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

/-- There are twelve type-two exterior edges, so C4-freeness bounds the
total number of unordered pairs of type-two service neighbors by `66`. -/
theorem h305_typeTwo_serviceNeighbor_cherry_sum_le_sixtySix
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
      (serviceNeighborShoreTypeCount R Cedge a U 2).choose 2) ≤ 66 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let E2 := shoreTypeEdgeFinset R U 2
  have hbound :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      Cedge hfree E2
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hE2 : E2.card = 12 := by simpa [E2, U] using hpop.1
  rw [hE2] at hbound
  norm_num [Nat.choose] at hbound
  change (∑ a : R.edgeFinset,
    (serviceNeighborShoreTypeCount R Cedge a U 2).choose 2) ≤ 66
  simpa [E2, serviceNeighborShoreTypeCount_eq_neighbor_inter_type,
    hE2] using hbound

/-- Symmetric cherry bound for the twelve type-zero exterior edges. -/
theorem h305_typeZero_serviceNeighbor_cherry_sum_le_sixtySix
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
      (serviceNeighborShoreTypeCount R Cedge a U 0).choose 2) ≤ 66 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let E0 := shoreTypeEdgeFinset R U 0
  have hbound :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      Cedge hfree E0
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hE0 : E0.card = 12 := by simpa [E0, U] using hpop.2.2
  rw [hE0] at hbound
  norm_num [Nat.choose] at hbound
  change (∑ a : R.edgeFinset,
    (serviceNeighborShoreTypeCount R Cedge a U 0).choose 2) ≤ 66
  simpa [E0, serviceNeighborShoreTypeCount_eq_neighbor_inter_type,
    hE0] using hbound

end

end Erdos85

#print axioms Erdos85.h305_typeTwo_serviceNeighbor_cherry_sum_le_sixtySix
#print axioms Erdos85.h305_typeZero_serviceNeighbor_cherry_sum_le_sixtySix
