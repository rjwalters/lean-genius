import Proofs.Erdos85C4FreeNeighborBlockPartition
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Row covers for the q=9 three-high second profile

This module applies the generic C4-free neighbor-block partition without
adding further material to the large bin-zero classification module.  Every
ordinary bin-zero row partitions the unmarked 24-point bin-one core outside
its defect neighborhood.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- For every bin-zero vertex, its neighbor rows cover the unmarked bin-one
core with no overlap.  Numerically, the total row mass is `24` minus its
number of unmarked bin-one defect neighbors. -/
theorem squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {x t : V} (hx : x ∈ squareOrderNineLowIncidenceBin G 3)
    (ht : t ∈ squareOrderNineLowIncidenceBin G 0) :
    let B := squareOrderNineLowIncidenceBin G
    let M := G.neighborFinset x ∩ B 1
    let U1 := B 1 \ M
    let D := secondOrderDefectGraph G
    (∑ w ∈ G.neighborFinset t,
      (G.neighborFinset w ∩ U1).card) =
        24 - (D.neighborFinset t ∩ U1).card := by
  classical
  dsimp only
  let B := squareOrderNineLowIncidenceBin G
  let M := G.neighborFinset x ∩ B 1
  let U1 := B 1 \ M
  let D := secondOrderDefectGraph G
  have hmarked :=
    squareOrderNine_threeHigh_secondProfile_marked_core_cardinalities
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  dsimp only at hmarked
  have hMcard :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_binOne_neighbors
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 hx
  have hMsub : M ⊆ B 1 := Finset.inter_subset_right
  have hU1card : U1.card = 24 := by
    rw [Finset.card_sdiff_of_subset hMsub, hmarked.1, hMcard]
  have htNotU1 : t ∉ U1 := by
    intro htU1
    have htB1 := (Finset.mem_sdiff.mp htU1).1
    have hkt0 := (Finset.mem_filter.mp ht).2
    have hkt1 := (Finset.mem_filter.mp htB1).2
    omega
  have hcover := c4Free_sum_neighbor_block_cards_eq_defect_complement
    G hfree t U1 htNotU1
  dsimp only at hcover
  rw [hcover, Finset.card_sdiff, hU1card]

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binZero_unmarked_row_cover
