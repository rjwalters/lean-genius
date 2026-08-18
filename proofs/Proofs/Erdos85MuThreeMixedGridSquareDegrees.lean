import Proofs.Erdos85MuThreeMixedGridSquarePartition
import Proofs.Erdos85ConflictRegular

/-!
# Degrees in the mixed-grid square partition

The common-neighbour graph is the standard conflict graph of the exterior.
Its degree is therefore `6 * 5 = 30`.  The rook and residual degree counts
complete the intrinsic `30 + 10 + 7 = 47` partition.
-/

open SimpleGraph

namespace Erdos85

/-- Under C4-freeness, "has a common neighbour" is equivalent to "has
exactly one common neighbour". -/
theorem MuThreeMixedGridCode.commonNeighborGraph_eq_conflict
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    mixedGridCommonNeighborGraph K C = commonNeighborConflict C := by
  ext u v
  simp only [mixedGridCommonNeighborGraph, commonNeighborConflict_adj_iff]
  constructor
  · rintro ⟨hne, hone⟩
    exact ⟨hne, Finset.card_pos.mp (by omega)⟩
  · rintro ⟨hne, hnonempty⟩
    refine ⟨hne, ?_⟩
    have hpos : 0 < (C.neighborFinset u ∩ C.neighborFinset v).card :=
      Finset.card_pos.mpr hnonempty
    have hle := MuThreeMixedGridCode.common_neighbor_card_le_one
      H K C code u v hne
    omega

/-- The common-neighbour relation in every mixed grid code is 30-regular. -/
theorem MuThreeMixedGridCode.commonNeighborGraph_degree_eq_thirty
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    (mixedGridCommonNeighborGraph K C).degree u = 30 := by
  rw [← (mixedGridCommonNeighborGraph K C).card_neighborFinset_eq_degree]
  have hgraph := MuThreeMixedGridCode.commonNeighborGraph_eq_conflict H K C code
  have hfinset : (mixedGridCommonNeighborGraph K C).neighborFinset u =
      (commonNeighborConflict C).neighborFinset u := by
    ext v
    simp only [mem_neighborFinset]
    exact iff_of_eq (congrArg (fun G : SimpleGraph (muThreeMixedCell K) =>
      G.Adj u v) hgraph)
  rw [hfinset, (commonNeighborConflict C).card_neighborFinset_eq_degree]
  have hdegree := degree_commonNeighborConflict_of_regular_c4Free
    C code.c4Free (fun v => MuThreeMixedGridCode.degree_eq_six H K C code v) u
  norm_num at hdegree ⊢
  exact hdegree

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborGraph_eq_conflict
#print axioms Erdos85.MuThreeMixedGridCode.commonNeighborGraph_degree_eq_thirty
