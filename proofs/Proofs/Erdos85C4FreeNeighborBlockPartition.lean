import Proofs.Erdos85GadgetExtension
import Proofs.Erdos85ExteriorDefectDecomposition

/-! # Neighbor-block partitions in C4-free graphs

For a fixed vertex `x`, every common neighbor of `x` and a target point is
routed through one of the rows indexed by `N(x)`.  In a C4-free graph those
rows are pairwise disjoint away from `x`.  This is the generic combinatorial
API behind the rowwise disjoint-cover constraint in the q=9 B.3 design.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Away from the center `x`, the neighbor blocks indexed by `N(x)` are
pairwise disjoint, and their union is exactly the target points sharing a
common neighbor with `x`. -/
theorem c4Free_neighbor_blocks_partition_common_targets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (x : V) (U : Finset V) (hxU : x ∉ U) :
    let C := G.neighborFinset x
    let F := fun w => G.neighborFinset w ∩ U
    (∀ w ∈ C, ∀ z ∈ C, w ≠ z → Disjoint (F w) (F z)) ∧
      C.biUnion F =
        U.filter fun y => (G.neighborFinset x ∩ G.neighborFinset y).Nonempty := by
  classical
  dsimp only
  let C := G.neighborFinset x
  let F := fun w => G.neighborFinset w ∩ U
  have hdisjoint : ∀ w ∈ C, ∀ z ∈ C, w ≠ z → Disjoint (F w) (F z) := by
    intro w hwC z hzC hwz
    rw [Finset.disjoint_left]
    intro y hyW hyZ
    have hyWParts := Finset.mem_inter.mp hyW
    have hyZParts := Finset.mem_inter.mp hyZ
    have hxCommon : x ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset w x).mpr
          ((G.adj_comm x w).mp ((G.mem_neighborFinset x w).mp hwC)),
        (G.mem_neighborFinset z x).mpr
          ((G.adj_comm x z).mp ((G.mem_neighborFinset x z).mp hzC))⟩
    have hyCommon : y ∈ G.neighborFinset w ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hyWParts.1, hyZParts.1⟩
    have hxy : x ≠ y := fun h => hxU (h ▸ hyWParts.2)
    have hle := (not_containsC4_iff_forall_common_le_one G).mp hfree w z hwz
    exact hxy (Finset.card_le_one.mp hle x hxCommon y hyCommon)
  refine ⟨hdisjoint, ?_⟩
  ext y
  constructor
  · intro hy
    simp only [C, F, Finset.mem_biUnion] at hy
    obtain ⟨w, hwx, hyF⟩ := hy
    have hyParts := Finset.mem_inter.mp hyF
    refine Finset.mem_filter.mpr ⟨hyParts.2, ⟨w, ?_⟩⟩
    exact Finset.mem_inter.mpr ⟨hwx, (G.mem_neighborFinset y w).mpr
      ((G.adj_comm w y).mp ((G.mem_neighborFinset w y).mp hyParts.1))⟩
  · intro hy
    have hyParts := Finset.mem_filter.mp hy
    obtain ⟨w, hwCommon⟩ := hyParts.2
    have hwParts := Finset.mem_inter.mp hwCommon
    simp only [C, F, Finset.mem_biUnion]
    exact ⟨w, hwParts.1, Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset w y).mpr
        ((G.adj_comm y w).mp ((G.mem_neighborFinset y w).mp hwParts.2)),
      hyParts.1⟩⟩

/-- Cardinal form of `c4Free_neighbor_blocks_partition_common_targets`:
the number of covered target points is the sum of the row sizes. -/
theorem c4Free_sum_neighbor_block_cards_eq_common_targets
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (x : V) (U : Finset V) (hxU : x ∉ U) :
    let C := G.neighborFinset x
    let F := fun w => G.neighborFinset w ∩ U
    (∑ w ∈ C, (F w).card) =
      (U.filter fun y =>
        (G.neighborFinset x ∩ G.neighborFinset y).Nonempty).card := by
  classical
  dsimp only
  let C := G.neighborFinset x
  let F := fun w => G.neighborFinset w ∩ U
  have hpart := c4Free_neighbor_blocks_partition_common_targets
    G hfree x U hxU
  dsimp only at hpart
  rw [← hpart.2, Finset.card_biUnion hpart.1]

/-- Defect-complement form: in a C4-free graph the disjoint neighbor blocks
cover exactly the target points outside the second-order defect neighborhood
of the center. -/
theorem c4Free_neighbor_blocks_partition_defect_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (x : V) (U : Finset V) (hxU : x ∉ U) :
    let C := G.neighborFinset x
    let F := fun w => G.neighborFinset w ∩ U
    C.biUnion F = U \ (secondOrderDefectGraph G).neighborFinset x := by
  classical
  dsimp only
  let C := G.neighborFinset x
  let F := fun w => G.neighborFinset w ∩ U
  have hpart := c4Free_neighbor_blocks_partition_common_targets
    G hfree x U hxU
  dsimp only at hpart
  rw [hpart.2]
  ext y
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨hyU, hyCommon⟩
    refine ⟨hyU, ?_⟩
    intro hyD
    have hxy : x ≠ y := fun h => hxU (h ▸ hyU)
    have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxy).mp
        (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hyD)
    have hempty := Finset.card_eq_zero.mp hzero
    simpa [hempty] using hyCommon
  · rintro ⟨hyU, hyNotD⟩
    refine ⟨hyU, ?_⟩
    rw [← Finset.card_pos]
    by_contra hnotPos
    have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by omega
    have hxy : x ≠ y := fun h => hxU (h ▸ hyU)
    have hD := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxy).mpr hzero
    exact hyNotD (((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hD)

/-- Cardinal defect-complement form of the row partition. -/
theorem c4Free_sum_neighbor_block_cards_eq_defect_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (x : V) (U : Finset V) (hxU : x ∉ U) :
    let C := G.neighborFinset x
    let F := fun w => G.neighborFinset w ∩ U
    (∑ w ∈ C, (F w).card) =
      (U \ (secondOrderDefectGraph G).neighborFinset x).card := by
  classical
  dsimp only
  let C := G.neighborFinset x
  let F := fun w => G.neighborFinset w ∩ U
  have hpart := c4Free_neighbor_blocks_partition_common_targets
    G hfree x U hxU
  dsimp only at hpart
  rw [← c4Free_neighbor_blocks_partition_defect_complement
      G hfree x U hxU,
    Finset.card_biUnion hpart.1]

end

end Erdos85

#print axioms Erdos85.c4Free_neighbor_blocks_partition_common_targets
#print axioms Erdos85.c4Free_sum_neighbor_block_cards_eq_common_targets
#print axioms Erdos85.c4Free_neighbor_blocks_partition_defect_complement
#print axioms Erdos85.c4Free_sum_neighbor_block_cards_eq_defect_complement
