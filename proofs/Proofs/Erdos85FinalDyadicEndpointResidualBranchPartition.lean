import Proofs.Erdos85FinalDyadicEndpointResidualDefectProfile
import Proofs.Erdos85C4FreeNeighborBlockPartition

/-!
# Residual branch partition at the endpoint

Around a residual vertex `w`, the graph-neighbor rows partition the
non-defect portion of the punctured residual cell.  There are `q` pairwise
disjoint rows and each has size exactly `r-1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The `q` graph-neighbor branches at a residual vertex form disjoint
`(r-1)`-sets whose union is the residual defect complement. -/
theorem finalDyadic_endpoint_residual_neighborBranch_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {w : V}
    (hw : w ∈ (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)) :
    let W := (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)
    let F := fun z => G.neighborFinset z ∩ W.erase w
    (∀ z ∈ G.neighborFinset w, (F z).card = r - 1) ∧
    (∀ z ∈ G.neighborFinset w, ∀ z' ∈ G.neighborFinset w,
      z ≠ z' → Disjoint (F z) (F z')) ∧
    (G.neighborFinset w).biUnion F =
      W.erase w \ (secondOrderDefectGraph G).neighborFinset w := by
  dsimp only
  let M := finalDyadicNegativeHighCutCenters G S j r
  let W := (Finset.univ : Finset V) \ (S ∪ M)
  let F := fun z => G.neighborFinset z ∩ W.erase w
  have hwW : w ∈ W := hw
  have hrows : ∀ z ∈ G.neighborFinset w, (F z).card = r - 1 := by
    intro z hz
    have hzNotSupport : z ∉ exceptionalSignedSupport G S q := by
      have hzH :=
        finalDyadic_endpoint_residual_neighborFinset_subset_nonexceptional
          G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
            hsupport hemptyClique hw hz
      exact (Finset.mem_sdiff.mp hzH).2
    have hzResidual :=
      (finalDyadic_endpoint_nonexceptional_residual_degree_profile
        G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
          hsupport hemptyClique hzNotSupport).2.2
    have hwNz : w ∈ G.neighborFinset z :=
      (G.mem_neighborFinset z w).mpr
        ((G.mem_neighborFinset w z).mp hz).symm
    have hwRes : w ∈ G.neighborFinset z \ (S ∪ M) :=
      Finset.mem_sdiff.mpr ⟨hwNz, (Finset.mem_sdiff.mp hwW).2⟩
    have hset : F z =
        (G.neighborFinset z \ (S ∪ M)).erase w := by
      ext x
      simp [F, W, and_left_comm, and_assoc]
    rw [hset, Finset.card_erase_of_mem hwRes, hzResidual]
  have hpart := c4Free_neighbor_blocks_partition_common_targets
    G hfree w (W.erase w) (by simp)
  dsimp only at hpart
  have hdefect := c4Free_neighbor_blocks_partition_defect_complement
    G hfree w (W.erase w) (by simp)
  dsimp only at hdefect
  exact ⟨hrows, hpart.1, hdefect⟩

end

end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_residual_neighborBranch_partition
