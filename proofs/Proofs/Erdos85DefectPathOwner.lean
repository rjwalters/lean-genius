import Proofs.Erdos85SquareOrderDefectNeighborhoodDesign

/-! # Original-graph owners of induced defect paths

This is the cycle-facing form of the square-order exactness law.  An induced
two-step path in the second-order defect graph has a unique original-graph
owner for its endpoints.  The owner is the middle vertex precisely when both
defect-path edges are also original edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The endpoints of an induced defect two-path have a unique common neighbor
in the original graph.  Its equality with the middle vertex records exactly
whether both path edges belong to the original graph. -/
theorem existsUnique_commonOwner_of_induced_secondOrderDefect_path
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z : V}
    (_hDxy : (secondOrderDefectGraph G).Adj x y)
    (_hDyz : (secondOrderDefectGraph G).Adj y z)
    (hxz : x ≠ z)
    (hnotDxz : ¬ (secondOrderDefectGraph G).Adj x z) :
    ∃ w : V,
      (G.Adj w x ∧ G.Adj w z) ∧
      (∀ w' : V, G.Adj w' x → G.Adj w' z → w' = w) ∧
      (w = y ↔ G.Adj x y ∧ G.Adj y z) := by
  obtain ⟨w, hw, huniq⟩ :=
    existsUnique_squareOrderDefectOwner_of_not_adj G hfree hxz hnotDxz
  have hwx : G.Adj w x := by
    simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hw.1
  have hwz : G.Adj w z := by
    simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hw.2
  refine ⟨w, ⟨hwx, hwz⟩, ?_, ?_⟩
  · intro w' hw'x hw'z
    apply huniq w'
    constructor
    · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hw'x
    · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hw'z
  · constructor
    · intro hwy
      subst w
      exact ⟨hwx.symm, hwz⟩
    · rintro ⟨hxy, hyz⟩
      apply (huniq y ?_).symm
      constructor
      · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset,
          G.adj_comm] using hxy
      · simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hyz

/-- Consecutive induced two-paths have distinct original-graph owners.  If
the owners coincided, the first vertices of the two paths would be a defect
edge lying inside one original neighborhood, which is impossible. -/
theorem exists_distinct_commonOwners_of_consecutive_induced_secondOrderDefect_paths
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z t : V}
    (hDxy : (secondOrderDefectGraph G).Adj x y)
    (hDyz : (secondOrderDefectGraph G).Adj y z)
    (hDzt : (secondOrderDefectGraph G).Adj z t)
    (hxz : x ≠ z) (hyt : y ≠ t)
    (hnotDxz : ¬ (secondOrderDefectGraph G).Adj x z)
    (hnotDyt : ¬ (secondOrderDefectGraph G).Adj y t) :
    ∃ w₁ w₂ : V,
      G.Adj w₁ x ∧ G.Adj w₁ z ∧
      G.Adj w₂ y ∧ G.Adj w₂ t ∧ w₁ ≠ w₂ ∧
      (w₁ = y ↔ G.Adj x y ∧ G.Adj y z) ∧
      (w₂ = z ↔ G.Adj y z ∧ G.Adj z t) := by
  obtain ⟨w₁, hw₁, _, hw₁mid⟩ :=
    existsUnique_commonOwner_of_induced_secondOrderDefect_path
      G hfree hDxy hDyz hxz hnotDxz
  obtain ⟨w₂, hw₂, _, hw₂mid⟩ :=
    existsUnique_commonOwner_of_induced_secondOrderDefect_path
      G hfree hDyz hDzt hyt hnotDyt
  have hwne : w₁ ≠ w₂ := by
    intro heq
    have hxmem : x ∈ squareOrderDefectOwnerBlock G w₁ := by
      simpa [squareOrderDefectOwnerBlock, SimpleGraph.mem_neighborFinset] using hw₁.1
    have hymem : y ∈ squareOrderDefectOwnerBlock G w₁ := by
      simpa [heq, squareOrderDefectOwnerBlock,
        SimpleGraph.mem_neighborFinset] using hw₂.1
    exact (not_defectAdj_of_mem_squareOrderDefectOwnerBlock
      G hfree hxmem hymem hDxy.ne) hDxy
  exact ⟨w₁, w₂, hw₁.1, hw₁.2, hw₂.1, hw₂.2, hwne, hw₁mid, hw₂mid⟩

/-- If the endpoints of an induced defect two-path already share an external
original neighbor `r`, then the two defect-path edges cannot both be original
edges unless the middle vertex is `r`.  This is the local obstruction used
when the endpoint colors of a three-colored defect cycle agree. -/
theorem not_both_originalEdges_of_induced_secondOrderDefect_path_of_commonOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z r : V}
    (hDxy : (secondOrderDefectGraph G).Adj x y)
    (hDyz : (secondOrderDefectGraph G).Adj y z)
    (hxz : x ≠ z)
    (hnotDxz : ¬ (secondOrderDefectGraph G).Adj x z)
    (hrx : G.Adj r x) (hrz : G.Adj r z) (hyr : y ≠ r) :
    ¬ (G.Adj x y ∧ G.Adj y z) := by
  obtain ⟨w, _, huniq, hmid⟩ :=
    existsUnique_commonOwner_of_induced_secondOrderDefect_path
      G hfree hDxy hDyz hxz hnotDxz
  have hrw : r = w := huniq r hrx hrz
  intro hedges
  have hwy : w = y := hmid.mpr hedges
  exact hyr (hrw.trans hwy).symm

end

end Erdos85

#print axioms Erdos85.existsUnique_commonOwner_of_induced_secondOrderDefect_path
#print axioms Erdos85.exists_distinct_commonOwners_of_consecutive_induced_secondOrderDefect_paths
#print axioms Erdos85.not_both_originalEdges_of_induced_secondOrderDefect_path_of_commonOwner
