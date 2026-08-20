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

end

end Erdos85

#print axioms Erdos85.existsUnique_commonOwner_of_induced_secondOrderDefect_path
