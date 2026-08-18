import Proofs.Erdos85BinarySquareRegularParity

/-! # The unique owner graph in the connected-defect stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- When the second-order defect graph is connected, its unique component
owner graph is exactly the simple-graph complement of the defect graph.  This
turns the `[8]` owner-density terminal into a direct defect/operator identity. -/
theorem componentOwnerGraph_eq_compl_secondOrderDefect_of_oneComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (a : (secondOrderDefectGraph G).ConnectedComponent) :
    componentOwnerGraph G (secondOrderDefectGraph G) a =
      (secondOrderDefectGraph G)ᶜ := by
  classical
  haveI hsub : Subsingleton
      (secondOrderDefectGraph G).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [SimpleGraph.compl_adj]
    rw [and_iff_right hxy]
    constructor
    · intro howner hdefect
      have hunique :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hxy).mpr
          ⟨a, howner, fun c _ => Subsingleton.elim c a⟩
      exact hunique hdefect
    · intro hnot
      obtain ⟨c, hc, _⟩ :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hxy).mp hnot
      simpa [Subsingleton.elim c a] using hc

end

end Erdos85

#print axioms Erdos85.componentOwnerGraph_eq_compl_secondOrderDefect_of_oneComponent
