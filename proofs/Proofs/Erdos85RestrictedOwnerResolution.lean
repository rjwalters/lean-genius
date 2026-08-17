import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization

/-! # Local owner resolution on one defect component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restricting the global owner resolution to one defect component gives
an exact local edge-color decomposition: the restricted owner adjacency
matrices sum to the adjacency matrix of the complement of the induced defect
graph.  Unlike the global centered-owner cubic identity, this equality lives
entirely on the source component and is therefore suitable for a local
triangle-pattern expansion. -/
theorem sum_restrictedComponentOwnerGraph_adjMatrix_eq_inducedDefect_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ owner : (secondOrderDefectGraph G).ConnectedComponent,
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ) =
        (((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ := by
  ext x y
  simp only [Matrix.sum_apply]
  have hleft :
      (∑ owner : (secondOrderDefectGraph G).ConnectedComponent,
        (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ x y) =
      ∑ owner : (secondOrderDefectGraph G).ConnectedComponent,
        (componentOwnerGraph G (secondOrderDefectGraph G) owner).adjMatrix ℤ
          x.1 y.1 := by
    apply Finset.sum_congr rfl
    intro owner _howner
    rfl
  have hglobal := congrArg
    (fun M : Matrix V V ℤ => M x.1 y.1)
    (sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect
      G hfree)
  simp only [Matrix.sum_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.one_apply] at hglobal
  rw [hleft, hglobal]
  by_cases hxy : x = y
  · subst y
    simp [SimpleGraph.adjMatrix_apply]
  · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    by_cases hD : (secondOrderDefectGraph G).Adj x.1 y.1 <;>
      simp [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
        hxy, hval, hD]

end

end Erdos85
