import Proofs.Erdos85RestrictedOwnerResolution

/-! # Cubic expansion of the local owner resolution -/

namespace Erdos85

noncomputable section

/-- The trace of the cube of a finite matrix sum is the sum of all ordered
mixed cubic traces.  Keeping the indices ordered is the convenient interface
for subsequently separating monochromatic, two-color, and rainbow owner
patterns. -/
theorem trace_finsetSum_cube_eq_sum_ordered_traces
    {I V R : Type*} [Fintype I] [Fintype V] [CommRing R]
    (A : I → Matrix V V R) :
    Matrix.trace ((∑ i, A i) * (∑ i, A i) * (∑ i, A i)) =
      ∑ k, ∑ j, ∑ i, Matrix.trace (A i * A j * A k) := by
  calc
    Matrix.trace ((∑ i, A i) * (∑ i, A i) * (∑ i, A i)) =
        Matrix.trace (∑ k, ∑ j, ∑ i, A i * A j * A k) := by
          congr 1
          simp_rw [Finset.mul_sum]
          simp_rw [Finset.sum_mul]
    _ = ∑ k, ∑ j, ∑ i, Matrix.trace (A i * A j * A k) := by
      simp only [Matrix.trace_sum]

/-- Local owner-color specialization on one defect component. -/
theorem trace_inducedDefect_compl_cube_eq_sum_restrictedOwner_ordered_traces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source : (secondOrderDefectGraph G).ConnectedComponent) :
    let A := fun owner : (secondOrderDefectGraph G).ConnectedComponent =>
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ
    Matrix.trace
        (((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ) *
          ((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ) *
          ((((secondOrderDefectGraph G).induce source.supp)ᶜ).adjMatrix ℤ)) =
      ∑ k, ∑ j, ∑ i, Matrix.trace (A i * A j * A k) := by
  dsimp
  rw [← sum_restrictedComponentOwnerGraph_adjMatrix_eq_inducedDefect_compl
    G hfree source]
  exact trace_finsetSum_cube_eq_sum_ordered_traces _

end

end Erdos85
