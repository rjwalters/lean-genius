import Proofs.Erdos85BinarySquareSizeTwoPairedOwnerComponentEquiv

/-! # Resolution of component incidence Grams into cross blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Splitting the ambient row coordinate into defect components resolves a
component-incidence Gram product into the sum of its cross-block products. -/
theorem sum_transpose_crossIncidence_mul_crossIncidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d e) =
      (defectComponentNeighborIncidenceMatrix (K := ℤ) G c).transpose *
        defectComponentNeighborIncidenceMatrix (K := ℤ) G e := by
  classical
  ext x z
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
  let f : (Σ d : (secondOrderDefectGraph G).ConnectedComponent, d.supp) → ℤ :=
    fun y => defectComponentCrossIncidenceMatrix (K := ℤ) G y.1 c y.2 x *
      defectComponentCrossIncidenceMatrix (K := ℤ) G y.1 e y.2 z
  let E := vertexConnectedComponentEquiv (secondOrderDefectGraph G)
  change (∑ d, ∑ y, f ⟨d, y⟩) = _
  calc
    (∑ d, ∑ y, f ⟨d, y⟩) = ∑ y, f y := (Fintype.sum_sigma f).symm
    _ = ∑ y : V, f (E y) := (E.sum_comp f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _hy
      simp [f, E, defectComponentCrossIncidenceMatrix,
        defectComponentNeighborIncidenceMatrix, vertexConnectedComponentEquiv]

/-- For distinct endpoint components, the cross-block products through all
intermediate defect components resolve the all-ones matrix. -/
theorem sum_transpose_crossIncidence_mul_crossIncidence_eq_ones
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e) :
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d e) =
      Matrix.of fun _ _ => (1 : ℤ) := by
  rw [sum_transpose_crossIncidence_mul_crossIncidence]
  exact transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree c e hce

end

end Erdos85
