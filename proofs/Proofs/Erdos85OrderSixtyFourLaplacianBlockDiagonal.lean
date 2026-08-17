import Proofs.Erdos85DependentPiDeterminant
import Proofs.Erdos85ComponentLocalObstruction

/-! # Component block diagonalization of the defect Laplacian -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the canonical connected-component enumeration, the degree matrix
is the dependent block diagonal of the induced component degree matrices. -/
theorem reindex_degMatrix_eq_componentBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V]
    [Semiring R] (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] :
    (D.degMatrix R).reindex (vertexConnectedComponentEquiv D)
        (vertexConnectedComponentEquiv D) =
      Matrix.blockDiagonal'
        (fun c : D.ConnectedComponent => (D.induce c.supp).degMatrix R) := by
  ext ⟨c, u⟩ ⟨c', v⟩
  by_cases hcc : c = c'
  · subst c'
    by_cases huv : u = v
    · subst v
      simp [Matrix.reindex_apply, vertexConnectedComponentEquiv,
        Matrix.blockDiagonal'_apply_eq, SimpleGraph.degMatrix,
        degree_induce_connectedComponent_supp]
    · have hval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
      simp [Matrix.reindex_apply, vertexConnectedComponentEquiv,
        Matrix.blockDiagonal'_apply_eq, SimpleGraph.degMatrix, huv, hval]
  · have hval : u.1 ≠ v.1 := by
      intro huv
      apply hcc
      rw [← u.2, ← v.2, huv]
    simp [Matrix.reindex_apply, vertexConnectedComponentEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hcc,
      SimpleGraph.degMatrix, hval]

/-- The graph Laplacian is a dependent block diagonal matrix over connected
components. -/
theorem reindex_lapMatrix_eq_componentBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] :
    (D.lapMatrix R).reindex (vertexConnectedComponentEquiv D)
        (vertexConnectedComponentEquiv D) =
      Matrix.blockDiagonal'
        (fun c : D.ConnectedComponent => (D.induce c.supp).lapMatrix R) := by
  rw [SimpleGraph.lapMatrix]
  have hreindex :
      ((D.degMatrix R - D.adjMatrix R).reindex
        (vertexConnectedComponentEquiv D)
        (vertexConnectedComponentEquiv D)) =
      (D.degMatrix R).reindex (vertexConnectedComponentEquiv D)
          (vertexConnectedComponentEquiv D) -
        (D.adjMatrix R).reindex (vertexConnectedComponentEquiv D)
          (vertexConnectedComponentEquiv D) := by
    ext
    rfl
  rw [hreindex, reindex_degMatrix_eq_componentBlockDiagonal,
    reindex_adjMatrix_eq_componentBlockDiagonal,
    ← Matrix.blockDiagonal'_sub]
  rfl

end

end Erdos85
