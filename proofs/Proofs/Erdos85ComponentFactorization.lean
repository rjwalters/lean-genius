import Proofs.Erdos85CycleGraphIso
import Proofs.RationalCanonicalFormExists

namespace Erdos85

open SimpleGraph

/-- Every vertex is uniquely a vertex of its connected component. -/
noncomputable def vertexConnectedComponentEquiv
    {V : Type*} (D : SimpleGraph V) :
    V ≃ Σ c : D.ConnectedComponent, c.supp where
  toFun v := ⟨D.connectedComponentMk v, ⟨v, rfl⟩⟩
  invFun z := z.2.1
  left_inv _ := rfl
  right_inv z := by
    rcases z with ⟨c, v, hv⟩
    change D.connectedComponentMk v = c at hv
    subst c
    rfl

/-- Under the canonical component enumeration, an adjacency matrix is a
dependent block diagonal matrix of the induced component adjacency matrices. -/
theorem reindex_adjMatrix_eq_componentBlockDiagonal
    {V R : Type*} [Fintype V] [DecidableEq V]
    [Semiring R] (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] :
    (D.adjMatrix R).reindex (vertexConnectedComponentEquiv D)
        (vertexConnectedComponentEquiv D) =
      Matrix.blockDiagonal'
        (fun c : D.ConnectedComponent => (D.induce c.supp).adjMatrix R) := by
  ext ⟨c, u⟩ ⟨c', v⟩
  by_cases hcc : c = c'
  · subst c'
    simp [Matrix.reindex_apply, vertexConnectedComponentEquiv,
      Matrix.blockDiagonal'_apply_eq, SimpleGraph.adjMatrix_apply]
  · have hnadj : ¬ D.Adj u.1 v.1 := by
      intro huv
      apply hcc
      rw [← u.2, ← v.2]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj huv
    simp [Matrix.reindex_apply, vertexConnectedComponentEquiv,
      Matrix.blockDiagonal'_apply_ne _ _ _ hcc, SimpleGraph.adjMatrix_apply,
      hcc, hnadj]

/-- The determinant of a scalar resolvent factors over connected components. -/
theorem det_resolvent_eq_prod_connectedComponents
    {V R : Type*} [Fintype V] [DecidableEq V]
    [CommRing R] (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (a : R) :
    (Matrix.scalar V a - D.adjMatrix R).det =
      ∏ c : D.ConnectedComponent,
        (Matrix.scalar c.supp a - (D.induce c.supp).adjMatrix R).det := by
  let e := vertexConnectedComponentEquiv D
  rw [← Matrix.det_reindex_self e]
  have hscalar : (Matrix.scalar V a).reindex e e =
      Matrix.blockDiagonal' (fun c : D.ConnectedComponent => Matrix.scalar c.supp a) := by
    ext ⟨c, u⟩ ⟨c', v⟩
    by_cases hcc : c = c'
    · subst c'
      by_cases huv : u = v
      · subst v
        simp [Matrix.reindex_apply, e, vertexConnectedComponentEquiv,
          Matrix.blockDiagonal'_apply_eq, Matrix.scalar_apply]
      · have hval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
        simp [Matrix.reindex_apply, e, vertexConnectedComponentEquiv,
          Matrix.blockDiagonal'_apply_eq, Matrix.scalar_apply, huv, hval]
    · have hval : u.1 ≠ v.1 := by
        intro huv
        apply hcc
        rw [← u.2, ← v.2, huv]
      simp [Matrix.reindex_apply, e, vertexConnectedComponentEquiv,
        Matrix.blockDiagonal'_apply_ne _ _ _ hcc, Matrix.scalar_apply, hcc, hval]
  have hreindex : ((Matrix.scalar V a - D.adjMatrix R).reindex e e) =
      (Matrix.scalar V a).reindex e e - (D.adjMatrix R).reindex e e := by
    ext
    rfl
  rw [hreindex, hscalar, reindex_adjMatrix_eq_componentBlockDiagonal]
  rw [← Matrix.blockDiagonal'_sub]
  exact RationalCanonicalFormExists.RCF.det_blockDiagonal' _

end Erdos85
