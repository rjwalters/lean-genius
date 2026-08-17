import Proofs.Erdos85OrderSixtyFourLaplacianBlockDiagonal

/-! # Product formula for the residual defect Laplacian -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Every graph Laplacian has coordinate sum zero on every output vector. -/
theorem coordinateSumLinearMap_lapMatrix_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V → ℚ) :
    coordinateSumLinearMap V ((H.lapMatrix ℚ).mulVec v) = 0 := by
  change (∑ x, ∑ y, H.lapMatrix ℚ x y * v y) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro y _
  calc
    (∑ x, H.lapMatrix ℚ x y * v y) =
        (∑ x, H.lapMatrix ℚ x y) * v y := by
      rw [Finset.sum_mul]
    _ = 0 * v y := by
      congr 1
      calc
        (∑ x, H.lapMatrix ℚ x y) =
            ∑ x, H.lapMatrix ℚ y x := by
          apply Finset.sum_congr rfl
          intro x _
          exact (H.isSymm_lapMatrix ℚ).apply x y |>.symm
        _ = 0 := by
          have hz := congrFun
            (H.lapMatrix_mulVec_const_eq_zero (R := ℚ)) y
          simpa [Matrix.mulVec, dotProduct] using hz
    _ = 0 := zero_mul _

/-- The induced-component Laplacian preserves its mean-zero sector. -/
theorem componentLaplacian_maps_meanZero
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) [Fintype c.supp] :
    ∀ v ∈ LinearMap.ker (coordinateSumLinearMap c.supp),
      ((D.induce c.supp).lapMatrix ℚ).toLin' v ∈
        LinearMap.ker (coordinateSumLinearMap c.supp) := by
  intro v _hv
  apply LinearMap.mem_ker.mpr
  exact coordinateSumLinearMap_lapMatrix_mulVec_eq_zero
    (D.induce c.supp) v

/-- The residual Laplacian endomorphism of one connected component. -/
def componentResidualLaplacian
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) [Fintype c.supp] :
    LinearMap.ker (coordinateSumLinearMap c.supp) →ₗ[ℚ]
      LinearMap.ker (coordinateSumLinearMap c.supp) :=
  ((D.induce c.supp).lapMatrix ℚ).toLin'.restrict
    (componentLaplacian_maps_meanZero D c)

/-- Pointwise action of a simultaneously reindexed square matrix. -/
theorem reindex_mulVec_comp_symm_apply
    {V W : Type*} [Fintype V] [Fintype W]
    (M : Matrix V V ℚ) (e : V ≃ W) (v : V → ℚ) (z : W) :
    (M.reindex e e).mulVec (fun w => v (e.symm w)) z =
      M.mulVec v (e.symm z) := by
  let w : W → ℚ := fun x => v (e.symm x)
  have hs := Matrix.submatrix_mulVec_equiv M w e.symm e.symm
  have hs' := congrFun hs z
  have hw : w ∘ e.symm.symm = v := by
    funext x
    exact congrArg v (e.symm.apply_symm_apply x)
  rw [hw] at hs'
  simpa [w, Matrix.reindex_apply] using hs'

/-- Pointwise action of a dependent block diagonal matrix. -/
theorem dependentBlockDiagonal_mulVec_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : ι → Type*} [∀ i, Fintype (T i)]
    (M : ∀ i, Matrix (T i) (T i) ℚ)
    (v : (Σ i, T i) → ℚ) (c : ι) (x : T c) :
    (Matrix.blockDiagonal' M).mulVec v (Sigma.mk c x) =
      (M c).mulVec (fun y => v (Sigma.mk c y)) x := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro z _
    rw [Matrix.blockDiagonal'_apply_eq]
  · intro c' _ hc'
    apply Finset.sum_eq_zero
    intro z _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc'.symm]
    exact zero_mul _
  · simp

/-- The instance-stable form of a seven-regular graph Laplacian. -/
def sevenRegularLaplacianMatrix
    {V : Type*} [Fintype V] [DecidableEq V] (D : SimpleGraph V)
    [DecidableRel D.Adj] : Matrix V V ℚ :=
  Matrix.scalar V 7 - D.adjMatrix ℚ

/-- For a seven-regular graph, `7I-A` is its graph Laplacian. -/
theorem sevenRegularLaplacianMatrix_eq_lapMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x, D.degree x = 7) :
    sevenRegularLaplacianMatrix D = D.lapMatrix ℚ := by
  ext x y
  simp only [sevenRegularLaplacianMatrix, Matrix.scalar_apply,
    SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.sub_apply,
    Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst y
    simp [hreg x, SimpleGraph.adjMatrix_apply]
  · simp [hxy]

/-- The stable seven-regular Laplacian form block diagonalizes over connected
components without depending on how their finite support instances were
chosen. -/
theorem reindex_sevenRegularLaplacianMatrix_eq_componentBlockDiagonal
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent] :
    (sevenRegularLaplacianMatrix D).reindex
        (vertexConnectedComponentEquiv D)
        (vertexConnectedComponentEquiv D) =
      Matrix.blockDiagonal'
        (fun c : D.ConnectedComponent =>
          sevenRegularLaplacianMatrix (D.induce c.supp)) := by
  let e := vertexConnectedComponentEquiv D
  have hscalar : (Matrix.scalar (Fin 64) (7 : ℚ)).reindex e e =
      Matrix.blockDiagonal'
        (fun c : D.ConnectedComponent => Matrix.scalar c.supp (7 : ℚ)) := by
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
        Matrix.blockDiagonal'_apply_ne _ _ _ hcc,
        Matrix.scalar_apply, hval]
  have hreindex :
      ((Matrix.scalar (Fin 64) (7 : ℚ) - D.adjMatrix ℚ).reindex e e) =
        (Matrix.scalar (Fin 64) (7 : ℚ)).reindex e e -
          (D.adjMatrix ℚ).reindex e e := by
    ext
    rfl
  rw [sevenRegularLaplacianMatrix, hreindex, hscalar,
    reindex_adjMatrix_eq_componentBlockDiagonal,
    ← Matrix.blockDiagonal'_sub]
  rfl

/-- The stable regular Laplacian action reindexes componentwise. -/
theorem componentFunctionLinearEquiv_sevenRegularLaplacian_mulVec
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (v : Fin 64 → ℚ) :
    componentFunctionLinearEquiv D
        ((sevenRegularLaplacianMatrix D).mulVec v) =
      fun c => (sevenRegularLaplacianMatrix (D.induce c.supp)).mulVec
        (componentFunctionLinearEquiv D v c) := by
  let hdec := ‹DecidableEq D.ConnectedComponent›
  classical
  letI : DecidableEq D.ConnectedComponent := hdec
  funext c y
  have hmat :=
    reindex_sevenRegularLaplacianMatrix_eq_componentBlockDiagonal D
  have happ := congrFun
    (congrArg (fun M => M.mulVec
      (fun z => v ((vertexConnectedComponentEquiv D).symm z))) hmat)
    (Sigma.mk c y)
  rw [reindex_mulVec_comp_symm_apply,
    dependentBlockDiagonal_mulVec_apply] at happ
  have he : (vertexConnectedComponentEquiv D).symm (Sigma.mk c y) = y.1 :=
    rfl
  rw [he] at happ
  have hfun :
      (fun z : c.supp =>
        v ((vertexConnectedComponentEquiv D).symm (Sigma.mk c z))) =
        componentFunctionLinearEquiv D v c := by
    funext z
    rw [componentFunctionLinearEquiv_apply]
    rfl
  rw [hfun] at happ
  rw [componentFunctionLinearEquiv_apply]
  exact happ

/-- Once the stable regular Laplacian preserves the global and component
mean-zero spaces, its global residual determinant is the product of the
component residual determinants. -/
theorem det_sevenRegularLaplacian_restrict_eq_prod_components
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [∀ c : D.ConnectedComponent, Fintype c.supp]
    (hW : ∀ v ∈ LinearMap.ker
        (defectComponentNormalizedProjection D).toLin',
      (sevenRegularLaplacianMatrix D).toLin' v ∈
        LinearMap.ker (defectComponentNormalizedProjection D).toLin')
    (hC : ∀ c : D.ConnectedComponent,
      ∀ v ∈ LinearMap.ker (coordinateSumLinearMap c.supp),
        (sevenRegularLaplacianMatrix (D.induce c.supp)).toLin' v ∈
          LinearMap.ker (coordinateSumLinearMap c.supp)) :
    LinearMap.det
        ((sevenRegularLaplacianMatrix D).toLin'.restrict hW) =
      ∏ c : D.ConnectedComponent,
        LinearMap.det
          ((sevenRegularLaplacianMatrix (D.induce c.supp)).toLin'.restrict
            (hC c)) := by
  let E := residualComponentMeanZeroLinearEquiv D
  let g := (sevenRegularLaplacianMatrix D).toLin'.restrict hW
  let f (c : D.ConnectedComponent) :=
    (sevenRegularLaplacianMatrix (D.induce c.supp)).toLin'.restrict (hC c)
  have hconj :
      (E : _ →ₗ[ℚ] _) ∘ₗ g ∘ₗ (E.symm : _ →ₗ[ℚ] _) =
        LinearMap.pi (fun c => (f c).comp (LinearMap.proj c)) := by
    apply LinearMap.ext
    intro w
    funext c
    apply Subtype.ext
    have ha := congrFun
      (componentFunctionLinearEquiv_sevenRegularLaplacian_mulVec D
        ((E.symm w).1)) c
    have hinv := E.apply_symm_apply w
    have hc := congrFun hinv c
    have hcval := congrArg Subtype.val hc
    change componentFunctionLinearEquiv D (E.symm w).1 c = (w c).1 at hcval
    change
      componentFunctionLinearEquiv D
          ((sevenRegularLaplacianMatrix D).mulVec (E.symm w).1) c =
        (sevenRegularLaplacianMatrix (D.induce c.supp)).mulVec (w c).1
    rw [ha, hcval]
  calc
    LinearMap.det g =
        LinearMap.det ((E : _ →ₗ[ℚ] _) ∘ₗ g ∘ₗ
          (E.symm : _ →ₗ[ℚ] _)) := by
      symm
      exact LinearMap.det_conj g E
    _ = LinearMap.det
        (LinearMap.pi (fun c => (f c).comp (LinearMap.proj c))) := by
      rw [hconj]
    _ = ∏ c : D.ConnectedComponent, LinearMap.det (f c) := by
      exact LinearMap.det_dependent_pi
        (fun c : D.ConnectedComponent =>
          LinearMap.ker (coordinateSumLinearMap c.supp)) f

end

end Erdos85
