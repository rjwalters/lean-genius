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

end

end Erdos85
