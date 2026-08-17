import Proofs.Erdos85OrderSixtyFourProjectionRank

/-! # The residual determinant of a complete eight-vertex block -/

namespace Erdos85

noncomputable section

/-- Coordinate summation on a finite rational function space. -/
def coordinateSumLinearMap (ι : Type*) [Fintype ι] :
    (ι → ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ i, v i
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum]

/-- The mean-zero space on an eight-element type has dimension seven. -/
theorem finrank_ker_coordinateSumLinearMap_eq_seven
    (ι : Type*) [Fintype ι] (hcard : Fintype.card ι = 8) :
    Module.finrank ℚ (LinearMap.ker (coordinateSumLinearMap ι)) = 7 := by
  have hsurj : Function.Surjective (coordinateSumLinearMap ι) := by
    intro y
    refine ⟨fun _ => y / 8, ?_⟩
    simp [coordinateSumLinearMap, hcard]
    ring
  have hrange : LinearMap.range (coordinateSumLinearMap ι) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (coordinateSumLinearMap ι)
  rw [hrange] at hsum
  have hone : Module.finrank ℚ ℚ = 1 := by simp
  have hamb : Module.finrank ℚ (ι → ℚ) = 8 := by
    simp [hcard]
  rw [finrank_top, hone, hamb] at hsum
  omega

/-- The matrix `8I-J`, i.e. the Laplacian of a complete graph on eight
vertices once the index type is known to have cardinality eight. -/
def eightCompleteLaplacianMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℚ :=
  (8 : ℚ) • (1 : Matrix ι ι ℚ) - Matrix.of (fun _ _ => (1 : ℚ))

/-- On the mean-zero sector, `8I-J` acts as scalar multiplication by eight. -/
theorem eightCompleteLaplacianMatrix_mulVec_of_sum_zero
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (v : ι → ℚ) (hv : coordinateSumLinearMap ι v = 0) :
    (eightCompleteLaplacianMatrix ι).mulVec v = 8 • v := by
  funext i
  rw [eightCompleteLaplacianMatrix, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [Matrix.mulVec, dotProduct]
  simp only [Matrix.of_apply, one_mul]
  change 8 * v i - coordinateSumLinearMap ι v = 8 * v i
  rw [hv, sub_zero]

/-- The determinant of the complete eight-vertex Laplacian on its residual
mean-zero sector is `8^7`. -/
theorem det_eightCompleteLaplacian_restrict_meanZero
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 8) :
    ∃ (hW : ∀ v ∈ LinearMap.ker (coordinateSumLinearMap ι),
          (eightCompleteLaplacianMatrix ι).toLin' v ∈
            LinearMap.ker (coordinateSumLinearMap ι)),
      LinearMap.det
          ((eightCompleteLaplacianMatrix ι).toLin'.restrict hW) =
        (8 : ℚ) ^ 7 := by
  let W := LinearMap.ker (coordinateSumLinearMap ι)
  have hW : ∀ v ∈ W, (eightCompleteLaplacianMatrix ι).toLin' v ∈ W := by
    intro v hv
    have heq := eightCompleteLaplacianMatrix_mulVec_of_sum_zero ι v hv
    change coordinateSumLinearMap ι
      ((eightCompleteLaplacianMatrix ι).mulVec v) = 0
    rw [heq]
    exact (W.smul_mem (8 : ℚ) hv)
  refine ⟨hW, ?_⟩
  have hrestrict :
      (eightCompleteLaplacianMatrix ι).toLin'.restrict hW =
        (8 : ℚ) • (LinearMap.id : W →ₗ[ℚ] W) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact eightCompleteLaplacianMatrix_mulVec_of_sum_zero ι v v.property
  rw [hrestrict, LinearMap.det_smul, LinearMap.det_id,
    finrank_ker_coordinateSumLinearMap_eq_seven ι hcard, mul_one]

end

end Erdos85
