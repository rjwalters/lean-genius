import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The one-high determinant block reduction

The graph-facing one-high square candidate has block form
`[[8, 1ᵀ], [1, H + J]]`.  Its defect geometry supplies a vector `x` with
`H x = 1` and coordinate sum `328`.  The lemma below isolates the purely
algebraic endpoint: the 49-dimensional determinant is exactly `2304 det H`.
-/

open Matrix

namespace Erdos85

noncomputable section

theorem det_oneHighBlock_eq_2304_mul_det
    {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℚ) (x : n → ℚ)
    (hx : H.mulVec x = 1)
    (hsum : ∑ i, x i = 328)
    (hHdet : H.det ≠ 0) :
    (Matrix.fromBlocks
      (fun _ : Unit => fun _ : Unit => (8 : ℚ))
      (fun _ : Unit => fun _ : n => (1 : ℚ))
      (fun _ : n => fun _ : Unit => (1 : ℚ))
      (H + Matrix.vecMulVec (fun _ : n => (1 : ℚ))
        (fun _ : n => (1 : ℚ)))).det = 2304 * H.det := by
  let A : Matrix Unit Unit ℚ := fun _ _ => 8
  let R : Matrix Unit n ℚ := fun _ _ => 1
  let C : Matrix n Unit ℚ := fun _ _ => 1
  let J : Matrix n n ℚ := Matrix.vecMulVec (fun _ => 1) (fun _ => 1)
  change (Matrix.fromBlocks A R C (H + J)).det = _
  have hAdet : A.det = 8 := by simp [A, Matrix.det_unique]
  have hAunit : IsUnit A.det := by rw [hAdet]; norm_num
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hAunit
  rw [Matrix.det_fromBlocks₁₁]
  rw [hAdet]
  have hAinv : ⅟A = (fun _ _ => (1 / 8 : ℚ)) := by
    apply invOf_eq_right_inv
    ext i j
    simp [A, Matrix.mul_apply]
  have hschur : H + J - C * ⅟A * R = H + (7 / 8 : ℚ) • J := by
    ext i j
    simp [hAinv, R, C, J, Matrix.mul_apply, Matrix.vecMulVec, smul_eq_mul]
    ring
  rw [hschur]
  have hHunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hHdet
  letI : Invertible H := Matrix.invertibleOfIsUnitDet H hHunit
  let u : n → ℚ := fun _ => 7 / 8
  let z : n → ℚ := fun _ => 1
  have houter : (7 / 8 : ℚ) • J =
      Matrix.replicateCol Unit u * Matrix.replicateRow Unit z := by
    ext i j
    simp [u, z, J, Matrix.vecMulVec, Matrix.mul_apply, smul_eq_mul]
  rw [houter, Matrix.det_add_replicateCol_mul_replicateRow hHunit]
  have hHu : H.mulVec ((7 / 8 : ℚ) • x) = u := by
    rw [Matrix.mulVec_smul, hx]
    ext i
    simp [u]
  have hInv : H⁻¹.mulVec u = (7 / 8 : ℚ) • x := by
    rw [← hHu]
    calc
      H⁻¹.mulVec (H.mulVec ((7 / 8 : ℚ) • x)) =
          ((H⁻¹ * H).mulVec ((7 / 8 : ℚ) • x)) := by
            rw [Matrix.mulVec_mulVec]
      _ = (7 / 8 : ℚ) • x := by rw [H.nonsing_inv_mul hHunit]; simp
  have hmiddle : H⁻¹ * Matrix.replicateCol Unit u =
      Matrix.replicateCol Unit ((7 / 8 : ℚ) • x) := by
    ext i j
    change (H⁻¹.mulVec u) i = (7 / 8 : ℚ) * x i
    simpa using congrFun hInv i
  rw [Matrix.mul_assoc, hmiddle]
  have hscalar :
      (1 + Matrix.replicateRow Unit z *
        Matrix.replicateCol Unit ((7 / 8 : ℚ) • x)).det = 288 := by
    rw [Matrix.det_unique]
    simp [Matrix.mul_apply, z, hsum]
    norm_num
  rw [hscalar]
  ring

end

end Erdos85
