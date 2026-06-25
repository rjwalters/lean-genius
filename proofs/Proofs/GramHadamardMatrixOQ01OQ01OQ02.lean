import Mathlib
import Proofs.GramLinearIndependenceOQ01OQ01

/-!
# Hadamard's determinant inequality, matrix form

For a square matrix `A : Matrix (Fin n) (Fin n) 𝕜` over `𝕜 = ℝ` or `ℂ`, **Hadamard's
inequality** bounds the absolute value of the determinant by the product of the Euclidean
norms of its columns:

* `hadamard_matrix_inequality` — `‖A.det‖ ≤ ∏ j, ‖col A j‖`,
* `hadamard_matrix_inequality_sq` — the squared form `‖A.det‖² ≤ ∏ j, ‖col A j‖²`,
* `hadamard_matrix_inequality_explicit` — the same with the column norms written out:
  `‖A.det‖ ≤ ∏ j, √(∑ i, ‖A i j‖²)`.

This is the classical matrix Hadamard inequality, derived here as a **corollary** of the
Gramian form proved in `GramLinearIndependenceOQ01OQ01`. The bridge is:

* the Gram matrix of the columns of `A` (as vectors of `EuclideanSpace 𝕜 (Fin n)`) is
  `Aᴴ * A` (`gram_col_eq`), so
* `det (gram 𝕜 (col A)) = det Aᴴ * det A = conj (det A) * det A = ‖det A‖²`
  (`gram_col_det`).

Feeding this into `hadamard_inequality_euclidean` turns the Gramian bound
`det (gram 𝕜 (col A)) ≤ ∏ j, ‖col A j‖²` into `‖det A‖² ≤ ∏ j, ‖col A j‖²`, and taking
square roots gives the matrix form. The geometric reading: the volume of the
parallelepiped spanned by the columns is at most the product of the edge lengths, with
equality exactly when the columns are pairwise orthogonal.

All results are machine-checked with no `sorry` and no extra axioms.
-/

namespace GramHadamardMatrixOQ01OQ01OQ02

open Matrix RCLike Finset
open scoped ComplexOrder InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The `j`-th column of `A`, viewed as a vector in `EuclideanSpace 𝕜 (Fin n)`. -/
def col (A : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n) : EuclideanSpace 𝕜 (Fin n) :=
  WithLp.toLp 2 (fun i => A i j)

omit [RCLike 𝕜] in
@[simp] theorem col_apply (A : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    col A j i = A i j := rfl

/-- **Column Gram matrix.** The Gram matrix of the columns of `A` is `Aᴴ * A`: indeed
`⟪col i, col j⟫ = ∑ k, conj (A k i) * A k j = (Aᴴ * A) i j`. -/
theorem gram_col_eq (A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.gram 𝕜 (col A) = Aᴴ * A := by
  ext i j
  rw [Matrix.gram_apply, Matrix.mul_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [RCLike.inner_apply, col_apply, col_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  ring

/-- **The Gramian of the columns is `‖det A‖²`.** Using `gram_col_eq` and
`det (Aᴴ * A) = conj (det A) * det A`. -/
theorem gram_col_det (A : Matrix (Fin n) (Fin n) 𝕜) :
    (Matrix.gram 𝕜 (col A)).det = ((‖A.det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [gram_col_eq, Matrix.det_mul, Matrix.det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
  push_cast
  ring

/-- **Hadamard's inequality, squared matrix form.** `‖det A‖² ≤ ∏ j, ‖col A j‖²`. -/
theorem hadamard_matrix_inequality_sq (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ‖col A j‖ ^ 2 := by
  have h := GramLinearIndependenceOQ01OQ01.hadamard_inequality_euclidean (col A)
  rw [gram_col_det] at h
  exact RCLike.ofReal_le_ofReal.mp h

/-- **Hadamard's inequality, matrix form.** The absolute value of the determinant is at
most the product of the Euclidean column norms: `‖det A‖ ≤ ∏ j, ‖col A j‖`. -/
theorem hadamard_matrix_inequality (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ j, ‖col A j‖ := by
  have hsq := hadamard_matrix_inequality_sq A
  rw [Finset.prod_pow] at hsq
  have hb : (0 : ℝ) ≤ ∏ j, ‖col A j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hb] at h

/-- The Euclidean norm of a column written out: `‖col A j‖ = √(∑ i, ‖A i j‖²)`. -/
theorem norm_col_eq (A : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n) :
    ‖col A j‖ = Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp only [col_apply]

/-- **Hadamard's inequality, explicit form.** With the column norms written out:
`‖det A‖ ≤ ∏ j, √(∑ i, ‖A i j‖²)`. -/
theorem hadamard_matrix_inequality_explicit (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  have h := hadamard_matrix_inequality A
  rwa [Finset.prod_congr rfl fun j _ => norm_col_eq A j] at h

end GramHadamardMatrixOQ01OQ01OQ02
