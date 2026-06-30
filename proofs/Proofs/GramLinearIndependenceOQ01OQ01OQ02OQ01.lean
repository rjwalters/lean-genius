import Proofs.GramLinearIndependenceOQ01OQ01

/-!
# Hadamard's determinant inequality for square matrices: row and uniform forms

The grandparent entry `gram-linear-independence-iff-oq-01-oq-01` proved the abstract
**Gram-matrix** form of Hadamard's inequality `det (gram 𝕜 v) ≤ ∏ i, ‖v i‖²`, and the
parent entry `gram-linear-independence-iff-oq-01-oq-01-oq-02` specialised it to the
**column** form for a square matrix, `‖det A‖ ≤ ∏ j, ‖col j A‖`.

This entry rounds out the matrix picture with the two remaining standard statements, both
obtained from the column bridge `gram 𝕜 (columns A) = Aᴴ * A` (so that
`det (Aᴴ A) = conj (det A) · det A = ‖det A‖²`):

* `matrix_hadamard_inequality` — the **column** form
  `‖det A‖ ≤ ∏ j, √(∑ i, ‖A i j‖²)`, re-derived self-containedly here as the platform for
  the two extensions below;
* `matrix_hadamard_inequality_rows` — the **row** form
  `‖det A‖ ≤ ∏ i, √(∑ j, ‖A i j‖²)`, obtained by transposing (`det Aᵀ = det A`);
* `matrix_hadamard_bound` — the **uniform** corollary `‖det A‖ ≤ (√n · M)^n = M^n · n^(n/2)`
  when every entry satisfies `‖A i j‖ ≤ M`, the classical ceiling showing a determinant of
  bounded entries grows no faster than `n^(n/2)`.

This file imports only the grandparent (`Proofs.GramLinearIndependenceOQ01OQ01`); the column
form is reproved from the bridge so that the row and uniform extensions stand on their own.

All results are machine-checked with no `sorry` and no extra axioms.
-/

namespace GramLinearIndependenceOQ01OQ01OQ02OQ01

open Matrix RCLike Finset
open scoped ComplexOrder InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The `j`-th column of a square matrix `A`, viewed as a vector in `EuclideanSpace 𝕜 (Fin n)`. -/
noncomputable def col (A : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n) : EuclideanSpace 𝕜 (Fin n) :=
  (WithLp.toLp 2 fun i => A i j)

omit [RCLike 𝕜] in
@[simp] theorem col_apply (A : Matrix (Fin n) (Fin n) 𝕜) (i j : Fin n) :
    (col A j) i = A i j := rfl

/-- **Bridge to the Gram matrix.** The Gram matrix of the columns of `A` is `Aᴴ * A`. -/
theorem gram_col_eq (A : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.gram 𝕜 (col A) = Aᴴ * A := by
  ext i j
  rw [Matrix.gram_apply, PiLp.inner_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [col_apply, col_apply, RCLike.inner_apply', Matrix.conjTranspose_apply, star_def]

/-- The Gramian of the columns is the squared norm of the determinant:
`det (gram 𝕜 (col A)) = ‖det A‖²`. -/
theorem gram_col_det (A : Matrix (Fin n) (Fin n) 𝕜) :
    (Matrix.gram 𝕜 (col A)).det = ((‖A.det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [gram_col_eq, Matrix.det_mul, Matrix.det_conjTranspose, star_def, RCLike.conj_mul]
  push_cast
  ring

/-- The squared norm of the `j`-th column is the sum of the squared moduli of its entries. -/
theorem norm_col_sq (A : Matrix (Fin n) (Fin n) 𝕜) (j : Fin n) :
    ‖col A j‖ ^ 2 = ∑ i, ‖A i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ => by rw [col_apply]

/-- **Squared form of Hadamard's inequality.** `‖det A‖² ≤ ∏ j, ∑ i, ‖A i j‖²`. -/
theorem matrix_hadamard_sq (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  have hbound := GramLinearIndependenceOQ01OQ01.hadamard_inequality_euclidean (col A)
  rw [gram_col_det A] at hbound
  have hreal : ‖A.det‖ ^ 2 ≤ ∏ j, ‖col A j‖ ^ 2 := by
    have := (RCLike.ofReal_le_ofReal (K := 𝕜)).mp hbound
    simpa using this
  calc ‖A.det‖ ^ 2 ≤ ∏ j, ‖col A j‖ ^ 2 := hreal
    _ = ∏ j, ∑ i, ‖A i j‖ ^ 2 := Finset.prod_congr rfl fun j _ => norm_col_sq A j

/-- **Hadamard's inequality for matrices (column form).** The modulus of the determinant of a
square matrix is at most the product of the Euclidean norms of its columns:
`‖det A‖ ≤ ∏ j, √(∑ i, ‖A i j‖²)`. -/
theorem matrix_hadamard_inequality (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) := by
  have hP : (0 : ℝ) ≤ ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) :=
    Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  have hsq : ‖A.det‖ ^ 2 ≤ (∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine (matrix_hadamard_sq A).trans (le_of_eq ?_)
    exact Finset.prod_congr rfl fun j _ =>
      (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
  rw [← Real.sqrt_sq (norm_nonneg A.det), ← Real.sqrt_sq hP]
  exact Real.sqrt_le_sqrt hsq

/-- **Hadamard's inequality for matrices (row form).** The modulus of the determinant is at most
the product of the Euclidean norms of the **rows**, obtained from the column form via
`det Aᵀ = det A`. -/
theorem matrix_hadamard_inequality_rows (A : Matrix (Fin n) (Fin n) 𝕜) :
    ‖A.det‖ ≤ ∏ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) := by
  have h := matrix_hadamard_inequality Aᵀ
  rw [Matrix.det_transpose] at h
  refine h.trans (le_of_eq (Finset.prod_congr rfl fun i _ => ?_))
  exact congrArg Real.sqrt (Finset.sum_congr rfl fun j _ => by rw [Matrix.transpose_apply])

/-- **Uniform entry bound.** If every entry of `A` has modulus at most `M ≥ 0`, then
`‖det A‖ ≤ (√n · M)^n = M^n · n^(n/2)` — the classical bound that shows the determinant of a
matrix with bounded entries cannot grow faster than `n^(n/2)`. -/
theorem matrix_hadamard_bound (A : Matrix (Fin n) (Fin n) 𝕜) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ i j, ‖A i j‖ ≤ M) :
    ‖A.det‖ ≤ (Real.sqrt n * M) ^ n := by
  refine (matrix_hadamard_inequality A).trans ?_
  have hcol : ∀ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt n * M := by
    intro j
    have hsum : ∑ i, ‖A i j‖ ^ 2 ≤ (n : ℝ) * M ^ 2 := by
      calc ∑ i, ‖A i j‖ ^ 2 ≤ ∑ _i : Fin n, M ^ 2 :=
            Finset.sum_le_sum fun i _ => by nlinarith [norm_nonneg (A i j), hbound i j]
        _ = (n : ℝ) * M ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc Real.sqrt (∑ i, ‖A i j‖ ^ 2) ≤ Real.sqrt ((n : ℝ) * M ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt n * M := by rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hM]
  calc ∏ j, Real.sqrt (∑ i, ‖A i j‖ ^ 2)
      ≤ ∏ _j : Fin n, (Real.sqrt n * M) :=
        Finset.prod_le_prod (fun j _ => Real.sqrt_nonneg _) (fun j _ => hcol j)
    _ = (Real.sqrt n * M) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GramLinearIndependenceOQ01OQ01OQ02OQ01

open GramLinearIndependenceOQ01OQ01OQ02OQ01 in
#print axioms matrix_hadamard_inequality_rows
open GramLinearIndependenceOQ01OQ01OQ02OQ01 in
#print axioms matrix_hadamard_bound
