import Proofs.Erdos85OrderSixtyFourCofactorSquare
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Row-sum change of basis for the Laplacian cofactor bridge -/

namespace Erdos85

open Matrix

noncomputable section

/-- Replace one row of the identity by the all-ones row.  Left
multiplication sums all rows into the distinguished row; right
multiplication by its transpose performs the analogous column operation. -/
def rowSumChange
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) : Matrix ι ι R :=
  (1 : Matrix ι ι R).updateRow r (fun _ => 1)

/-- The row-sum change matrix is unimodular. -/
theorem det_rowSumChange
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) :
    Matrix.det (rowSumChange (R := R) r) = 1 := by
  have hrow :
      (fun _ : ι => (1 : R)) =
        ∑ k : ι, (1 : R) • (1 : Matrix ι ι R) k := by
    funext j
    simp [Matrix.one_apply]
  rw [rowSumChange, hrow, Matrix.det_updateRow_sum]
  simp

/-- Congruence by the row-sum change preserves determinants. -/
theorem det_rowSumChange_mul_mul_transpose
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) (M : Matrix ι ι R) :
    Matrix.det
      (rowSumChange (R := R) r * M *
        (rowSumChange (R := R) r).transpose) =
        Matrix.det M := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_rowSumChange, one_mul, mul_one]

/-- The distinguished row is all ones. -/
theorem rowSumChange_apply_distinguished
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r j : ι) :
    rowSumChange (R := R) r r j = 1 := by
  simp [rowSumChange]

/-- Every other row is the corresponding identity row. -/
theorem rowSumChange_apply_ne
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i : ι} (hri : i ≠ r) (j : ι) :
    rowSumChange (R := R) r i j = if i = j then 1 else 0 := by
  simp [rowSumChange, hri, Matrix.one_apply]

def rowSumCongruence
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) (M : Matrix ι ι R) : Matrix ι ι R :=
  rowSumChange (R := R) r * M * (rowSumChange (R := R) r).transpose

theorem rowSumChange_mul_apply_distinguished
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r j : ι) (M : Matrix ι ι R) :
    (rowSumChange (R := R) r * M) r j = ∑ i, M i j := by
  simp [Matrix.mul_apply, rowSumChange_apply_distinguished]

theorem rowSumChange_mul_apply_ne
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i : ι} (hri : i ≠ r) (j : ι) (M : Matrix ι ι R) :
    (rowSumChange (R := R) r * M) i j = M i j := by
  simp [Matrix.mul_apply, rowSumChange_apply_ne hri]

theorem mul_rowSumChange_transpose_apply_distinguished
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r i : ι) (M : Matrix ι ι R) :
    (M * (rowSumChange (R := R) r).transpose) i r = ∑ j, M i j := by
  simp [Matrix.mul_apply, rowSumChange_apply_distinguished]

theorem mul_rowSumChange_transpose_apply_ne
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r j : ι} (hrj : j ≠ r) (i : ι) (M : Matrix ι ι R) :
    (M * (rowSumChange (R := R) r).transpose) i j = M i j := by
  simp [Matrix.mul_apply, rowSumChange_apply_ne hrj]

/-- Away from the distinguished row and column the congruence leaves the
matrix entry unchanged. -/
theorem rowSumCongruence_apply_ne_ne
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i j : ι} (hri : i ≠ r) (hrj : j ≠ r)
    (M : Matrix ι ι R) :
    rowSumCongruence r M i j = M i j := by
  rw [rowSumCongruence, mul_rowSumChange_transpose_apply_ne hrj,
    rowSumChange_mul_apply_ne hri]

/-- Its distinguished row consists of column sums. -/
theorem rowSumCongruence_apply_distinguished_left
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r j : ι} (hrj : j ≠ r) (M : Matrix ι ι R) :
    rowSumCongruence r M r j = ∑ i, M i j := by
  rw [rowSumCongruence, mul_rowSumChange_transpose_apply_ne hrj,
    rowSumChange_mul_apply_distinguished]

/-- Its distinguished column consists of row sums. -/
theorem rowSumCongruence_apply_distinguished_right
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i : ι} (hri : i ≠ r) (M : Matrix ι ι R) :
    rowSumCongruence r M i r = ∑ j, M i j := by
  rw [rowSumCongruence, mul_rowSumChange_transpose_apply_distinguished]
  apply Finset.sum_congr rfl
  intro j _
  rw [rowSumChange_mul_apply_ne hri]

/-- The distinguished diagonal entry is the sum of all entries. -/
theorem rowSumCongruence_apply_distinguished
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) (M : Matrix ι ι R) :
    rowSumCongruence r M r r = ∑ i, ∑ j, M i j := by
  rw [rowSumCongruence, mul_rowSumChange_transpose_apply_distinguished]
  simp_rw [rowSumChange_mul_apply_distinguished]
  rw [Finset.sum_comm]

end

end Erdos85
