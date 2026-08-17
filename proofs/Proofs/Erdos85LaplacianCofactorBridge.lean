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

/-- For a matrix with zero column sums, adding the all-ones matrix makes
every non-root entry of the transformed root row equal to the order. -/
theorem rowSumCongruence_laplacian_add_ones_root_row
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r j : ι} (hrj : j ≠ r) (L : Matrix ι ι R)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    rowSumCongruence r (L + Matrix.of (fun _ _ => (1 : R))) r j =
      (Fintype.card ι : R) := by
  rw [rowSumCongruence_apply_distinguished_left hrj]
  simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib,
    hcol, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_add]

/-- The analogous transformed root column also equals the order. -/
theorem rowSumCongruence_laplacian_add_ones_root_col
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i : ι} (hri : i ≠ r) (L : Matrix ι ι R)
    (hrow : ∀ i, ∑ j, L i j = 0) :
    rowSumCongruence r (L + Matrix.of (fun _ _ => (1 : R))) i r =
      (Fintype.card ι : R) := by
  rw [rowSumCongruence_apply_distinguished_right hri]
  simp only [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib,
    hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_add]

/-- The transformed root diagonal is the square of the order. -/
theorem rowSumCongruence_laplacian_add_ones_root_root
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) (L : Matrix ι ι R)
    (hrow : ∀ i, ∑ j, L i j = 0) :
    rowSumCongruence r (L + Matrix.of (fun _ _ => (1 : R))) r r =
      (Fintype.card ι : R) ^ 2 := by
  rw [rowSumCongruence_apply_distinguished]
  simp_rw [Matrix.add_apply, Matrix.of_apply, Finset.sum_add_distrib, hrow]
  simp [pow_two]

/-- The non-root block is unchanged, hence remains `L + J`. -/
theorem rowSumCongruence_laplacian_add_ones_ne_ne
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {r i j : ι} (hri : i ≠ r) (hrj : j ≠ r)
    (L : Matrix ι ι R) :
    rowSumCongruence r (L + Matrix.of (fun _ _ => (1 : R))) i j =
      L i j + 1 := by
  rw [rowSumCongruence_apply_ne_ne hri hrj]
  rfl

abbrev rootReduced {ι : Type*} (r : ι) := {x : ι // x ≠ r}

def rootSplitEquiv {ι : Type*} [DecidableEq ι] (r : ι) :
    ι ≃ Unit ⊕ rootReduced r where
  toFun x := if h : x = r then Sum.inl () else Sum.inr ⟨x, h⟩
  invFun
    | Sum.inl _ => r
    | Sum.inr x => x.1
  left_inv x := by
    by_cases h : x = r <;> simp [h]
  right_inv x := by
    rcases x with u | x
    · rcases u with ⟨⟩
      simp
    · simp [x.2]

/-- After splitting off the root, the transformed matrix has the explicit
block form needed by the Schur complement. -/
theorem rowSumCongruence_reindex_eq_fromBlocks
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (r : ι) (L : Matrix ι ι R)
    (hrow : ∀ i, ∑ j, L i j = 0)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    Matrix.reindex (rootSplitEquiv r) (rootSplitEquiv r)
      (rowSumCongruence r (L + Matrix.of (fun _ _ => (1 : R)))) =
      Matrix.fromBlocks
        (fun _ : Unit => fun _ : Unit => (Fintype.card ι : R) ^ 2)
        (fun _ : Unit => fun _ : rootReduced r => (Fintype.card ι : R))
        (fun _ : rootReduced r => fun _ : Unit => (Fintype.card ι : R))
        (L.submatrix (fun x : rootReduced r => x.1)
            (fun x : rootReduced r => x.1) +
          Matrix.of (fun _ : rootReduced r => fun _ : rootReduced r => (1 : R))) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rcases i with ⟨⟩
    rcases j with ⟨⟩
    simpa [Matrix.reindex_apply, rootSplitEquiv] using
      rowSumCongruence_laplacian_add_ones_root_root r L hrow
  · rcases i with ⟨⟩
    simpa [Matrix.reindex_apply, rootSplitEquiv] using
      rowSumCongruence_laplacian_add_ones_root_row j.2 L hcol
  · rcases j with ⟨⟩
    simpa [Matrix.reindex_apply, rootSplitEquiv] using
      rowSumCongruence_laplacian_add_ones_root_col i.2 L hrow
  · simpa [Matrix.reindex_apply, rootSplitEquiv] using
      rowSumCongruence_laplacian_add_ones_ne_ne i.2 j.2 L

/-- **Laplacian rank-one/cofactor identity.**  For a nonempty finite index
type and a matrix with zero row and column sums,
`det (L + J) = n² det(L without one row and column)`. -/
theorem det_laplacian_add_ones_eq_card_sq_mul_minor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι) (L : Matrix ι ι ℚ)
    (hrow : ∀ i, ∑ j, L i j = 0)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    Matrix.det (L + Matrix.of (fun _ _ => (1 : ℚ))) =
      (Fintype.card ι : ℚ) ^ 2 *
        Matrix.det (L.submatrix (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)) := by
  letI : Nonempty ι := ⟨r⟩
  let n : ℚ := Fintype.card ι
  let A : Matrix Unit Unit ℚ := fun _ _ => n ^ 2
  let B : Matrix Unit (rootReduced r) ℚ := fun _ _ => n
  let C : Matrix (rootReduced r) Unit ℚ := fun _ _ => n
  let K := L.submatrix (fun x : rootReduced r => x.1)
    (fun x : rootReduced r => x.1)
  let D : Matrix (rootReduced r) (rootReduced r) ℚ :=
    K + Matrix.of (fun _ _ => (1 : ℚ))
  have hn0 : n ≠ 0 := by
    dsimp only [n]
    norm_cast
    exact Fintype.card_ne_zero
  have hAdet : Matrix.det A = n ^ 2 := by
    rw [Matrix.det_unique]
  have hAunit : IsUnit (Matrix.det A) := by
    rw [hAdet]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hn0)
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hAunit
  have hschur : D - C * ⅟A * B = K := by
    have hAA : A * ⅟A = 1 := mul_invOf_self A
    have hentry := congrArg (fun M : Matrix Unit Unit ℚ => M () ()) hAA
    simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton,
      A, Matrix.one_apply_eq] at hentry
    ext x y
    simp only [Matrix.sub_apply, Matrix.mul_apply, Finset.univ_unique,
      Finset.sum_singleton, D, C, B, Matrix.add_apply, Matrix.of_apply]
    dsimp only [K]
    field_simp [hn0] at hentry ⊢
    nlinarith
  calc
    Matrix.det (L + Matrix.of (fun _ _ => (1 : ℚ))) =
        Matrix.det (rowSumCongruence r
          (L + Matrix.of (fun _ _ => (1 : ℚ)))) :=
      (det_rowSumChange_mul_mul_transpose r _).symm
    _ = Matrix.det (Matrix.reindex (rootSplitEquiv r) (rootSplitEquiv r)
          (rowSumCongruence r
            (L + Matrix.of (fun _ _ => (1 : ℚ))))) :=
      (Matrix.det_reindex_self (rootSplitEquiv r) _).symm
    _ = Matrix.det (Matrix.fromBlocks A B C D) := by
      rw [rowSumCongruence_reindex_eq_fromBlocks r L hrow hcol]
    _ = Matrix.det A * Matrix.det (D - C * ⅟A * B) :=
      Matrix.det_fromBlocks₁₁ A B C D
    _ = n ^ 2 * Matrix.det K := by rw [hAdet, hschur]
    _ = (Fintype.card ι : ℚ) ^ 2 *
        Matrix.det (L.submatrix (fun x : rootReduced r => x.1)
          (fun x : rootReduced r => x.1)) := by rfl

end

end Erdos85
