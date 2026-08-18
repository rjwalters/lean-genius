import Mathlib

/-!
# Balance algebra for an exterior partial-permutation grid

Split a balanced cell-incidence matrix into its row and column incidences
`Bₓ, Bᵧ`.  The cross-block equation

`H Bᵧ + Bₓ C = J`

with symmetric exterior adjacency `C` forces the occupied-cell relation
`Bₓ Bᵧᵀ` to be balanced against `H`.  Equivalently, its complement (when
both factors are regular) satisfies the missing-factor equation
`M Hᵀ = H Mᵀ` observed in the `μ = 3` grid audit.

The result is purely matrix algebra and is uniform in the grid order.
-/

open Matrix

namespace Erdos85

/-- The cross-block equation and constant row sums force the row/column
incidence relation to intertwine with `H` after transposition. -/
theorem exteriorGrid_crossBlock_forces_relation_balance
    {X Y U R : Type*} [Fintype X] [Fintype Y] [Fintype U]
    [DecidableEq X] [DecidableEq Y] [DecidableEq U]
    [CommRing R]
    (H : Matrix X Y R) (Bx : Matrix X U R) (By : Matrix Y U R)
    (C : Matrix U U R) (d : R)
    (hC : C.transpose = C)
    (hrow : ∀ x, ∑ u, Bx x u = d)
    (hcross : H * By + Bx * C = fun _ _ => 1) :
    H * By * Bx.transpose = Bx * By.transpose * H.transpose := by
  let P : Matrix X X R := H * By * Bx.transpose
  let A : Matrix X X R := Bx * C * Bx.transpose
  let J : Matrix X U R := fun _ _ => 1
  let Q : Matrix X X R := J * Bx.transpose
  have hmain : P + A = Q := by
    have hcross' : H * By + Bx * C = J := by simpa [J] using hcross
    have h := congrArg (fun M : Matrix X U R => M * Bx.transpose) hcross'
    rw [Matrix.add_mul] at h
    simpa only [P, A, Q] using h
  have hA : A.transpose = A := by
    simp only [A, transpose_mul, transpose_transpose, hC]
    exact (Matrix.mul_assoc Bx C Bx.transpose).symm
  have hQentry : ∀ i j, Q i j = d := by
    intro i j
    simp only [Q, J, mul_apply, transpose_apply, one_mul]
    simpa using hrow j
  have hQ : Q.transpose = Q := by
    ext i j
    rw [transpose_apply, hQentry, hQentry]
  have htrans : P.transpose + A = Q := by
    have h := congrArg Matrix.transpose hmain
    simpa only [transpose_add, hA, hQ] using h
  have hP : P = P.transpose := by
    apply add_right_cancel (b := A)
    rw [hmain, htrans]
  change P = _
  rw [hP]
  simp only [P, transpose_mul, transpose_transpose]
  exact (Matrix.mul_assoc Bx By.transpose H.transpose).symm

/-- If `H` has constant row sum, balance passes from an occupied relation to
its entrywise complement.  This is the abstract `R ↦ M = J - R` step used for
the missing-cell 2-factor. -/
theorem exteriorGrid_complement_relation_balance
    {X Y R : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [CommRing R]
    (H M : Matrix X Y R) (e : R)
    (hHrow : ∀ x, ∑ y, H x y = e)
    (hbalance : H * M.transpose = M * H.transpose) :
    let J : Matrix X Y R := fun _ _ => 1
    H * (J - M).transpose = (J - M) * H.transpose := by
  let J : Matrix X Y R := fun _ _ => 1
  have hJbalance : H * J.transpose = J * H.transpose := by
    ext i j
    simp only [mul_apply, transpose_apply, J, mul_one, one_mul]
    rw [hHrow i, hHrow j]
  change H * (J - M).transpose = (J - M) * H.transpose
  rw [transpose_sub, Matrix.mul_sub, Matrix.sub_mul, hJbalance, hbalance]

end Erdos85

#print axioms Erdos85.exteriorGrid_crossBlock_forces_relation_balance
#print axioms Erdos85.exteriorGrid_complement_relation_balance
