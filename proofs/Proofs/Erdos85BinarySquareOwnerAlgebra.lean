import Mathlib

/-!
# Algebraic skeleton for square-order owner coordinates

For a defect component `c`, the component Gram block is `M_c = A P_c A`.
For distinct components `c,e`, the square-order identity for `A²`, projector
orthogonality, defect block-diagonality, and uniform routing reduce
`M_c M_e` to a rank-one all-ones term.  This file isolates that noncommutative
matrix calculation from the graph-facing owner-coordinate API.
-/

namespace Erdos85

noncomputable section

/-- Abstract cross-owner Gram product.  The hypotheses are exactly the four
graph identities needed for distinct defect components. -/
theorem ownerGram_cross_product_of_square_relation
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (A D J P Q : Matrix V V K) (a r : K)
    (hsq : A * A = a • (1 : Matrix V V K) + J - D)
    (horth : P * Q = 0)
    (hdefect : P * D * Q = 0)
    (hroute : A * P * J * Q * A = r • J) :
    (A * P * A) * (A * Q * A) = r • J := by
  calc
    (A * P * A) * (A * Q * A) = A * P * (A * A) * Q * A := by
      simp only [Matrix.mul_assoc]
    _ = A * P * (a • (1 : Matrix V V K) + J - D) * Q * A := by rw [hsq]
    _ = A * P * (a • (1 : Matrix V V K)) * Q * A +
          A * P * J * Q * A - A * P * D * Q * A := by
      noncomm_ring
    _ = 0 + A * P * J * Q * A - 0 := by
      rw [show A * P * (a • (1 : Matrix V V K)) * Q * A = 0 by
        simp only [Matrix.mul_assoc]
        simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul]
        rw [show P * (Q * A) = 0 by rw [← Matrix.mul_assoc, horth, zero_mul]]
        simp]
      rw [show A * P * D * Q * A = 0 by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc D Q A, ← Matrix.mul_assoc P (D * Q) A,
          ← Matrix.mul_assoc P D Q, hdefect]
        simp]
    _ = r • J := by simpa using hroute

/-- If shifted owner matrices have symmetric rank-one cross products, then
the owner matrices themselves commute. -/
theorem ownerMatrices_comm_of_shifted_cross_product
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (O P J : Matrix V V K) (m n r : K)
    (hOP : (O + m • (1 : Matrix V V K)) *
        (P + n • (1 : Matrix V V K)) = r • J)
    (hPO : (P + n • (1 : Matrix V V K)) *
        (O + m • (1 : Matrix V V K)) = r • J) :
    O * P = P * O := by
  have h := hOP.trans hPO.symm
  have hcentral (X : Matrix V V K) (s : K) :
      X * (s • (1 : Matrix V V K)) = (s • (1 : Matrix V V K)) * X := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  let C := O * (n • (1 : Matrix V V K)) +
    (m • (1 : Matrix V V K)) * P +
      (m • (1 : Matrix V V K)) * (n • (1 : Matrix V V K))
  have hleft : (O + m • (1 : Matrix V V K)) *
      (P + n • (1 : Matrix V V K)) = O * P + C := by
    dsimp [C]
    noncomm_ring
    simp [smul_add, smul_smul, mul_comm]
  have hright : (P + n • (1 : Matrix V V K)) *
      (O + m • (1 : Matrix V V K)) = P * O + C := by
    dsimp [C]
    noncomm_ring [hcentral O n, hcentral P m]
    simp [smul_add, smul_smul, mul_comm]
  rw [hleft, hright] at h
  exact add_right_cancel h

/-- Integral centering removes the common all-ones direction.  If two Gram
blocks have the rank-one cross product and the expected constant row/column
sums, then their centered operators annihilate one another.  The formula uses
`q M - m J`, so it remains meaningful in characteristic two without dividing
by `q`. -/
theorem centeredOwnerGrams_mul_eq_zero
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (M N J : Matrix V V K) (q m n : K)
    (hMN : M * N = (m * n) • J)
    (hMJ : M * J = (q * m) • J)
    (hJN : J * N = (q * n) • J)
    (hJJ : J * J = (q * q) • J) :
    (q • M - m • J) * (q • N - n • J) = 0 := by
  rw [sub_mul, mul_sub, mul_sub]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hMN, hMJ, hJN, hJJ]
  simp only [smul_smul]
  module

end

end Erdos85
