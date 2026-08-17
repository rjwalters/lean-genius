import Proofs.Erdos85BinarySquareOwnerCross

/-!
# Orthogonality of centered owner-coordinate Gram blocks

Distinct shifted owner matrices have rank-one cross product.  After removing
their common all-ones direction integrally, the centered blocks annihilate
one another.  This is stronger than commutation and isolates the mutually
orthogonal nontrivial owner sectors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem regular_adjMatrix_mul_onesMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    H.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V =
      (k : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, mul_one]
  have hrow : (H.adjMatrix ℤ).mulVec (Function.const V 1) x = (k : ℤ) := by
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x]
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa using hrow

private theorem onesMatrix_mul_regular_adjMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    FriendshipTheoremOQ01.onesMatrix V * H.adjMatrix ℤ =
      (k : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  simp only [Matrix.mul_apply, FriendshipTheoremOQ01.onesMatrix,
    Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, one_mul]
  have hrow : (H.adjMatrix ℤ).mulVec (Function.const V 1) y = (k : ℤ) := by
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg y]
  rw [Matrix.mulVec, dotProduct] at hrow
  simpa [SimpleGraph.adjMatrix_apply, H.adj_comm] using hrow

private theorem shifted_regular_adjMatrix_mul_onesMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k m r : ℕ)
    (hreg : ∀ x, H.degree x = k) (hkm : k + m = r) :
    (H.adjMatrix ℤ + (m : ℤ) • (1 : Matrix V V ℤ)) *
        FriendshipTheoremOQ01.onesMatrix V =
      (r : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  rw [Matrix.add_mul, regular_adjMatrix_mul_onesMatrix H k hreg,
    Matrix.smul_mul, Matrix.one_mul, ← add_smul]
  norm_num [← Nat.cast_add, hkm]

private theorem onesMatrix_mul_shifted_regular_adjMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k m r : ℕ)
    (hreg : ∀ x, H.degree x = k) (hkm : k + m = r) :
    FriendshipTheoremOQ01.onesMatrix V *
        (H.adjMatrix ℤ + (m : ℤ) • (1 : Matrix V V ℤ)) =
      (r : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  rw [Matrix.mul_add, onesMatrix_mul_regular_adjMatrix H k hreg,
    Matrix.mul_smul, Matrix.mul_one, ← add_smul]
  norm_num [← Nat.cast_add, hkm]

private theorem onesMatrix_sq
    {V : Type*} [Fintype V] [DecidableEq V] :
    FriendshipTheoremOQ01.onesMatrix V *
        FriendshipTheoremOQ01.onesMatrix V =
      (Fintype.card V : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  simp [Matrix.mul_apply, FriendshipTheoremOQ01.onesMatrix]

/-- Distinct owner Gram blocks have mutually annihilating centered parts.
Here `M_c = Adj(Owner(c)) + m_c I`; multiplying by `q` avoids division by the
ambient order's square root. -/
theorem binarySquare_regular_centeredOwnerGrams_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    {m_c m_d : ℕ} (hc : c.supp.ncard = q * m_c)
    (hd : d.supp.ncard = q * m_d) :
    let J := FriendshipTheoremOQ01.onesMatrix V
    let M_c :=
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
        (m_c : ℤ) • (1 : Matrix V V ℤ)
    let M_d :=
      (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ +
        (m_d : ℤ) • (1 : Matrix V V ℤ)
    ((q : ℤ) • M_c - (m_c : ℤ) • J) *
        ((q : ℤ) • M_d - (m_d : ℤ) • J) = 0 := by
  dsimp
  let O_c := componentOwnerGraph G (secondOrderDefectGraph G) c
  let O_d := componentOwnerGraph G (secondOrderDefectGraph G) d
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hcReg : ∀ x, O_c.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hdReg : ∀ x, O_d.degree x = m_d * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard d hd
  have hcSum : m_c * (q - 1) + m_c = q * m_c := by
    calc
      m_c * (q - 1) + m_c = m_c * (q - 1) + m_c * 1 := by rw [Nat.mul_one]
      _ = m_c * ((q - 1) + 1) := by rw [Nat.mul_add]
      _ = m_c * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * m_c := by rw [Nat.mul_comm]
  have hdSum : m_d * (q - 1) + m_d = q * m_d := by
    calc
      m_d * (q - 1) + m_d = m_d * (q - 1) + m_d * 1 := by rw [Nat.mul_one]
      _ = m_d * ((q - 1) + 1) := by rw [Nat.mul_add]
      _ = m_d * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * m_d := by rw [Nat.mul_comm]
  apply centeredOwnerGrams_mul_eq_zero
  · exact binarySquare_regular_shiftedOwnerMatrices_cross_product
      G hfree hq hreg hcard c d hcd hc hd
  · exact shifted_regular_adjMatrix_mul_onesMatrix
      O_c (m_c * (q - 1)) m_c (q * m_c) hcReg hcSum
  · exact onesMatrix_mul_shifted_regular_adjMatrix
      O_d (m_d * (q - 1)) m_d (q * m_d) hdReg hdSum
  · rw [onesMatrix_sq, hcard]
    push_cast
    rfl

end

end Erdos85
