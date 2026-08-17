import Proofs.Erdos85BinarySquareCenteredOwnerCubic

/-!
# Cubic trace arithmetic for centered owner sectors

This evaluates one color of the cubic centered-owner resolution.  Unlike the
quadratic Frobenius calibration, the result retains `trace(O_c^3)`, hence the
owner-triangle count, and is therefore capable of imposing new arithmetic on
the surviving mixed partitions.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem regular_adj_mul_ones
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

private theorem ones_mul_regular_adj
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

private theorem ones_sq
    {V : Type*} [Fintype V] [DecidableEq V] :
    FriendshipTheoremOQ01.onesMatrix V *
        FriendshipTheoremOQ01.onesMatrix V =
      (Fintype.card V : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  simp [Matrix.mul_apply, FriendshipTheoremOQ01.onesMatrix]

/-- **One-color cubic trace formula.**  The centered cube consists of the
owner-triangle trace plus an explicit polynomial in the normalized component
size. -/
theorem binarySquare_regular_trace_centeredOwnerGram_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    let O := componentOwnerGraph G (secondOrderDefectGraph G) c
    let C_c :=
      (q : ℤ) • (O.adjMatrix ℤ + (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    Matrix.trace (C_c * C_c * C_c) =
      (q : ℤ) ^ 3 *
        (Matrix.trace (O.adjMatrix ℤ * O.adjMatrix ℤ * O.adjMatrix ℤ) +
          (q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ) * (m_c : ℤ) ^ 2 *
            (3 - (m_c : ℤ))) := by
  dsimp
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let A := O.adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let M := A + (m_c : ℤ) • (1 : Matrix V V ℤ)
  let k := m_c * (q - 1)
  have hOreg : ∀ x, O.degree x = k :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hAJ : A * J = (k : ℤ) • J := regular_adj_mul_ones O k hOreg
  have hJA : J * A = (k : ℤ) • J := ones_mul_regular_adj O k hOreg
  have hJJ : J * J = ((q * q : ℕ) : ℤ) • J := by
    rw [ones_sq, hcard]
  have hMJ : M * J = ((q * m_c : ℕ) : ℤ) • J := by
    dsimp [M]
    rw [Matrix.add_mul, hAJ, Matrix.smul_mul, Matrix.one_mul, ← add_smul]
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring_nf
  have hJM : J * M = ((q * m_c : ℕ) : ℤ) • J := by
    dsimp [M]
    rw [Matrix.mul_add, hJA, Matrix.mul_smul, Matrix.mul_one, ← add_smul]
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring_nf
  have hMMJ : M * M * J = (((q * m_c : ℕ) : ℤ) ^ 2) • J := by
    rw [Matrix.mul_assoc, hMJ, Matrix.mul_smul, hMJ, smul_smul]
    push_cast
    ring_nf
  have hMJM : M * J * M = (((q * m_c : ℕ) : ℤ) ^ 2) • J := by
    rw [hMJ, Matrix.smul_mul, hJM, smul_smul]
    push_cast
    ring_nf
  have hJMM : J * M * M = (((q * m_c : ℕ) : ℤ) ^ 2) • J := by
    rw [hJM, Matrix.smul_mul, hJM, smul_smul]
    push_cast
    ring_nf
  have hcube :
      ((q : ℤ) • M - (m_c : ℤ) • J) *
          ((q : ℤ) • M - (m_c : ℤ) • J) *
          ((q : ℤ) • M - (m_c : ℤ) • J) =
        ((q : ℤ) ^ 3) • (M * M * M) -
          ((q : ℤ) ^ 4 * (m_c : ℤ) ^ 3) • J := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hMJ, hMMJ]
    simp only [Matrix.smul_mul, hJM, hJJ, smul_smul]
    push_cast
    module
  have htrA : Matrix.trace A = 0 :=
    SimpleGraph.trace_adjMatrix (α := ℤ) O
  have htrA2 : Matrix.trace (A * A) =
      ((q * q : ℕ) : ℤ) * (k : ℤ) := by
    rw [← hcard]
    exact FriendshipTheoremOQ01.trace_adjMatrix_sq O k hOreg
  have htrJ : Matrix.trace J = ((q * q : ℕ) : ℤ) := by
    rw [← hcard]
    simp [J, Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  have hM3 : M * M * M =
      A * A * A + (3 * (m_c : ℤ)) • (A * A) +
        (3 * (m_c : ℤ) ^ 2) • A +
        ((m_c : ℤ) ^ 3) • (1 : Matrix V V ℤ) := by
    dsimp [M]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  change Matrix.trace
      (((q : ℤ) • M - (m_c : ℤ) • J) *
        ((q : ℤ) • M - (m_c : ℤ) • J) *
        ((q : ℤ) • M - (m_c : ℤ) • J)) = _
  rw [hcube, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    hM3, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    htrA2, htrA, Matrix.trace_one, htrJ, hcard]
  dsimp [k]
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  ring

end

end Erdos85
