import Proofs.Erdos85BinarySquareCenteredOwnerResolution

/-!
# Colorwise trace calibration for centered owner sectors

The global Frobenius budget splits exactly in proportion to normalized defect
component size.  Consequently scalar trace mass alone cannot obstruct the
regular square-order core; any terminal must use rank, equality structure, or
the self-indexed cycle blocks.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem regular_adjMatrix_mul_ones_int
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

private theorem ones_mul_regular_adjMatrix_int
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

private theorem onesMatrix_sq_int
    {V : Type*} [Fintype V] [DecidableEq V] :
    FriendshipTheoremOQ01.onesMatrix V *
        FriendshipTheoremOQ01.onesMatrix V =
      (Fintype.card V : ℤ) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  simp [Matrix.mul_apply, FriendshipTheoremOQ01.onesMatrix]

/-- Trace of one centered owner sector. -/
theorem binarySquare_regular_trace_centeredOwnerGram
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
    Matrix.trace
      ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V) =
      ((m_c * q * q * (q - 1) : ℕ) : ℤ) := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have htrO : Matrix.trace (O.adjMatrix ℤ) = 0 :=
    SimpleGraph.trace_adjMatrix (α := ℤ) O
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, htrO, Matrix.trace_one]
  have htrJ : Matrix.trace (FriendshipTheoremOQ01.onesMatrix V) =
      (Fintype.card V : ℤ) := by
    simp [Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  rw [htrJ, hcard]
  simp only [zero_add]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  ring

/-- Squared Frobenius trace of one centered owner sector.  It is linear in
the normalized component size `m_c`. -/
theorem binarySquare_regular_trace_centeredOwnerGram_sq
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
    let C_c :=
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    Matrix.trace (C_c * C_c) =
      ((m_c * q ^ 4 * (q - 1) : ℕ) : ℤ) := by
  dsimp
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let A := O.adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let k := m_c * (q - 1)
  have hOreg : ∀ x, O.degree x = k :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hAJ : A * J = (k : ℤ) • J :=
    regular_adjMatrix_mul_ones_int O k hOreg
  have hJA : J * A = (k : ℤ) • J :=
    ones_mul_regular_adjMatrix_int O k hOreg
  have hJJ : J * J = (Fintype.card V : ℤ) • J := onesMatrix_sq_int
  have htrA : Matrix.trace A = 0 :=
    SimpleGraph.trace_adjMatrix (α := ℤ) O
  have htrA2 : Matrix.trace (A * A) =
      (Fintype.card V : ℤ) * (k : ℤ) :=
    FriendshipTheoremOQ01.trace_adjMatrix_sq O k hOreg
  have htrJ : Matrix.trace J = (Fintype.card V : ℤ) := by
    simp [J, Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  have hexpand :
      ((q : ℤ) • (A + (m_c : ℤ) • (1 : Matrix V V ℤ)) - (m_c : ℤ) • J) *
          ((q : ℤ) • (A + (m_c : ℤ) • (1 : Matrix V V ℤ)) - (m_c : ℤ) • J) =
        ((q : ℤ) ^ 2) • (A * A) +
          ((2 : ℤ) * (q : ℤ) ^ 2 * (m_c : ℤ)) • A +
          ((q : ℤ) ^ 2 * (m_c : ℤ) ^ 2) • (1 : Matrix V V ℤ) -
          ((q : ℤ) ^ 2 * (m_c : ℤ) ^ 2) • J := by
    rw [hcard] at hJJ
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub, smul_smul]
    rw [hAJ, hJA, hJJ]
    dsimp [k]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    module
  change Matrix.trace
      (((q : ℤ) • (A + (m_c : ℤ) • (1 : Matrix V V ℤ)) - (m_c : ℤ) • J) *
        ((q : ℤ) • (A + (m_c : ℤ) • (1 : Matrix V V ℤ)) - (m_c : ℤ) • J)) = _
  rw [hexpand, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    htrA2, htrA, Matrix.trace_one, htrJ, hcard]
  dsimp [k]
  simp only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  push_cast
  ring

/-- Every centered owner color satisfies the sharp moment-ratio equality
`trace(C_c²) = q² trace(C_c)`.  Any rank terminal must exploit the equality
case of this identity rather than its scalar sum. -/
theorem binarySquare_regular_trace_centeredOwnerGram_sq_eq
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
    let C_c :=
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m_c : ℤ) • (1 : Matrix V V ℤ)) -
        (m_c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    Matrix.trace (C_c * C_c) =
      ((q : ℤ) ^ 2) * Matrix.trace C_c := by
  dsimp
  rw [binarySquare_regular_trace_centeredOwnerGram_sq
      G hfree hq hreg hcard c hc,
    binarySquare_regular_trace_centeredOwnerGram
      G hfree hq hreg hcard c hc]
  push_cast
  ring

end

end Erdos85
