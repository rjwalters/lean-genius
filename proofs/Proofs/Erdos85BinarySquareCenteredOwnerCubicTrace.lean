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

/-- Cubic trace of the centered defect resolution. -/
theorem binarySquare_regular_trace_defectResolution_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let D := secondOrderDefectGraph G
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - D.adjMatrix ℤ)
    Matrix.trace (R * R * R) =
      (q : ℤ) ^ 3 *
        ((q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ) ^ 2 * ((q + 2 : ℕ) : ℤ) -
          Matrix.trace (D.adjMatrix ℤ * D.adjMatrix ℤ * D.adjMatrix ℤ)) := by
  dsimp
  let D := secondOrderDefectGraph G
  let A := D.adjMatrix ℤ
  let a : ℤ := (q - 1 : ℕ)
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have htrA : Matrix.trace A = 0 :=
    SimpleGraph.trace_adjMatrix (α := ℤ) D
  have htrA2 : Matrix.trace (A * A) =
      ((q * q : ℕ) : ℤ) * a := by
    rw [← hcard]
    exact FriendshipTheoremOQ01.trace_adjMatrix_sq D (q - 1) hDreg
  have hexpand :
      ((q : ℤ) • (a • (1 : Matrix V V ℤ) - A)) *
          ((q : ℤ) • (a • (1 : Matrix V V ℤ) - A)) *
          ((q : ℤ) • (a • (1 : Matrix V V ℤ) - A)) =
        ((q : ℤ) ^ 3 * a ^ 3) • (1 : Matrix V V ℤ) -
          (3 * (q : ℤ) ^ 3 * a ^ 2) • A +
          (3 * (q : ℤ) ^ 3 * a) • (A * A) -
          ((q : ℤ) ^ 3) • (A * A * A) := by
    simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul]
    module
  change Matrix.trace
      (((q : ℤ) • (a • (1 : Matrix V V ℤ) - A)) *
        ((q : ℤ) • (a • (1 : Matrix V V ℤ) - A)) *
        ((q : ℤ) • (a • (1 : Matrix V V ℤ) - A))) = _
  rw [hexpand, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, htrA, htrA2, hcard]
  dsimp [a]
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  push_cast
  ring

/-- **Owner/defect cubic trace equation.**  After cancelling the common
`q^3` factor in the centered cubic resolution, all graph-dependent terms are
the adjacency-cube traces.  In particular their sum is congruent to zero
modulo `q^2`, which is the large two-primary triangle divisibility available
in the binary branch. -/
theorem binarySquare_regular_owner_defect_cube_trace_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (Matrix.trace
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
            (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
            (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) +
        (q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ) * (m c : ℤ) ^ 2 *
          (3 - (m c : ℤ)))) =
      (q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ) ^ 2 * ((q + 2 : ℕ) : ℤ) -
        Matrix.trace
          ((secondOrderDefectGraph G).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ) := by
  have htrace := binarySquare_regular_sum_trace_centeredOwnerGrams_cube
    G hfree hq hreg hcard m hm hsum
  have hcolor := fun c => binarySquare_regular_trace_centeredOwnerGram_cube
    G hfree hq hreg hcard c (hm c)
  simp_rw [hcolor] at htrace
  rw [binarySquare_regular_trace_defectResolution_cube
    G hfree hq hreg hcard] at htrace
  rw [← Finset.mul_sum] at htrace
  apply mul_left_cancel₀ (a := (q : ℤ) ^ 3)
  · exact pow_ne_zero 3 (by exact_mod_cast (show q ≠ 0 by omega))
  · exact htrace

/-- The graph-dependent cubic traces have a common `q²` divisibility.  Since
an adjacency-cube trace is six times a triangle count, this becomes a strong
two-primary divisibility when `q` is a power of two. -/
theorem binarySquare_regular_sq_dvd_sum_owner_defect_cube_traces
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    (q : ℤ) ^ 2 ∣
      Matrix.trace
          ((secondOrderDefectGraph G).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ *
            (secondOrderDefectGraph G).adjMatrix ℤ) +
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          Matrix.trace
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
              (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
              (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) := by
  have heq := binarySquare_regular_owner_defect_cube_trace_eq
    G hfree hq hreg hcard m hm hsum
  let correction := fun c : (secondOrderDefectGraph G).ConnectedComponent =>
    ((q - 1 : ℕ) : ℤ) * (m c : ℤ) ^ 2 * (3 - (m c : ℤ))
  let total : ℤ := ((q - 1 : ℕ) : ℤ) ^ 2 * ((q + 2 : ℕ) : ℤ)
  refine ⟨total - ∑ c, correction c, ?_⟩
  have hcorr :
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        (q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ) * (m c : ℤ) ^ 2 *
          (3 - (m c : ℤ))) =
        (q : ℤ) ^ 2 * ∑ c, correction c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _hc
    dsimp [correction]
    ring
  rw [Finset.sum_add_distrib, hcorr] at heq
  dsimp [total]
  push_cast at heq ⊢
  linarith

end

end Erdos85
