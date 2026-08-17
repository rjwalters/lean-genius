import Proofs.Erdos85BinarySquareCenteredOwnerCross

/-!
# Resolution of the centered owner sectors

The centered owner Gram blocks resolve the nonconstant defect polynomial.
Together with pairwise annihilation, this makes each color an algebraic
summand of `q ((q-1)I-D)` and directly couples owner coordinates to the
cycle spectrum of the second-order defect graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The centered owner Gram blocks sum to the centered square-order defect
operator. -/
theorem binarySquare_regular_sum_centeredOwnerGrams
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hsum : ∑ c, m c = q) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      ((q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V)) =
      (q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ) := by
  have hO :=
    sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect
      G hfree
  have hsumZ : ∑ c, (m c : ℤ) = (q : ℤ) := by
    exact_mod_cast hsum
  rw [Finset.sum_sub_distrib]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]
  rw [← Finset.smul_sum, hO]
  simp_rw [smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_smul]
  simp only [← Finset.mul_sum, hsumZ]
  simp only [FriendshipTheoremOQ01.onesMatrix]
  rw [Nat.cast_sub hq]
  module

/-- Pairwise annihilation turns every centered owner block into a summand of
the defect polynomial: multiplying by the full resolution selects precisely
that block. -/
theorem binarySquare_regular_centeredOwnerGram_mul_defectResolution
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
    (hsum : ∑ c, m c = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let C_c :=
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    C_c * ((q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ)) = C_c * C_c := by
  dsimp
  let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
    fun d =>
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ +
            (m d : ℤ) • (1 : Matrix V V ℤ)) -
        (m d : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  have hresolution : (∑ d, C d) =
      (q : ℤ) •
        (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
          (secondOrderDefectGraph G).adjMatrix ℤ) := by
    exact binarySquare_regular_sum_centeredOwnerGrams G hfree (by omega) m hsum
  rw [← hresolution]
  rw [Finset.mul_sum]
  apply Finset.sum_eq_single c
  · intro d _hd hdc
    exact binarySquare_regular_centeredOwnerGrams_mul_eq_zero
      G hfree hq hreg hcard c d hdc.symm (hm c) (hm d)
  · simp

/-- Abstract finite Parseval identity for mutually selected matrix summands. -/
theorem sum_matrix_sq_eq_sq_of_sum_eq_of_mul_sum_eq_sq
    {I V K : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    [CommRing K]
    (C : I → Matrix V V K) (R : Matrix V V K)
    (hsum : ∑ i, C i = R) (hselect : ∀ i, C i * R = C i * C i) :
    ∑ i, C i * C i = R * R := by
  calc
    ∑ i, C i * C i = ∑ i, C i * R := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (hselect i).symm
    _ = (∑ i, C i) * R := by rw [Finset.sum_mul]
    _ = R * R := by rw [hsum]

/-- **Centered-owner Parseval identity.**  The sum of the squared color
sectors is exactly the square of the centered defect operator.  Taking traces
turns this into an additive Frobenius-mass identity across owner colors. -/
theorem binarySquare_regular_sum_centeredOwnerGrams_sq
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
    let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
      fun c =>
        (q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ)
    ∑ c, C c * C c = R * R := by
  dsimp
  let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
    fun c =>
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  let R : Matrix V V ℤ := (q : ℤ) •
    (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
      (secondOrderDefectGraph G).adjMatrix ℤ)
  apply sum_matrix_sq_eq_sq_of_sum_eq_of_mul_sum_eq_sq C R
  · exact binarySquare_regular_sum_centeredOwnerGrams G hfree (by omega) m hsum
  · intro c
    exact binarySquare_regular_centeredOwnerGram_mul_defectResolution
      G hfree hq hreg hcard m hm hsum c

/-- The total squared centered-owner mass has a closed numerical trace. -/
theorem binarySquare_regular_trace_defectResolution_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Matrix.trace
      (((q : ℤ) •
          (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
            (secondOrderDefectGraph G).adjMatrix ℤ)) *
        ((q : ℤ) •
          (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
            (secondOrderDefectGraph G).adjMatrix ℤ))) =
      ((q ^ 5 * (q - 1) : ℕ) : ℤ) := by
  let D := secondOrderDefectGraph G
  let A := D.adjMatrix ℤ
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have htrA : Matrix.trace A = 0 := by
    exact SimpleGraph.trace_adjMatrix (α := ℤ) D
  have htrA2 : Matrix.trace (A * A) =
      (Fintype.card V : ℤ) * ((q - 1 : ℕ) : ℤ) := by
    exact FriendshipTheoremOQ01.trace_adjMatrix_sq D (q - 1) hDreg
  have hexpand :
      ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)) *
          ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)) =
        ((q : ℤ) ^ 2 * (((q - 1 : ℕ) : ℤ) ^ 2)) •
            (1 : Matrix V V ℤ) -
          ((2 : ℤ) * (q : ℤ) ^ 2 * ((q - 1 : ℕ) : ℤ)) • A +
          ((q : ℤ) ^ 2) • (A * A) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_mul, mul_sub, smul_sub, smul_smul]
    module
  change Matrix.trace
      (((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)) *
        ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A))) = _
  rw [hexpand, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, htrA, htrA2, hcard]
  simp only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ q)]
  ring

end

end Erdos85
