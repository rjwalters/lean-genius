import Proofs.Erdos85BinarySquareOwnerCross
import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Mixed cubic traces of distinct owner colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem trace_ones_mul_regular_adjMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    Matrix.trace (FriendshipTheoremOQ01.onesMatrix V * H.adjMatrix ℤ) =
      (Fintype.card V : ℤ) * k := by
  rw [Matrix.trace_mul_comm,
    FriendshipTheoremOQ01.adjMatrix_mul_ones H k hreg,
    Matrix.trace_smul]
  simp [Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  ring

private theorem trace_distinct_owner_mul_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ) = 0 := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hshift := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree hq hreg hcard a b hab ha hb
  have hprod : A * B =
      ((m_a : ℤ) * (m_b : ℤ)) • J -
        (m_b : ℤ) • A - (m_a : ℤ) • B -
          ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
    calc
      A * B = (A + (m_a : ℤ) • (1 : Matrix V V ℤ)) *
            (B + (m_b : ℤ) • (1 : Matrix V V ℤ)) -
          (m_b : ℤ) • A - (m_a : ℤ) • B -
            ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
        module
      _ = _ := by rw [hshift]
  rw [hprod, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, SimpleGraph.trace_adjMatrix,
    SimpleGraph.trace_adjMatrix, Matrix.trace_one]
  have htraceJ : Matrix.trace J = Fintype.card V := by
    simp [J, Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  rw [htraceJ]
  ring

/-- For three pairwise-distinct owner coordinates, the mixed cubic trace is
completely determined by their normalized component sizes. -/
theorem binarySquare_regular_trace_three_distinct_ownerMatrices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {m_a m_b m_c : ℕ}
    (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    (hc : c.supp.ncard = q * m_c) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) =
      ((q * q : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) *
        (m_a : ℤ) * (m_b : ℤ) * (m_c : ℤ) := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let C := (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hshift := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree hq hreg hcard a b hab ha hb
  have hprod : A * B =
      ((m_a : ℤ) * (m_b : ℤ)) • J -
        (m_b : ℤ) • A - (m_a : ℤ) • B -
          ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
    calc
      A * B = (A + (m_a : ℤ) • (1 : Matrix V V ℤ)) *
            (B + (m_b : ℤ) • (1 : Matrix V V ℤ)) -
          (m_b : ℤ) • A - (m_a : ℤ) • B -
            ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
        module
      _ = _ := by rw [hshift]
  have hCreg : ∀ x,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).degree x =
        m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hJC : Matrix.trace (J * C) =
      (Fintype.card V : ℤ) * (m_c * (q - 1) : ℕ) :=
    trace_ones_mul_regular_adjMatrix _ _ hCreg
  have hAC : Matrix.trace (A * C) = 0 :=
    trace_distinct_owner_mul_eq_zero
      G hfree hq hreg hcard a c hac ha hc
  have hBC : Matrix.trace (B * C) = 0 :=
    trace_distinct_owner_mul_eq_zero
      G hfree hq hreg hcard b c hbc hb hc
  change Matrix.trace (A * B * C) = _
  rw [hprod, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, hJC, hAC, hBC, SimpleGraph.trace_adjMatrix, hcard]
  have hqcast : (((q - 1 : ℕ) : ℤ)) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  push_cast [hqcast]
  ring

/-- In the four-component order-64 branch, every ordered triple of distinct
owner colors has mixed cubic trace `3584`. -/
theorem orderSixtyFour_regular_fourComponents_trace_three_distinct_ownerMatrices
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) =
      3584 := by
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  simpa using binarySquare_regular_trace_three_distinct_ownerMatrices
    G hfree (q := 8) (by norm_num) hreg (by norm_num)
      a b c hab hac hbc (m_a := 2) (m_b := 2) (m_c := 2)
        (by norm_num [hall a]) (by norm_num [hall b]) (by norm_num [hall c])

end

end Erdos85
