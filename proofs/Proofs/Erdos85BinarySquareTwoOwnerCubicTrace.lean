import Proofs.Erdos85BinarySquareMixedOwnerCubicTrace
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus
import Proofs.Erdos85OrderSixtyFourRegularPartitionShapes

/-! # Repeated-color cubic traces for two owner coordinates -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem trace_adjMatrix_mul_ones_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) :
    Matrix.trace (H.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) =
      (Fintype.card V : ℤ) * k := by
  rw [FriendshipTheoremOQ01.adjMatrix_mul_ones H k hreg,
    Matrix.trace_smul]
  simp [Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
  ring

/-- For two distinct owner coordinates, the cubic trace with the first color
repeated is determined solely by the two normalized component sizes.  Unlike
the three-distinct-color trace, this remains available when the defect graph
has only two components. -/
theorem binarySquare_regular_trace_firstOwner_sq_mul_secondOwner
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
        (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ) =
      ((q * q : ℕ) : ℤ) * ((q - 1 : ℕ) : ℤ) *
        (m_a : ℤ) * (m_b : ℤ) * ((m_a : ℤ) - 1) := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let Oa := componentOwnerGraph G (secondOrderDefectGraph G) a
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
  have hOareg : ∀ x, Oa.degree x = m_a * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard a ha
  have hAJ : Matrix.trace (A * J) =
      (Fintype.card V : ℤ) * (m_a * (q - 1) : ℕ) := by
    simpa [A, J, Oa] using
      trace_adjMatrix_mul_ones_of_regular Oa (m_a * (q - 1)) hOareg
  have hA2 : Matrix.trace (A * A) =
      (Fintype.card V : ℤ) * (m_a * (q - 1) : ℕ) := by
    simpa [A, Oa] using
      FriendshipTheoremOQ01.trace_adjMatrix_sq Oa
        (m_a * (q - 1)) hOareg
  have hAB : Matrix.trace (A * B) = 0 := by
    rw [hprod, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, SimpleGraph.trace_adjMatrix,
      SimpleGraph.trace_adjMatrix, Matrix.trace_one]
    have htraceJ : Matrix.trace J = Fintype.card V := by
      simp [J, Matrix.trace, Matrix.diag, FriendshipTheoremOQ01.onesMatrix]
    rw [htraceJ, hcard]
    ring
  change Matrix.trace (A * A * B) = _
  rw [Matrix.mul_assoc, hprod, Matrix.mul_sub, Matrix.mul_sub,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, hAJ, hA2, hAB,
    SimpleGraph.trace_adjMatrix, hcard]
  have hqcast : (((q - 1 : ℕ) : ℤ)) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  push_cast [hqcast]
  ring

/-- Combinatorial form of the repeated-color cubic trace. -/
theorem binarySquare_regular_card_twoOwnerColoredTriples
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
    (cyclicColoredTriples
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)).card =
      q * q * (q - 1) * m_a * m_b * (m_a - 1) := by
  have htrace := binarySquare_regular_trace_firstOwner_sq_mul_secondOwner
    G hfree hq hreg hcard a b hab ha hb
  rw [trace_three_adjMatrices_eq_card_cyclicColoredTriples] at htrace
  have hma : 1 ≤ m_a := by
    have hpos := a.nonempty_supp.ncard_pos
    rw [ha] at hpos
    exact Nat.pos_of_mul_pos_left hpos
  have hsubcast : (m_a : ℤ) - 1 = ((m_a - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hma]
    norm_num
  rw [hsubcast] at htrace
  exact_mod_cast htrace

/-- The three two-component order-64 strata have large, exact two-owner
triangle censuses, with the smaller normalized component used as the repeated
owner color. -/
theorem orderSixtyFour_regular_twoComponents_twoOwnerCensus
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ d, d.supp.ncard = 8 * m d) ∧
      ((∃ a b, a ≠ b ∧ m a = 2 ∧ m b = 6 ∧
          (cyclicColoredTriples
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card = 5376) ∨
       (∃ a b, a ≠ b ∧ m a = 3 ∧ m b = 5 ∧
          (cyclicColoredTriples
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card = 13440) ∨
       (∃ a b, a ≠ b ∧ m a = 4 ∧ m b = 4 ∧
          (cyclicColoredTriples
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)).card = 21504)) := by
  classical
  obtain ⟨m, E, hm, hshape⟩ :=
    orderSixtyFour_regular_two_defectComponents_partition_shape
      G hfree hreg hcount
  have hne : E.symm 0 ≠ E.symm 1 := by simp
  refine ⟨m, hm, ?_⟩
  rcases hshape with h26 | h62 | h35 | h53 | h44
  · left
    refine ⟨E.symm 0, E.symm 1, hne, h26.1, h26.2, ?_⟩
    simpa [h26.1, h26.2] using
      binarySquare_regular_card_twoOwnerColoredTriples G hfree
        (q := 8) (by norm_num) hreg (by norm_num) (E.symm 0) (E.symm 1)
        hne (hm (E.symm 0)) (hm (E.symm 1))
  · left
    refine ⟨E.symm 1, E.symm 0, hne.symm, h62.2, h62.1, ?_⟩
    simpa [h62.1, h62.2] using
      binarySquare_regular_card_twoOwnerColoredTriples G hfree
        (q := 8) (by norm_num) hreg (by norm_num) (E.symm 1) (E.symm 0)
        hne.symm (hm (E.symm 1)) (hm (E.symm 0))
  · right; left
    refine ⟨E.symm 0, E.symm 1, hne, h35.1, h35.2, ?_⟩
    simpa [h35.1, h35.2] using
      binarySquare_regular_card_twoOwnerColoredTriples G hfree
        (q := 8) (by norm_num) hreg (by norm_num) (E.symm 0) (E.symm 1)
        hne (hm (E.symm 0)) (hm (E.symm 1))
  · right; left
    refine ⟨E.symm 1, E.symm 0, hne.symm, h53.2, h53.1, ?_⟩
    simpa [h53.1, h53.2] using
      binarySquare_regular_card_twoOwnerColoredTriples G hfree
        (q := 8) (by norm_num) hreg (by norm_num) (E.symm 1) (E.symm 0)
        hne.symm (hm (E.symm 1)) (hm (E.symm 0))
  · right; right
    refine ⟨E.symm 0, E.symm 1, hne, h44.1, h44.2, ?_⟩
    simpa [h44.1, h44.2] using
      binarySquare_regular_card_twoOwnerColoredTriples G hfree
        (q := 8) (by norm_num) hreg (by norm_num) (E.symm 0) (E.symm 1)
        hne (hm (E.symm 0)) (hm (E.symm 1))

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_trace_firstOwner_sq_mul_secondOwner
#print axioms Erdos85.binarySquare_regular_card_twoOwnerColoredTriples
#print axioms Erdos85.orderSixtyFour_regular_twoComponents_twoOwnerCensus
