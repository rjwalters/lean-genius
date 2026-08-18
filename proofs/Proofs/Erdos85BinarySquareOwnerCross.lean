import Proofs.Erdos85BinarySquareOwnerAlgebra
import Proofs.Erdos85BinarySquareRegularParity

/-!
# Cross-coordinate owner algebra in a binary square-order core

This specializes the abstract owner Gram calculation to distinct connected
components of the second-order defect graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem binarySquare_regular_ownerGram_route
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) {m_c m_d : ℕ}
    (hc : c.supp.ncard = q * m_c) (hd : d.supp.ncard = q * m_d) :
    G.adjMatrix ℤ *
          defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) c *
        FriendshipTheoremOQ01.onesMatrix V *
          defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) d *
        G.adjMatrix ℤ =
      ((m_c : ℤ) * (m_d : ℤ)) • FriendshipTheoremOQ01.onesMatrix V := by
  ext x y
  simp only [Matrix.mul_apply, defectComponentDiagonalMatrix,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    SimpleGraph.adjMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  have hcx : (componentNeighborFinset G (secondOrderDefectGraph G) c x).card =
      m_c := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk x) c (x := x) (by rfl)
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hdy : (componentNeighborFinset G (secondOrderDefectGraph G) d y).card =
      m_d := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk y) d (x := y) (by rfl)
    rw [hd] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  simp only [Matrix.diagonal_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hsumc : (∑ z : V,
      if (secondOrderDefectGraph G).connectedComponentMk z = c then
        if G.Adj x z then (1 : ℤ) else 0 else 0) = (m_c : ℤ) := by
    calc
      _ = ∑ z : V, if G.Adj x z ∧
          (secondOrderDefectGraph G).connectedComponentMk z = c
          then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hxz : G.Adj x z <;>
          by_cases hzc : (secondOrderDefectGraph G).connectedComponentMk z = c <;>
          simp [hxz, hzc]
      _ = ((componentNeighborFinset G (secondOrderDefectGraph G) c x).card : ℤ) := by
        rw [Finset.sum_boole]
        have hfilt : (Finset.univ : Finset V).filter (fun z =>
            G.Adj x z ∧ (secondOrderDefectGraph G).connectedComponentMk z = c) =
            componentNeighborFinset G (secondOrderDefectGraph G) c x := by
          ext z
          simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset]
        rw [hfilt]
      _ = (m_c : ℤ) := by rw [hcx]
  rw [hsumc]
  calc
    (∑ z : V, if G.Adj z y then
        if (secondOrderDefectGraph G).connectedComponentMk z = d then
          (m_c : ℤ) else 0 else 0) =
        (m_c : ℤ) * ∑ z : V, if G.Adj z y ∧
          (secondOrderDefectGraph G).connectedComponentMk z = d
          then (1 : ℤ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hzy : G.Adj z y <;>
        by_cases hzd : (secondOrderDefectGraph G).connectedComponentMk z = d <;>
        simp [hzy, hzd]
    _ = (m_c : ℤ) *
        ((componentNeighborFinset G (secondOrderDefectGraph G) d y).card : ℤ) := by
      rw [Finset.sum_boole]
      have hfilt : (Finset.univ : Finset V).filter (fun z =>
          G.Adj z y ∧ (secondOrderDefectGraph G).connectedComponentMk z = d) =
          componentNeighborFinset G (secondOrderDefectGraph G) d y := by
        ext z
        simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          G.adj_comm]
      rw [hfilt]
    _ = (m_c : ℤ) * (m_d : ℤ) := by rw [hdy]

/-- Distinct defect coordinates have a rank-one cross Gram product. -/
theorem binarySquare_regular_ownerGram_cross_product
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
    (G.adjMatrix ℤ *
        defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) c *
        G.adjMatrix ℤ) *
      (G.adjMatrix ℤ *
        defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) d *
        G.adjMatrix ℤ) =
      ((m_c : ℤ) * (m_d : ℤ)) • FriendshipTheoremOQ01.onesMatrix V := by
  let D := secondOrderDefectGraph G
  let P := defectComponentDiagonalMatrix (K := ℤ) D c
  let Q := defectComponentDiagonalMatrix (K := ℤ) D d
  apply ownerGram_cross_product_of_square_relation
      (G.adjMatrix ℤ) (D.adjMatrix ℤ)
      (FriendshipTheoremOQ01.onesMatrix V) P Q
      ((q : ℤ) - 1) ((m_c : ℤ) * (m_d : ℤ))
  · exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  · ext x y
    simp only [P, Q, defectComponentDiagonalMatrix,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst y
      by_cases hxc : D.connectedComponentMk x = c <;>
        by_cases hxd : D.connectedComponentMk x = d <;> simp_all
    · simp [hxy]
  · have hcomm := adjMatrix_comm_defectComponentDiagonalMatrix
        (K := ℤ) D c
    rw [← hcomm, Matrix.mul_assoc]
    have hPQ : P * Q = 0 := by
      ext x y
      simp only [P, Q, defectComponentDiagonalMatrix,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
      by_cases hxy : x = y
      · subst y
        by_cases hxc : D.connectedComponentMk x = c <;>
          by_cases hxd : D.connectedComponentMk x = d <;> simp_all
      · simp [hxy]
    rw [hPQ, Matrix.mul_zero]
  · exact binarySquare_regular_ownerGram_route
      G hfree hq hreg hcard c d hc hd

/-- After restoring their deleted diagonals, distinct owner-coordinate
adjacency matrices multiply to the same rank-one constant matrix. -/
theorem binarySquare_regular_shiftedOwnerMatrices_cross_product
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
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
        (m_c : ℤ) • (1 : Matrix V V ℤ)) *
      ((componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ +
        (m_d : ℤ) • (1 : Matrix V V ℤ)) =
      ((m_c : ℤ) * (m_d : ℤ)) • FriendshipTheoremOQ01.onesMatrix V := by
  rw [binarySquare_regular_componentOwnerGraph_adjMatrix_eq
      G hfree hq hreg hcard c hc,
    binarySquare_regular_componentOwnerGraph_adjMatrix_eq
      G hfree hq hreg hcard d hd,
    sub_add_cancel, sub_add_cancel]
  exact binarySquare_regular_ownerGram_cross_product
    G hfree hq hreg hcard c d hcd hc hd

/-- Distinct owner-coordinate adjacency matrices commute. -/
theorem binarySquare_regular_ownerMatrices_comm
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
    (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ =
      (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ := by
  apply ownerMatrices_comm_of_shifted_cross_product
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ)
      ((componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ)
      (FriendshipTheoremOQ01.onesMatrix V)
      (m_c : ℤ) (m_d : ℤ) ((m_c : ℤ) * (m_d : ℤ))
  · exact binarySquare_regular_shiftedOwnerMatrices_cross_product
      G hfree hq hreg hcard c d hcd hc hd
  · simpa [mul_comm] using
      (binarySquare_regular_shiftedOwnerMatrices_cross_product
        G hfree hq hreg hcard d c hcd.symm hd hc)

end

end Erdos85
