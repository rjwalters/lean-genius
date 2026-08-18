import Proofs.Erdos85BinarySquareMixedOwnerRootedPatternBounds
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Pointwise mixed-owner closing counts

The shifted owner-matrix product determines not only the global mixed trace:
on each edge of one owner color it gives the exact number of two-step returns
whose second edge has any fixed distinct owner color.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unshifted product formula for two distinct owner matrices. -/
theorem binarySquare_regular_ownerMatrices_cross_product
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
    (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ =
      ((m_a : ℤ) * (m_b : ℤ)) • FriendshipTheoremOQ01.onesMatrix V -
        (m_b : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ -
        (m_a : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ -
        ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
  have hshift := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree hq hreg hcard a b hab ha hb
  calc
    _ = ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ +
          (m_a : ℤ) • (1 : Matrix V V ℤ)) *
        ((componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ +
          (m_b : ℤ) • (1 : Matrix V V ℤ)) -
        (m_b : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ -
        (m_a : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ -
        ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
          module
    _ = _ := by rw [hshift]

/-- Pointwise mixed-owner closing census, in its cast-free natural-number
form.  If `xy` has owner `a`, then exactly `m_b (m_a - 1)` vertices `z`
close the colored walk `x-a-y-a-z-b-x`. -/
theorem binarySquare_regular_ownerEdge_coloredTwoStepMiddles_card
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
    (hb : b.supp.ncard = q * m_b) (hma : 1 ≤ m_a)
    {x y : V}
    (hxy : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) y x).card =
        m_b * (m_a - 1) := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hprod : A * B =
      ((m_a : ℤ) * (m_b : ℤ)) • J - (m_b : ℤ) • A -
        (m_a : ℤ) • B -
        ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
    simpa [A, B, J] using binarySquare_regular_ownerMatrices_cross_product
      G hfree hq hreg hcard a b hab ha hb
  have hyx : y ≠ x := hxy.symm.ne
  have hAyx : A y x = 1 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ y x = 1
    rw [SimpleGraph.adjMatrix_apply, if_pos hxy.symm]
  have hnotB : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y x := by
    have hiff := componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree a hxy.symm b
    intro hbyx
    exact hab (hiff.mp hbyx).symm
  have hByx : B y x = 0 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ y x = 0
    rw [SimpleGraph.adjMatrix_apply, if_neg hnotB]
  have hentry : (A * B) y x = (m_a : ℤ) * (m_b : ℤ) - m_b := by
    rw [hprod]
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    rw [hAyx, hByx]
    simp [J, FriendshipTheoremOQ01.onesMatrix, hyx]
  have hc := mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles
    (componentOwnerGraph G (secondOrderDefectGraph G) a)
    (componentOwnerGraph G (secondOrderDefectGraph G) b) y x
  change (A * B) y x =
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) y x).card : ℤ) at hc
  have hsub : (m_a : ℤ) - 1 = (m_a - 1 : ℕ) := by
    omega
  have hcast :
      ((coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) y x).card : ℤ) =
          (m_b * (m_a - 1) : ℕ) := by
    rw [← hc, hentry]
    push_cast
    rw [← hsub]
    ring
  exact_mod_cast hcast

end

end Erdos85
