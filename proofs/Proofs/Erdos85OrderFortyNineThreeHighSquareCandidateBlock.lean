import Proofs.Erdos85OrderFortyNineThreeHighSchurDeterminant
import Proofs.Erdos85OrderFortyNineSquareRoot

/-! # The three-high square candidate as a 3+46 block matrix -/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryVertex (i : Fin 46) : Fin 49 :=
  Fin.natAdd 3 i

def orderFortyNineOrdinaryDefectL
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) ℚ :=
  fun i j => 6 * (1 : Matrix (Fin 46) (Fin 46) ℚ) i j -
    (secondOrderDefectGraph G).adjMatrix ℚ
      (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j)

private theorem orderFortyNine_defect_not_adj_of_degreeEight
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    {x y : Fin 49} (hx : G.degree x = 8) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  intro hxy
  have hzero :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin (by decide) hx).1
  have hy : y ∈ (secondOrderDefectGraph G).neighborFinset x := by
    simpa [SimpleGraph.mem_neighborFinset] using hxy
  have hpos : 1 ≤ (secondOrderDefectGraph G).degree x := by
    rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
    exact Finset.one_le_card.mpr ⟨y, hy⟩
  omega

/-- Under the canonical labeling with high vertices `0,1,2`, the rational
square candidate is exactly the block matrix consumed by the Schur formula.
-/
theorem orderFortyNine_threeHigh_squareCandidate_reindex_eq_blocks
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        ((Int.castRingHom ℚ).mapMatrix (orderFortyNineSquareCandidate G)) =
      Matrix.fromBlocks
        orderFortyNineThreeHighRootBlock
        (orderFortyNineOnes (Fin 3) (Fin 46))
        (orderFortyNineOnes (Fin 46) (Fin 3))
        (orderFortyNineOrdinaryDefectL G +
          orderFortyNineOnes (Fin 46) (Fin 46)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hi8 : G.degree (Fin.castAdd 46 i) = 8 :=
      (hhigh _).2 (by simp)
    have hD := orderFortyNine_defect_not_adj_of_degreeEight
      G hfree hmin hi8 (y := Fin.castAdd 46 j)
    have heq : Fin.castAdd 46 i = Fin.castAdd 46 j ↔ i = j := by
      exact Fin.castAdd_inj
    simp [orderFortyNineSquareCandidate, orderFortyNineHighDiagonal,
      orderFortyNineHighVertices, orderFortyNineThreeHighRootBlock,
      orderFortyNineOnes, Matrix.fromBlocks, finSumFinEquiv,
      FriendshipTheoremOQ01.onesMatrix, Matrix.one_apply,
      Matrix.ofNat_apply, Matrix.diagonal, hi8, hD, heq] <;>
      split_ifs <;> ring
  · have hi8 : G.degree (Fin.castAdd 46 i) = 8 :=
      (hhigh _).2 (by simp)
    have hD := orderFortyNine_defect_not_adj_of_degreeEight
      G hfree hmin hi8 (y := Fin.natAdd 3 j)
    have hne : Fin.castAdd 46 i ≠ Fin.natAdd 3 j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [orderFortyNineSquareCandidate, orderFortyNineHighDiagonal,
      orderFortyNineHighVertices, orderFortyNineOnes, Matrix.fromBlocks,
      finSumFinEquiv, FriendshipTheoremOQ01.onesMatrix,
      Matrix.ofNat_apply, Matrix.diagonal, hD, hne]
  · have hj8 : G.degree (Fin.castAdd 46 j) = 8 :=
      (hhigh _).2 (by simp)
    have hD := orderFortyNine_defect_not_adj_of_degreeEight
      G hfree hmin hj8 (y := Fin.natAdd 3 i)
    have hD' : ¬ (secondOrderDefectGraph G).Adj
        (Fin.natAdd 3 i) (Fin.castAdd 46 j) := by
      simpa [(secondOrderDefectGraph G).adj_comm] using hD
    have hne : Fin.natAdd 3 i ≠ Fin.castAdd 46 j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [orderFortyNineSquareCandidate, orderFortyNineHighDiagonal,
      orderFortyNineHighVertices, orderFortyNineOnes, Matrix.fromBlocks,
      finSumFinEquiv, FriendshipTheoremOQ01.onesMatrix,
      Matrix.ofNat_apply, Matrix.diagonal, hD', hne]
  · have hi7 : G.degree (Fin.natAdd 3 i) = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (by decide) (Fin.natAdd 3 i) with h | h
      · exact h
      · have := (hhigh _).1 h
        simp at this
    have heq : Fin.natAdd 3 i = Fin.natAdd 3 j ↔ i = j := by
      exact Fin.natAdd_inj 3
    simp [orderFortyNineSquareCandidate, orderFortyNineHighDiagonal,
      orderFortyNineHighVertices, orderFortyNineOnes,
      orderFortyNineOrdinaryDefectL, orderFortyNineOrdinaryVertex,
      Matrix.fromBlocks, finSumFinEquiv,
      FriendshipTheoremOQ01.onesMatrix, Matrix.one_apply,
      Matrix.ofNat_apply, Matrix.diagonal, hi7, heq] <;>
      split_ifs <;> ring

/-- Graph-level Schur formula for the canonical three-high labeling. -/
theorem orderFortyNine_threeHigh_squareCandidate_det_eq_fortyNine_mul_T
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ x : Fin 49, G.degree x = 8 ↔ x.val < 3)
    (hL : IsUnit (orderFortyNineOrdinaryDefectL G).det) :
    ((Int.castRingHom ℚ).mapMatrix
        (orderFortyNineSquareCandidate G)).det =
      49 * (10 * (orderFortyNineOrdinaryDefectL G).det +
        7 * dotProduct orderFortyNineOneVector
          ((orderFortyNineOrdinaryDefectL G).adjugate.mulVec
            orderFortyNineOneVector)) := by
  have hblock := orderFortyNine_threeHigh_squareCandidate_reindex_eq_blocks
    G hfree hmin hhigh
  have hdet := congrArg Matrix.det hblock
  rw [Matrix.det_reindex_self] at hdet
  rw [hdet]
  exact orderFortyNine_threeHigh_block_det_eq_fortyNine_mul_T_of_isUnit
    (orderFortyNineOrdinaryDefectL G) hL

end

end Erdos85
