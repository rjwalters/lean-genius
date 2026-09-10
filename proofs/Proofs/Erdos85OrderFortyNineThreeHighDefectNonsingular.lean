import Proofs.Erdos85WeightedDefectNonsingular
import Proofs.Erdos85OrderFortyNineDefectForcedSector

/-! The shifted ordinary defect matrix is nonsingular for an actual order49
C4-free graph with minimum degree7 and exactly the three labeled high vertices.
This is not a nonexistence theorem or a full adjacency determinant theorem. -/

open SimpleGraph
namespace Erdos85
noncomputable section

/-- Graph-facing H3 application of the positive-weight defect argument. -/
theorem orderFortyNine_threeHigh_defectShift_det_ne_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) :
    ((6 : ℝ) • (1 : Matrix (Fin 46) (Fin 46) ℝ) -
      (orderFortyNineOrdinaryDefectAdjInt G).map (Int.castRingHom ℝ)).det ≠ 0 := by
  let D := (orderFortyNineOrdinaryDefectAdjInt G).map (Int.castRingHom ℝ)
  let t : Fin 46 → ℝ := fun i => orderFortyNineOrdinaryHighSupportCountInt G i
  apply q7_defect_shift_det_ne_zero D t 3
  · intro i j
    simp only [D, Matrix.map_apply, Int.coe_castRingHom,
      orderFortyNineOrdinaryDefectAdjInt, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  · intro i
    simp [D, orderFortyNineOrdinaryDefectAdjInt, SimpleGraph.adjMatrix_apply]
  · intro i
    have hs : orderFortyNineOrdinaryHighSupportCountInt G i ≤ 3 := by
      unfold orderFortyNineOrdinaryHighSupportCountInt
      calc
        ∑ k : Fin 3, G.adjMatrix ℤ (Fin.castAdd 46 k) (orderFortyNineOrdinaryVertex i)
            ≤ ∑ _k : Fin 3, (1 : ℤ) := by
          apply Finset.sum_le_sum
          intro k _
          simp only [SimpleGraph.adjMatrix_apply]
          split_ifs <;> norm_num
        _ = 3 := by norm_num
    dsimp [t]
    exact_mod_cast hs
  · norm_num
  · intro i
    have hr := congrFun (orderFortyNineOrdinaryDefectAdjInt_mulVec_one
      G hfree hmin hhigh) i
    simp only [Matrix.mulVec, dotProduct, mul_one] at hr
    dsimp [D, t]
    exact_mod_cast hr
  · intro i
    have hr := congrFun (orderFortyNineOrdinaryDefectAdjInt_mulVec_highSupportCount
      G hfree hmin hhigh) i
    simp only [Matrix.mulVec, dotProduct] at hr
    dsimp [D, t]
    exact_mod_cast hr

end
end Erdos85
