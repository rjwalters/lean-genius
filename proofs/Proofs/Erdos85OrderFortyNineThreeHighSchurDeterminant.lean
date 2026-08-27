import Proofs.Erdos85OrderFortyNineHighDeterminantDivisibility
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The three-high Schur determinant at order 49 -/

namespace Erdos85

open Matrix

private def orderFortyNineOnes (m n : Type*) : Matrix m n ℚ :=
  fun _ _ => 1

private def orderFortyNineThreeHighRootBlock : Matrix (Fin 3) (Fin 3) ℚ :=
  (7 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) +
    orderFortyNineOnes (Fin 3) (Fin 3)

private def orderFortyNineThreeHighRootBlockInverse :
    Matrix (Fin 3) (Fin 3) ℚ :=
  (1 / 7 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) -
    (1 / 70 : ℚ) • orderFortyNineOnes (Fin 3) (Fin 3)

private theorem orderFortyNineThreeHighRootBlock_mul_inverse :
    orderFortyNineThreeHighRootBlock *
      orderFortyNineThreeHighRootBlockInverse = 1 := by
  native_decide

private theorem orderFortyNineThreeHighRootBlock_det :
    orderFortyNineThreeHighRootBlock.det = 490 := by
  native_decide

private theorem orderFortyNineThreeHigh_cross_mul_inverse_mul_cross :
    orderFortyNineOnes (Fin 46) (Fin 3) *
        orderFortyNineThreeHighRootBlockInverse *
        orderFortyNineOnes (Fin 3) (Fin 46) =
      (3 / 10 : ℚ) • orderFortyNineOnes (Fin 46) (Fin 46) := by
  native_decide

/-- The exact Schur reduction behind the three-high defect determinant.
The two root-difference directions contribute `7²`; the remaining root
direction contributes the factor ten and the rank-one coefficient `7/10`.
-/
theorem orderFortyNine_threeHigh_block_det_schur
    (L : Matrix (Fin 46) (Fin 46) ℚ) :
    (Matrix.fromBlocks
      orderFortyNineThreeHighRootBlock
      (orderFortyNineOnes (Fin 3) (Fin 46))
      (orderFortyNineOnes (Fin 46) (Fin 3))
      (L + orderFortyNineOnes (Fin 46) (Fin 46))).det =
        490 * (L + (7 / 10 : ℚ) •
          orderFortyNineOnes (Fin 46) (Fin 46)).det := by
  letI : Invertible orderFortyNineThreeHighRootBlock :=
    invertibleOfRightInverse _ _
      orderFortyNineThreeHighRootBlock_mul_inverse
  have hinv : ⅟orderFortyNineThreeHighRootBlock =
      orderFortyNineThreeHighRootBlockInverse :=
    invOf_eq_right_inv orderFortyNineThreeHighRootBlock_mul_inverse
  rw [Matrix.det_fromBlocks₁₁, hinv,
    orderFortyNineThreeHigh_cross_mul_inverse_mul_cross,
    orderFortyNineThreeHighRootBlock_det]
  congr 2
  ext i j
  simp [orderFortyNineOnes]
  ring

end Erdos85
