import Proofs.Erdos85OrderSixtyFourCyclePrimaryMomentTerminal

/-! # Correct transformed moments for cycle primaries

The registered cycle factors have roots `μ = 7 - α²`.  Consequently an
irreducible `μ`-primary contributes `Σ(7-μ) = Σα²`, not `Σμ²`, to the
two-regular cycle-operator square trace.  The order-64 moment terminal uses
the distinct 7-regular defect-block operator, where `μ` itself is an actual
eigenvalue and `Σμ²` is the relevant invariant.  This diagnostic ledger records
both `Σα²` and `Σα⁴` directly from the top coefficients. -/

open Polynomial

namespace Erdos85

/-- If a degree-`d` monic polynomial has roots `μᵢ`, this is
`Σ (7-μᵢ)`. -/
def sevenMinusRootSum (f : ℤ[X]) (degree : ℕ) : ℤ :=
  7 * degree + f.coeff (degree - 1)

/-- If a degree-`d` monic polynomial has roots `μᵢ`, this is
`Σ (7-μᵢ)²`. -/
def sevenMinusRootSquareSum (f : ℤ[X]) (degree : ℕ) : ℤ :=
  49 * degree + 14 * f.coeff (degree - 1) +
    monicRootSquareMoment f degree

theorem cycleDefectQuadraticFive_adjacencyMoments :
    sevenMinusRootSum cycleDefectQuadraticFive 2 = 3 ∧
    sevenMinusRootSquareSum cycleDefectQuadraticFive 2 = 7 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectQuadraticFive,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuadraticSixteen_adjacencyMoments :
    sevenMinusRootSum cycleDefectQuadraticSixteen 2 = 4 ∧
    sevenMinusRootSquareSum cycleDefectQuadraticSixteen 2 = 12 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectQuadraticSixteen,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectCubicSeven_adjacencyMoments :
    sevenMinusRootSum cycleDefectCubicSeven 3 = 5 ∧
    sevenMinusRootSquareSum cycleDefectCubicSeven 3 = 13 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectCubicSeven,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectCubicNine_adjacencyMoments :
    sevenMinusRootSum cycleDefectCubicNine 3 = 6 ∧
    sevenMinusRootSquareSum cycleDefectCubicNine 3 = 18 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectCubicNine,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuinticEleven_adjacencyMoments :
    sevenMinusRootSum cycleDefectQuinticEleven 5 = 9 ∧
    sevenMinusRootSquareSum cycleDefectQuinticEleven 5 = 25 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectQuinticEleven,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectSexticThirteen_adjacencyMoments :
    sevenMinusRootSum cycleDefectSexticThirteen 6 = 11 ∧
    sevenMinusRootSquareSum cycleDefectSexticThirteen 6 = 31 := by
  norm_num [sevenMinusRootSum, sevenMinusRootSquareSum,
    monicRootSquareMoment, cycleDefectSexticThirteen,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

end Erdos85
