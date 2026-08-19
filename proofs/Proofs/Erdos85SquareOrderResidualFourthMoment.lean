import Proofs.Erdos85SquareOrderAdjacencyMoments
import Proofs.Erdos85SquareOrderHighQuadraticResidual

/-!
# Arithmetic interface for the residual quadratic-sector moments

The high quadratic factor contributes `2 * (h - 1) * d` to the second
power sum and `2 * (h - 1) * d^2` to the fourth power sum.  This file
isolates the exact subtraction and the first even Newton identity.  The
statements are phrased as an interface: a later trace/root decomposition
only has to supply the two additive moment equations.
-/

namespace Erdos85

/-- Subtracting `h - 1` quadratic pairs from the square-order adjacency
moments gives the displayed residual second and fourth moments. -/
theorem squareOrder_residual_even_moments_of_quadratic_pairs
    (d h ambientSecond ambientFourth residualSecond residualFourth : ℤ)
    (hambientSecond : ambientSecond = d ^ 3 + h)
    (hambientFourth : ambientFourth = 2 * d ^ 4 - d ^ 3 + (4 * d + 1) * h)
    (hsplitSecond : ambientSecond = 2 * (h - 1) * d + residualSecond)
    (hsplitFourth : ambientFourth = 2 * (h - 1) * d ^ 2 + residualFourth) :
    residualSecond = d ^ 3 + h - 2 * (h - 1) * d ∧
    residualFourth =
      2 * d ^ 4 - d ^ 3 + (4 * d + 1) * h - 2 * (h - 1) * d ^ 2 := by
  constructor <;> omega

/-- At order 49 and minimum degree 7, the residual power sums are affine
functions of the number `h` of degree-eight vertices. -/
theorem orderFortyNineSeven_residual_even_moments_of_quadratic_pairs
    (h ambientSecond ambientFourth residualSecond residualFourth : ℤ)
    (hambientSecond : ambientSecond = 343 + h)
    (hambientFourth : ambientFourth = 4459 + 29 * h)
    (hsplitSecond : ambientSecond = 14 * (h - 1) + residualSecond)
    (hsplitFourth : ambientFourth = 98 * (h - 1) + residualFourth) :
    residualSecond = 357 - 13 * h ∧
    residualFourth = 4557 - 69 * h := by
  constructor <;> omega

/-- The trace-zero specialization of the fourth Newton identity.  Here
`secondCoeff` and `fourthCoeff` are the second and fourth elementary
symmetric functions (equivalently the corresponding coefficients of a
monic polynomial with zero next coefficient). -/
theorem fourth_newton_identity_of_first_power_sum_zero
    (secondPower fourthPower secondCoeff fourthCoeff : ℤ)
    (hsecond : 2 * secondCoeff = -secondPower)
    (hfourth : 4 * fourthCoeff = -(secondCoeff * secondPower + fourthPower)) :
    8 * fourthCoeff = secondPower ^ 2 - 2 * fourthPower := by
  calc
    8 * fourthCoeff = 2 * (4 * fourthCoeff) := by ring
    _ = -2 * (secondCoeff * secondPower + fourthPower) := by rw [hfourth]; ring
    _ = -(2 * secondCoeff) * secondPower - 2 * fourthPower := by ring
    _ = secondPower ^ 2 - 2 * fourthPower := by rw [hsecond]; ring

/-- The resulting exact fourth-coefficient constraint for the order-49
residual.  Keeping it in denominator-free form makes it usable over `ℤ`. -/
theorem orderFortyNineSeven_residual_fourthCoeff_constraint
    (h residualSecond residualFourth secondCoeff fourthCoeff : ℤ)
    (hsecondMoment : residualSecond = 357 - 13 * h)
    (hfourthMoment : residualFourth = 4557 - 69 * h)
    (hsecondNewton : 2 * secondCoeff = -residualSecond)
    (hfourthNewton :
      4 * fourthCoeff = -(secondCoeff * residualSecond + residualFourth)) :
    8 * fourthCoeff = 169 * h ^ 2 - 9144 * h + 118335 := by
  have hnewton := fourth_newton_identity_of_first_power_sum_zero
    residualSecond residualFourth secondCoeff fourthCoeff
    hsecondNewton hfourthNewton
  rw [hsecondMoment, hfourthMoment] at hnewton
  nlinarith

end Erdos85
