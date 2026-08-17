import Proofs.Erdos85CycleDefectFactorIrreducibility

/-! # Moment terminal for the cycle-derived order-64 primaries -/

/-!
The moments in this file are moments of the transformed roots `μ` themselves.
For the cycle transport used elsewhere, `μ = 7 - α²`; hence these numbers are
**not** ambient adjacency square moments.  Any use of the bound `63` below
requires a separately proved bound on `Σμ²`.  The literal two-regular H16
adjacency matrix does not provide such a bound.  See
`Erdos85CyclePrimaryAdjacencyMomentLedger` for the correctly transformed
`Σα²` and `Σα⁴` values.
-/

open Polynomial

namespace Erdos85

/-- Newton's second root power sum from the top two nonleading
coefficients of a monic polynomial of known degree. -/
def monicRootSquareMoment (f : ℤ[X]) (degree : ℕ) : ℤ :=
  (f.coeff (degree - 1)) ^ 2 - 2 * f.coeff (degree - 2)

theorem cycleDefectQuadraticFive_eval_seven :
    cycleDefectQuadraticFive.eval 7 = 1 := by
  norm_num [cycleDefectQuadraticFive]

theorem cycleDefectQuadraticSixteen_eval_seven :
    cycleDefectQuadraticSixteen.eval 7 = 2 := by
  norm_num [cycleDefectQuadraticSixteen]

theorem cycleDefectCubicSeven_eval_seven :
    cycleDefectCubicSeven.eval 7 = 1 := by
  norm_num [cycleDefectCubicSeven]

theorem cycleDefectCubicNine_eval_seven :
    cycleDefectCubicNine.eval 7 = 1 := by
  norm_num [cycleDefectCubicNine]

theorem cycleDefectQuinticEleven_eval_seven :
    cycleDefectQuinticEleven.eval 7 = 1 := by
  norm_num [cycleDefectQuinticEleven]

theorem cycleDefectSexticThirteen_eval_seven :
    cycleDefectSexticThirteen.eval 7 = 1 := by
  norm_num [cycleDefectSexticThirteen]

/-- The `C16` quadratic is the unique nonlinear cycle factor whose value at
`7` is not a rational square. -/
theorem cycleDefectQuadraticSixteen_eval_seven_not_isSquare :
    ¬ IsSquare ((cycleDefectQuadraticSixteen.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectQuadraticSixteen_eval_seven]
  norm_num

theorem cycleDefectQuadraticFive_eval_seven_isSquare :
    IsSquare ((cycleDefectQuadraticFive.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectQuadraticFive_eval_seven]
  exact ⟨1, by norm_num⟩

theorem cycleDefectCubicSeven_eval_seven_isSquare :
    IsSquare ((cycleDefectCubicSeven.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectCubicSeven_eval_seven]
  exact ⟨1, by norm_num⟩

theorem cycleDefectCubicNine_eval_seven_isSquare :
    IsSquare ((cycleDefectCubicNine.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectCubicNine_eval_seven]
  exact ⟨1, by norm_num⟩

theorem cycleDefectQuinticEleven_eval_seven_isSquare :
    IsSquare ((cycleDefectQuinticEleven.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectQuinticEleven_eval_seven]
  exact ⟨1, by norm_num⟩

theorem cycleDefectSexticThirteen_eval_seven_isSquare :
    IsSquare ((cycleDefectSexticThirteen.eval 7 : ℤ) : ℚ) := by
  rw [cycleDefectSexticThirteen_eval_seven]
  exact ⟨1, by norm_num⟩

theorem cycleDefectQuadraticFive_squareMoment :
    monicRootSquareMoment cycleDefectQuadraticFive 2 = 63 := by
  norm_num [monicRootSquareMoment, cycleDefectQuadraticFive,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuadraticSixteen_squareMoment :
    monicRootSquareMoment cycleDefectQuadraticSixteen 2 = 54 := by
  norm_num [monicRootSquareMoment, cycleDefectQuadraticSixteen,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectCubicSeven_squareMoment :
    monicRootSquareMoment cycleDefectCubicSeven 3 = 90 := by
  norm_num [monicRootSquareMoment, cycleDefectCubicSeven,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectCubicNine_squareMoment :
    monicRootSquareMoment cycleDefectCubicNine 3 = 81 := by
  norm_num [monicRootSquareMoment, cycleDefectCubicNine,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectQuinticEleven_squareMoment :
    monicRootSquareMoment cycleDefectQuinticEleven 5 = 144 := by
  norm_num [monicRootSquareMoment, cycleDefectQuinticEleven,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

theorem cycleDefectSexticThirteen_squareMoment :
    monicRootSquareMoment cycleDefectSexticThirteen 6 = 171 := by
  norm_num [monicRootSquareMoment, cycleDefectSexticThirteen,
    coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]

/-- The dimension and defect-square moment of a nonlinear cycle primary
whose value at `7` is square.  The `C16` quadratic is absent because its
value at `7` is `2`, not a rational square. -/
def OrderSixtyFourSquareCyclePrimaryMoment
    (dimension squareMoment : ℕ) : Prop :=
  (dimension = 2 ∧ squareMoment = 63) ∨
  (dimension = 3 ∧ squareMoment = 90) ∨
  (dimension = 3 ∧ squareMoment = 81) ∨
  (dimension = 5 ∧ squareMoment = 144) ∨
  (dimension = 6 ∧ squareMoment = 171)

/-- Conditional arithmetic endpoint: if a raw `Σμ²` budget of `63` is
available, the sole listed square primary which fits is the golden
quadratic.  This theorem does not assert that the H16 cycle operator has
that raw transformed-root budget. -/
theorem squareCyclePrimary_moment_le_sixtyThree_forces_golden
    {dimension squareMoment : ℕ}
    (hprimary : OrderSixtyFourSquareCyclePrimaryMoment
      dimension squareMoment)
    (hbudget : squareMoment ≤ 63) :
    dimension = 2 ∧ squareMoment = 63 := by
  rcases hprimary with h | h | h | h | h <;> omega

/-- Once a golden quadratic occurs, its moment `63` leaves no room for any
rational square sector.  Its dimension is two, leaving an odd residual
dimension `13`, contrary to the even-degree residual-primary condition. -/
theorem false_of_orderSixtyFour_goldenCyclePrimary_constraints
    (golden rationalSix rationalThree rationalMinusTwo : ℕ)
    (hgolden : 1 ≤ golden)
    (hmoment : 63 * golden + 36 * rationalSix + 9 * rationalThree
      + 4 * rationalMinusTwo ≤ 63)
    (hresidualEven : Even
      (15 - (2 * golden + rationalSix + rationalThree + rationalMinusTwo))) :
    False := by
  rcases hresidualEven with ⟨half, hhalf⟩
  omega

end Erdos85
