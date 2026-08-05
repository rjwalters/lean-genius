import Proofs.Erdos85DifferenceArrayArithmetic

/-!
# Algebraic norm bridge at primitive order nine

For `μ = ζ + ζ⁻¹`, the primitive order-nine relation is
`μ³ - 3μ + 1 = 0`.  This file records the coefficient comparison and norm
identity behind the corrected 3-primary argument.  It uses the genuine cubic
norm `x³ - 3x + 1`, rather than the previously conflated product with the
order-three factor.
-/

namespace Erdos85

/-- Norm of `A + Bμ + Cμ²` in the cubic order with
`μ³ - 3μ + 1 = 0`. -/
def orderNineCubicNorm (A B C : ℚ) : ℚ :=
  A ^ 3 + 6 * A ^ 2 * C - 3 * A * B ^ 2 + 3 * A * B * C +
    9 * A * C ^ 2 - B ^ 3 + 3 * B * C ^ 2 + C ^ 3

/-- The three coefficient equations obtained by squaring
`A + Bμ + Cμ² = u √(x-μ)` imply the cubic norm identity. -/
theorem orderNine_cubicNorm_identity_of_coefficients
    (A B C u x : ℚ)
    (h0 : A ^ 2 - 2 * B * C = u ^ 2 * x)
    (h1 : 2 * A * B + 6 * B * C - C ^ 2 = -u ^ 2)
    (h2 : 2 * A * C + B ^ 2 + 3 * C ^ 2 = 0) :
    orderNineCubicNorm A B C ^ 2 =
      u ^ 6 * (x ^ 3 - 3 * x + 1) := by
  let M : Matrix (Fin 3) (Fin 3) ℚ := ![
    ![A, -C, -B],
    ![B, A + 3 * C, 3 * B - C],
    ![C, B, A + 3 * C]]
  let N : Matrix (Fin 3) (Fin 3) ℚ := ![
    ![x, 0, 1],
    ![-1, x, -3],
    ![0, -1, x]]
  have hmat : M * M = u ^ 2 • N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, N, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_smul] at hdet
  simp only [Fintype.card_fin] at hdet
  have hM : Matrix.det M = orderNineCubicNorm A B C := by
    simp [M, Matrix.det_fin_three, orderNineCubicNorm]
    ring
  have hN : Matrix.det N = x ^ 3 - 3 * x + 1 := by
    simp [N, Matrix.det_fin_three]
    ring
  rw [hM, hN] at hdet
  nlinarith [hdet]

/-- Coefficient comparison in any characteristic-zero field containing a
degree-three element satisfying the primitive order-nine relation. -/
theorem orderNine_norm_identity_of_square
    {K : Type*} [Field K] [CharZero K]
    (μ : K) (hμ : μ ^ 3 - 3 * μ + 1 = 0)
    (hindep : ∀ A B C : ℚ,
      (A : K) + (B : K) * μ + (C : K) * μ ^ 2 = 0 → B = 0 ∧ C = 0)
    (A B C u x : ℚ)
    (hsq : ((A : K) + (B : K) * μ + (C : K) * μ ^ 2) ^ 2 =
      ((u : K) ^ 2) * ((x : K) - μ)) :
    orderNineCubicNorm A B C ^ 2 =
      u ^ 6 * (x ^ 3 - 3 * x + 1) := by
  have hexpand :
      (((A : K) + (B : K) * μ + (C : K) * μ ^ 2) ^ 2 -
          ((u : K) ^ 2) * ((x : K) - μ)) =
        ((A ^ 2 - 2 * B * C - u ^ 2 * x : ℚ) : K) +
          ((2 * A * B + 6 * B * C - C ^ 2 + u ^ 2 : ℚ) : K) * μ +
          ((2 * A * C + B ^ 2 + 3 * C ^ 2 : ℚ) : K) * μ ^ 2 := by
    push_cast
    linear_combination (2 * B * C + C ^ 2 * μ) * hμ
  have hzero :
      ((A ^ 2 - 2 * B * C - u ^ 2 * x : ℚ) : K) +
          ((2 * A * B + 6 * B * C - C ^ 2 + u ^ 2 : ℚ) : K) * μ +
          ((2 * A * C + B ^ 2 + 3 * C ^ 2 : ℚ) : K) * μ ^ 2 = 0 := by
    rw [← hexpand, hsq, sub_self]
  obtain ⟨h1, h2⟩ := hindep _ _ _ hzero
  have h0 : A ^ 2 - 2 * B * C = u ^ 2 * x := by
    rw [h1, h2, Rat.cast_zero, zero_mul, add_zero] at hzero
    simp only [zero_mul, add_zero] at hzero
    have hconstant : A ^ 2 - 2 * B * C - u ^ 2 * x = 0 := by
      exact_mod_cast hzero
    nlinarith
  exact orderNine_cubicNorm_identity_of_coefficients A B C u x h0
    (by nlinarith) (by nlinarith)

/-- At an odd natural parameter, the primitive order-nine norm remains
nonsquare over the rationals. -/
theorem orderNine_rationalPrimitiveNorm_not_isSquare
    (x : ℕ) (hodd : Odd x) :
    ¬ IsSquare ((x : ℚ) ^ 3 - 3 * x + 1) := by
  have hcast : ((((x : ℤ) ^ 3 - 3 * (x : ℤ) + 1 : ℤ) : ℚ)) =
      (x : ℚ) ^ 3 - 3 * x + 1 := by
    push_cast
    ring
  rw [← hcast, Rat.isSquare_intCast_iff]
  exact orderNinePrimitiveNorm_not_isSquare x hodd

/-- The integral multiplier in the primitive order-nine square branch must
vanish: otherwise the cubic norm identity would exhibit the nonsquare
primitive norm as a rational square. -/
theorem orderNine_coefficient_eq_zero
    {K : Type*} [Field K] [CharZero K]
    (μ : K) (hμ : μ ^ 3 - 3 * μ + 1 = 0)
    (hindep : ∀ A B C : ℚ,
      (A : K) + (B : K) * μ + (C : K) * μ ^ 2 = 0 → B = 0 ∧ C = 0)
    (A B C u : ℚ) (x : ℕ) (hodd : Odd x)
    (hsq : ((A : K) + (B : K) * μ + (C : K) * μ ^ 2) ^ 2 =
      ((u : K) ^ 2) * (((x : ℚ) : K) - μ)) : u = 0 := by
  by_contra hu
  apply orderNine_rationalPrimitiveNorm_not_isSquare x hodd
  let y : ℚ := orderNineCubicNorm A B C / u ^ 3
  refine ⟨y, ?_⟩
  rw [show y * y = y ^ 2 by ring]
  dsimp only [y]
  rw [div_pow, orderNine_norm_identity_of_square μ hμ hindep A B C u x hsq]
  field_simp [hu]

end Erdos85
