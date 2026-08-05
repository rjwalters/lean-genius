import Proofs.Erdos85DifferenceArrayArithmetic

/-!
# Algebraic norm bridge at order five

The real fifth-root parameter `μ = ζ + ζ⁻¹` satisfies `μ² + μ - 1 = 0`.
Writing a symmetric Fourier coefficient as `A + B μ`, the square-trace
identity implies that its quadratic norm squared is
`u⁴ (x² + x - 1)`.  Thus a nonsquare order-five norm forces `u = 0`.
-/

namespace Erdos85

/-- Rational form of the consecutive-square obstruction already proved over
the naturals. -/
theorem orderFive_rationalNorm_not_isSquare (x : ℕ) (hx : 2 ≤ x) :
    ¬ IsSquare ((x : ℚ) ^ 2 + x - 1) := by
  have hcast : (((x * x + x - 1 : ℕ) : ℚ)) =
      (x : ℚ) ^ 2 + x - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ x * x + x)]
    push_cast
    ring
  rw [← hcast, Rat.isSquare_natCast_iff]
  exact orderFiveNorm_not_isSquare x hx

/-- Coefficient comparison in the quadratic order-five field converts the
square-trace equation into its rational norm identity. -/
theorem orderFive_norm_identity_of_square
    {K : Type*} [Field K] [CharZero K]
    (μ : K) (hμ : μ ^ 2 + μ - 1 = 0)
    (hindep : ∀ C D : ℚ,
      (C : K) + (D : K) * μ = 0 → D = 0)
    (A B u x : ℚ)
    (hsq : ((A : K) + (B : K) * μ) ^ 2 =
      ((u : K) ^ 2) * ((x : K) - μ)) :
    (A ^ 2 - A * B - B ^ 2) ^ 2 =
      u ^ 4 * (x ^ 2 + x - 1) := by
  have hexpand :
      (((A : K) + (B : K) * μ) ^ 2 -
          ((u : K) ^ 2) * ((x : K) - μ)) =
        ((A ^ 2 + B ^ 2 - u ^ 2 * x : ℚ) : K) +
          ((2 * A * B - B ^ 2 + u ^ 2 : ℚ) : K) * μ := by
    push_cast
    linear_combination (B : K) ^ 2 * hμ
  have hzero :
      ((A ^ 2 + B ^ 2 - u ^ 2 * x : ℚ) : K) +
        ((2 * A * B - B ^ 2 + u ^ 2 : ℚ) : K) * μ = 0 := by
    rw [← hexpand, hsq, sub_self]
  have hlinear : 2 * A * B - B ^ 2 + u ^ 2 = 0 :=
    hindep _ _ hzero
  have hconstant : A ^ 2 + B ^ 2 - u ^ 2 * x = 0 := by
    rw [hlinear, Rat.cast_zero, zero_mul, add_zero] at hzero
    exact_mod_cast hzero
  nlinarith [sq_nonneg (A ^ 2 - A * B - B ^ 2),
    sq_nonneg (u ^ 2)]

/-- Consequently, if the order-five norm is not a rational square, the
integer eigenvalue-multiplicity coefficient in the square branch vanishes. -/
theorem orderFive_coefficient_eq_zero_of_norm_not_isSquare
    {K : Type*} [Field K] [CharZero K]
    (μ : K) (hμ : μ ^ 2 + μ - 1 = 0)
    (hindep : ∀ C D : ℚ,
      (C : K) + (D : K) * μ = 0 → D = 0)
    (A B u x : ℚ)
    (hsq : ((A : K) + (B : K) * μ) ^ 2 =
      ((u : K) ^ 2) * ((x : K) - μ))
    (hnorm : ¬ IsSquare (x ^ 2 + x - 1)) : u = 0 := by
  by_contra hu
  apply hnorm
  let y : ℚ := (A ^ 2 - A * B - B ^ 2) / u ^ 2
  refine ⟨y, ?_⟩
  have hnormId := orderFive_norm_identity_of_square
    μ hμ hindep A B u x hsq
  change x ^ 2 + x - 1 = y * y
  rw [show y * y = y ^ 2 by ring]
  symm
  dsimp only [y]
  rw [div_pow, hnormId]
  field_simp [hu]

end Erdos85
