import Proofs.Erdos85DifferenceArrayArithmetic
import Proofs.Erdos85PrimeFourierSquare
import Proofs.NthRootIrrationalOQ01OQ01Real

/-!
# Algebraic norm bridge at order five

The real fifth-root parameter `μ = ζ + ζ⁻¹` satisfies `μ² + μ - 1 = 0`.
Writing a symmetric Fourier coefficient as `A + B μ`, the square-trace
identity implies that its quadratic norm squared is
`u⁴ (x² + x - 1)`.  Thus a nonsquare order-five norm forces `u = 0`.
-/

namespace Erdos85

open scoped BigOperators

/-- The real parameter of a primitive fifth root satisfies its standard
quadratic equation. -/
theorem orderFive_realParameter_relation
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5) :
    (ζ + ζ⁻¹) ^ 2 + (ζ + ζ⁻¹) - 1 = 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [Finset.sum_range_succ] using
      hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
  field_simp [hζ0]
  linear_combination hsum

/-- Over `ℂ`, `1` and the real fifth-root parameter are rationally linearly
independent. -/
theorem orderFive_realParameter_independent_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) :
    ∀ C D : ℚ, (C : ℂ) + (D : ℂ) * (ζ + ζ⁻¹) = 0 → D = 0 := by
  intro C D hCD
  by_contra hD
  have hrat : ζ + ζ⁻¹ = ((-C / D : ℚ) : ℂ) := by
    push_cast
    apply (eq_div_iff (show (D : ℂ) ≠ 0 by exact_mod_cast hD)).2
    linear_combination hCD
  exact NthRootIrrationalOQ01OQ01Real.trace_not_rational
    (n := 5) (by rw [Nat.totient_prime Nat.prime_five]; norm_num) hζ
      ⟨-C / D, hrat.symm⟩

/-- A negation-symmetric integral Fourier coefficient at order five lies in
the real quadratic line `ℚ + ℚ(ζ+ζ⁻¹)`, with explicit coordinates. -/
theorem orderFive_symmetric_fourier_eq_realQuadratic
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 5)
    (c : ZMod 5 → ℤ) (hsymm : ∀ y, c (-y) = c y) :
    (∑ y : ZMod 5, (c y : K) * primitiveRootCharacter hζ y) =
      ((c 0 - c 2 : ℤ) : K) +
        ((c 1 - c 2 : ℤ) : K) * (ζ + ζ⁻¹) := by
  have hsum : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 = 0 := by
    simpa [Finset.sum_range_succ] using
      hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
  have hpow4 : ζ ^ 4 = ζ⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      ζ ^ 4 * ζ = ζ ^ 5 := by ring
      _ = 1 := hζ.pow_eq_one
  have hc4 : c 4 = c 1 := by
    have := hsymm (1 : ZMod 5)
    norm_num at this ⊢
    exact this
  have hc3 : c 3 = c 2 := by
    have := hsymm (2 : ZMod 5)
    norm_num at this ⊢
    exact this
  calc
    (∑ y : ZMod 5, (c y : K) * primitiveRootCharacter hζ y) =
        ∑ i : Fin 5, (c (ZMod.finEquiv 5 i) : K) * ζ ^ i.val := by
          refine Fintype.sum_equiv (ZMod.finEquiv 5).symm _ _ ?_
          intro i
          have hi := (ZMod.finEquiv 5).apply_symm_apply i
          have hval : ((ZMod.finEquiv 5).symm i).val = i.val := by
            exact congrArg ZMod.val hi
          change (c i : K) * primitiveRootCharacter hζ i =
            (c ((ZMod.finEquiv 5) ((ZMod.finEquiv 5).symm i)) : K) *
              ζ ^ ((ZMod.finEquiv 5).symm i).val
          rw [hi, primitiveRootCharacter_eq_pow_val, hval]
    _ = (c 0 : K) + (c 1 : K) * ζ + (c 2 : K) * ζ ^ 2 +
          (c 3 : K) * ζ ^ 3 + (c 4 : K) * ζ ^ 4 := by
          norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
          rfl
    _ = ((c 0 - c 2 : ℤ) : K) +
          ((c 1 - c 2 : ℤ) : K) * (ζ + ζ⁻¹) := by
            rw [hc3, hc4, hpow4]
            push_cast
            rw [← hpow4]
            linear_combination (c 2 : K) * hsum

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

/-- Natural graph-parameter specialization: for `x ≥ 2`, the verified
consecutive-square sandwich forces the order-five square coefficient to
vanish. -/
theorem orderFive_coefficient_eq_zero
    {K : Type*} [Field K] [CharZero K]
    (μ : K) (hμ : μ ^ 2 + μ - 1 = 0)
    (hindep : ∀ C D : ℚ,
      (C : K) + (D : K) * μ = 0 → D = 0)
    (A B u : ℚ) (x : ℕ) (hx : 2 ≤ x)
    (hsq : ((A : K) + (B : K) * μ) ^ 2 =
      ((u : K) ^ 2) * (((x : ℚ) : K) - μ)) : u = 0 := by
  exact orderFive_coefficient_eq_zero_of_norm_not_isSquare
    μ hμ hindep A B u x hsq (orderFive_rationalNorm_not_isSquare x hx)

/-- Complete order-five Fourier norm step.  For a symmetric integral
coefficient vector, the square-frequency identity has zero Fourier side. -/
theorem orderFive_fourier_eq_zero_of_square_identity
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5)
    (c : ZMod 5 → ℤ) (hsymm : ∀ y, c (-y) = c y)
    (x : ℕ) (hx : 2 ≤ x) (u : ℤ)
    (hsq :
      (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ((u * u : ℤ) : ℂ) * ((x : ℂ) - ζ - ζ⁻¹)) :
    ∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y = 0 := by
  let H : ℂ := ∑ y : ZMod 5,
    (c y : ℂ) * primitiveRootCharacter hζ y
  let μ : ℂ := ζ + ζ⁻¹
  let A : ℚ := (c 0 - c 2 : ℤ)
  let B : ℚ := (c 1 - c 2 : ℤ)
  have hH : H = (A : ℂ) + (B : ℂ) * μ := by
    simpa only [H, A, B, μ, Rat.cast_intCast] using
      orderFive_symmetric_fourier_eq_realQuadratic hζ c hsymm
  have hsq' : ((A : ℂ) + (B : ℂ) * μ) ^ 2 =
      ((((u : ℚ) : ℂ)) ^ 2) * ((((x : ℚ) : ℂ)) - μ) := by
    rw [← hH]
    dsimp only [H, μ]
    convert hsq using 1 <;> push_cast <;> ring
  have huQ : (u : ℚ) = 0 := orderFive_coefficient_eq_zero μ
    (orderFive_realParameter_relation hζ)
    (orderFive_realParameter_independent_complex hζ)
    A B u x hx hsq'
  have hu : u = 0 := by exact_mod_cast huQ
  rw [hu] at hsq
  have hHzero : H * H = 0 := by
    dsimp only [H]
    calc
      (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) =
          (((0 : ℤ) * 0 : ℤ) : ℂ) * ((x : ℂ) - ζ - ζ⁻¹) := hsq
      _ = 0 := by norm_num
  exact mul_self_eq_zero.mp hHzero

end Erdos85
