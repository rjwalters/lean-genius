import Proofs.Erdos85DifferenceArrayArithmetic
import Proofs.Erdos85OrderNineFourier
import Proofs.Erdos85PrimeFourierSquare
import Proofs.NthRootIrrationalOQ01OQ01Degree

/-!
# Algebraic norm bridge at primitive order nine

For `μ = ζ + ζ⁻¹`, the primitive order-nine relation is
`μ³ - 3μ + 1 = 0`.  This file records the coefficient comparison and norm
identity behind the corrected 3-primary argument.  It uses the genuine cubic
norm `x³ - 3x + 1`, rather than the previously conflated product with the
order-three factor.
-/

namespace Erdos85

open Polynomial Module IntermediateField

/-- The real parameter of a primitive ninth root satisfies the genuine
primitive order-nine cubic. -/
theorem orderNine_realParameter_relation
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 9) :
    (ζ + ζ⁻¹) ^ 3 - 3 * (ζ + ζ⁻¹) + 1 = 0 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hη : IsPrimitiveRoot (ζ ^ 3) 3 :=
    hζ.pow (by norm_num : 0 < 9) (by norm_num : 9 = 3 * 3)
  have hsum : 1 + ζ ^ 3 + ζ ^ 6 = 0 := by
    convert hη.geom_sum_eq_zero (by norm_num : 1 < 3) using 1 <;>
      simp [Finset.sum_range_succ] <;> ring
  field_simp [hζ0]
  linear_combination ζ ^ 3 * hsum - hζ.pow_eq_one

/-- Over `ℂ`, the first three powers of the real ninth-root parameter are
rationally linearly independent. -/
theorem orderNine_realParameter_independent_complex
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) :
    ∀ A B C : ℚ,
      (A : ℂ) + (B : ℂ) * (ζ + ζ⁻¹) +
        (C : ℂ) * (ζ + ζ⁻¹) ^ 2 = 0 → B = 0 ∧ C = 0 := by
  intro A B C hABC
  let μ : ℂ := ζ + ζ⁻¹
  have hζint : IsIntegral ℚ ζ :=
    NthRootIrrationalOQ01OQ01Degree.primitiveRoot_isIntegral
      (by norm_num : 0 < 9) hζ
  have hinv : ζ⁻¹ = ζ ^ 8 := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
    field_simp [hζ0]
    simpa [pow_succ] using hζ.pow_eq_one.symm
  have hμint : IsIntegral ℚ μ := by
    dsimp only [μ]
    exact hζint.add (hinv ▸ hζint.pow 8)
  have hdegree := NthRootIrrationalOQ01OQ01Degree.finrank_adjoin_trace_eq
    (n := 9) (by norm_num : 3 ≤ 9) hζ
  have hfinrank : Module.finrank ℚ
      (ℚ⟮ζ + ζ⁻¹⟯ : IntermediateField ℚ ℂ) = 3 := by
    rw [show Nat.totient 9 = 6 by decide] at hdegree
    omega
  have hmindeg : (minpoly ℚ μ).natDegree = 3 := by
    rw [← IntermediateField.adjoin.finrank hμint]
    simpa [μ] using hfinrank
  let P : ℚ[X] := Polynomial.C C * Polynomial.X ^ 2 +
    Polynomial.C B * Polynomial.X + Polynomial.C A
  have hPeval : Polynomial.aeval μ P = 0 := by
    dsimp only [P]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X]
    dsimp only [μ]
    change (C : ℂ) * (ζ + ζ⁻¹) ^ 2 +
      (B : ℂ) * (ζ + ζ⁻¹) + (A : ℂ) = 0
    linear_combination hABC
  have hPzero : P = 0 := by
    by_contra hP
    have hdvd : minpoly ℚ μ ∣ P := minpoly.dvd ℚ μ hPeval
    have hle := Polynomial.natDegree_le_of_dvd hdvd hP
    have hPdeg : P.natDegree ≤ 2 := by
      dsimp only [P]
      compute_degree
    rw [hmindeg] at hle
    omega
  have hC := congrArg (fun Q : ℚ[X] ↦ Q.coeff 2) hPzero
  have hB := congrArg (fun Q : ℚ[X] ↦ Q.coeff 1) hPzero
  simp [P] at hC hB
  exact ⟨hB, hC⟩

/-- A negation-symmetric integral Fourier coefficient at order nine has
explicit coordinates in the cubic real basis `1, μ, μ²`. -/
theorem orderNine_symmetric_fourier_eq_realCubic
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 9)
    (c : ZMod 9 → ℤ) (hsymm : ∀ y, c (-y) = c y) :
    (∑ y : ZMod 9, (c y : K) * primitiveRootCharacter hζ y) =
      ((c 0 - 2 * c 2 - c 3 + 2 * c 4 : ℤ) : K) +
        ((c 1 - c 4 : ℤ) : K) * (ζ + ζ⁻¹) +
        ((c 2 - c 4 : ℤ) : K) * (ζ + ζ⁻¹) ^ 2 := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hη : IsPrimitiveRoot (ζ ^ 3) 3 :=
    hζ.pow (by norm_num : 0 < 9) (by norm_num : 9 = 3 * 3)
  have hsum : 1 + ζ ^ 3 + ζ ^ 6 = 0 := by
    convert hη.geom_sum_eq_zero (by norm_num : 1 < 3) using 1 <;>
      simp [Finset.sum_range_succ] <;> ring
  have hc8 : c 8 = c 1 := by
    have h := hsymm (1 : ZMod 9)
    norm_num at h ⊢
    exact h
  have hc7 : c 7 = c 2 := by
    have h := hsymm (2 : ZMod 9)
    norm_num at h ⊢
    exact h
  have hc6 : c 6 = c 3 := by
    have h := hsymm (3 : ZMod 9)
    norm_num at h ⊢
    exact h
  have hc5 : c 5 = c 4 := by
    have h := hsymm (4 : ZMod 9)
    norm_num at h ⊢
    exact h
  have hs1 : ζ + ζ ^ 8 = ζ + ζ⁻¹ := by
    congr 1
    field_simp [hζ0]
    simpa [pow_succ] using hζ.pow_eq_one
  have hs2 : ζ ^ 2 + ζ ^ 7 = (ζ + ζ⁻¹) ^ 2 - 2 := by
    field_simp [hζ0]
    linear_combination hζ.pow_eq_one
  have hs3 : ζ ^ 3 + ζ ^ 6 = -1 := by
    linear_combination hsum
  have hs4 : ζ ^ 4 + ζ ^ 5 =
      2 - (ζ + ζ⁻¹) - (ζ + ζ⁻¹) ^ 2 := by
    have h5 : ζ ^ 5 = (ζ⁻¹) ^ 4 := by
      field_simp [hζ0]
      simpa [pow_succ] using hζ.pow_eq_one
    rw [h5]
    have hcheb : ζ ^ 4 + (ζ⁻¹) ^ 4 =
        (ζ + ζ⁻¹) ^ 4 - 4 * (ζ + ζ⁻¹) ^ 2 + 2 := by
      field_simp [hζ0]
      ring
    rw [hcheb]
    linear_combination (ζ + ζ⁻¹) * orderNine_realParameter_relation hζ
  calc
    (∑ y : ZMod 9, (c y : K) * primitiveRootCharacter hζ y) =
        ∑ i : Fin 9, (c (ZMod.finEquiv 9 i) : K) * ζ ^ i.val := by
          refine Fintype.sum_equiv (ZMod.finEquiv 9).symm _ _ ?_
          intro i
          have hi := (ZMod.finEquiv 9).apply_symm_apply i
          have hval : ((ZMod.finEquiv 9).symm i).val = i.val := by
            exact congrArg ZMod.val hi
          change (c i : K) * primitiveRootCharacter hζ i =
            (c ((ZMod.finEquiv 9) ((ZMod.finEquiv 9).symm i)) : K) *
              ζ ^ ((ZMod.finEquiv 9).symm i).val
          rw [hi, primitiveRootCharacter_eq_pow_val, hval]
    _ = (c 0 : K) + (c 1 : K) * ζ + (c 2 : K) * ζ ^ 2 +
          (c 3 : K) * ζ ^ 3 + (c 4 : K) * ζ ^ 4 +
          (c 5 : K) * ζ ^ 5 + (c 6 : K) * ζ ^ 6 +
          (c 7 : K) * ζ ^ 7 + (c 8 : K) * ζ ^ 8 := by
            norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
            rfl
    _ = ((c 0 - 2 * c 2 - c 3 + 2 * c 4 : ℤ) : K) +
          ((c 1 - c 4 : ℤ) : K) * (ζ + ζ⁻¹) +
          ((c 2 - c 4 : ℤ) : K) * (ζ + ζ⁻¹) ^ 2 := by
            rw [hc5, hc6, hc7, hc8]
            push_cast
            linear_combination
              (c 1 : K) * hs1 + (c 2 : K) * hs2 +
              (c 3 : K) * hs3 + (c 4 : K) * hs4

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

/-- Complete primitive order-nine Fourier norm step.  A symmetric integral
coefficient vector satisfying the graph square-frequency identity has
vanishing Fourier coefficient whenever the graph parameter is odd. -/
theorem orderNine_fourier_eq_zero_of_square_identity
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9)
    (c : ZMod 9 → ℤ) (hsymm : ∀ y, c (-y) = c y)
    (x : ℕ) (hodd : Odd x) (u : ℤ)
    (hsq :
      (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ((u * u : ℤ) : ℂ) * ((x : ℂ) - ζ - ζ⁻¹)) :
    ∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y = 0 := by
  let H : ℂ := ∑ y : ZMod 9,
    (c y : ℂ) * primitiveRootCharacter hζ y
  let μ : ℂ := ζ + ζ⁻¹
  let A : ℚ := (c 0 - 2 * c 2 - c 3 + 2 * c 4 : ℤ)
  let B : ℚ := (c 1 - c 4 : ℤ)
  let C : ℚ := (c 2 - c 4 : ℤ)
  have hH : H = (A : ℂ) + (B : ℂ) * μ + (C : ℂ) * μ ^ 2 := by
    simpa only [H, A, B, C, μ, Rat.cast_intCast] using
      orderNine_symmetric_fourier_eq_realCubic hζ c hsymm
  have hsq' : ((A : ℂ) + (B : ℂ) * μ + (C : ℂ) * μ ^ 2) ^ 2 =
      ((((u : ℚ) : ℂ)) ^ 2) * ((((x : ℚ) : ℂ)) - μ) := by
    rw [← hH]
    dsimp only [H, μ]
    convert hsq using 1 <;> push_cast <;> ring
  have huQ : (u : ℚ) = 0 := orderNine_coefficient_eq_zero μ
    (orderNine_realParameter_relation hζ)
    (orderNine_realParameter_independent_complex hζ)
    A B C u x hodd hsq'
  have hu : u = 0 := by exact_mod_cast huQ
  rw [hu] at hsq
  have hHzero : H * H = 0 := by
    dsimp only [H]
    calc
      (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) =
          (((0 : ℤ) * 0 : ℤ) : ℂ) * ((x : ℂ) - ζ - ζ⁻¹) := hsq
      _ = 0 := by norm_num
  exact mul_self_eq_zero.mp hHzero

/-- ZMod/character form of the primitive order-nine divisibility terminal. -/
theorem three_dvd_sum_of_orderNine_character_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 9)
    (c : ZMod 9 → ℤ)
    (hzero : ∑ y : ZMod 9,
      (c y : K) * primitiveRootCharacter hζ y = 0) :
    (3 : ℤ) ∣ ∑ y : ZMod 9, c y := by
  let a : Fin 9 → ℤ := fun i ↦ c (ZMod.finEquiv 9 i)
  have hzeroFin : ∑ i : Fin 9, (a i : K) * ζ ^ i.val = 0 := by
    calc
      (∑ i : Fin 9, (a i : K) * ζ ^ i.val) =
          ∑ y : ZMod 9,
            (c y : K) * primitiveRootCharacter hζ y := by
              refine Fintype.sum_equiv (ZMod.finEquiv 9) _ _ ?_
              intro i
              simp [a]
      _ = 0 := hzero
  have hdvd := three_dvd_sum_of_orderNine_fourier_eq_zero hζ a hzeroFin
  have hsum : (∑ i : Fin 9, a i) = ∑ y : ZMod 9, c y := by
    refine Fintype.sum_equiv (ZMod.finEquiv 9) _ _ ?_
    intro i
    simp [a]
  rw [← hsum]
  exact hdvd

end Erdos85
