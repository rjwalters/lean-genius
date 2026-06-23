/-
Area of Circle OQ-05-OQ-02: Multivariate Gaussian Integral via Matrix Diagonalization

Proves the multivariate Gaussian integral formula:

    ∫ x : Fin n → ℝ, exp(-xᵀAx) = √(πⁿ / det A)

for any positive-definite real symmetric matrix A.

## Proof Strategy

1. **Diagonal case** (`diagonal_gaussian`): When A = diag(b₁,...,bₙ),
   exp(-∑ bᵢxᵢ²) = ∏ exp(-bᵢxᵢ²). Apply Fubini to factor the integral
   over ℝⁿ into a product of scalar Gaussian integrals ∫ exp(-bᵢxᵢ²) = √(π/bᵢ).
   Then ∏ √(π/bᵢ) = √(πⁿ/∏bᵢ) by induction.

2. **General case** (`multivariate_gaussian_integral`): Diagonalize A = UᵀDU via
   the spectral theorem (U orthogonal, D = diag(λ₁,...,λₙ), λᵢ > 0).
   The orthogonal change of variables y = Uᵀx preserves Lebesgue measure
   (|det Uᵀ| = 1). Then xᵀAx = yᵀDy = ∑ λᵢyᵢ², and det A = ∏ λᵢ.

## Status (all proved, 0 sorries)
- `prod_sqrt_eq_sqrt_prod` : proved (induction on n)
- `diagonal_gaussian` : proved (Fubini + scalar Gaussian)
- `multivariate_gaussian_integral` : proved (spectral decomposition + orthogonal change of variables)

Parent: AreaOfCircleOQ05.lean
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Determinant
import Proofs.AreaOfCircleOQ05

namespace MultivariateGaussian

open MeasureTheory Real Matrix Finset

/-! ## Part 1: Product of Square Roots -/

/-- Helper: the product of square roots equals the square root of the product,
    when all factors are nonneg.

    `∏ i, √(f i) = √(∏ i, f i)` -/
private lemma prod_sqrt_eq_sqrt_prod :
    ∀ (n : ℕ) (f : Fin n → ℝ), (∀ i, 0 ≤ f i) →
    ∏ i, Real.sqrt (f i) = Real.sqrt (∏ i, f i) := by
  intro n
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    -- Split product at last element: ∏ Fin(n+1) = (∏ Fin n over castSucc) * last
    rw [Fin.prod_univ_castSucc (fun i => Real.sqrt (f i)),
        Fin.prod_univ_castSucc f]
    -- Apply IH to the prefix: ∏ √(f castSucc) = √(∏ f castSucc)
    rw [ih (fun i => f (Fin.castSucc i)) (fun i => hf (Fin.castSucc i))]
    -- Combine: √a * √b = √(a * b) using sqrt_mul with a ≥ 0
    rw [← Real.sqrt_mul
          (Finset.prod_nonneg (fun i _ => hf (Fin.castSucc i)))]

/-! ## Part 2: The Diagonal Gaussian Integral -/

/-- **Diagonal Gaussian Integral**: For positive weights b : Fin n → ℝ,
    the integral of exp(-∑ bᵢxᵢ²) over ℝⁿ equals √(πⁿ / ∏ bᵢ).

    Proof: factor exp(-∑ bᵢxᵢ²) = ∏ exp(-bᵢxᵢ²) via Real.exp_sum,
    apply Fubini (integral_fintype_prod_volume_eq_prod), evaluate each
    scalar Gaussian, then simplify the product of square roots. -/
theorem diagonal_gaussian {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) :
    ∫ x : Fin n → ℝ, Real.exp (-∑ i, b i * x i ^ 2) =
    Real.sqrt (Real.pi ^ n / ∏ i, b i) := by
  -- Step 1: Rewrite exp(-∑ bᵢxᵢ²) = ∏ i, exp(-bᵢxᵢ²) using exp_sum
  -- Strategy (following GaussianFourierTransform.lean):
  --   simp_rw [← Finset.sum_neg_distrib] : -(∑ f) → ∑ (-f) under integral
  --   simp_rw [Real.exp_sum]             : exp(∑ f) → ∏ exp(f) under integral
  simp_rw [← Finset.sum_neg_distrib, Real.exp_sum]
  -- Step 2: Apply Fubini — product integral over Fin n → ℝ factors as product of integrals
  rw [integral_fintype_prod_volume_eq_prod (fun i xi => Real.exp (-(b i * xi ^ 2)))]
  -- Step 3: Apply scalar Gaussian to each factor: ∫ exp(-bᵢxᵢ²) = √(π/bᵢ)
  have key : ∀ i : Fin n, ∫ xi : ℝ, Real.exp (-(b i * xi ^ 2)) = Real.sqrt (π / b i) :=
    fun i => GaussianIntegralCircle.scaled_gaussian (b i) (hb i)
  simp_rw [key]
  -- Step 4: Simplify ∏ √(π/bᵢ) = √(πⁿ/∏bᵢ)
  -- First: ∏ √(π/bᵢ) = √(∏(π/bᵢ)) by prod_sqrt lemma
  rw [prod_sqrt_eq_sqrt_prod n (fun i => π / b i)
        (fun i => div_nonneg pi_nonneg (hb i).le)]
  -- Then: ∏(π/bᵢ) = (∏ π)/(∏ bᵢ) = πⁿ/∏bᵢ
  congr 1
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Part 3: The Multivariate Gaussian Integral -/

/-- **Multivariate Gaussian Integral**: For a positive-definite real symmetric
    matrix A of size n×n,

        ∫ x : Fin n → ℝ, exp(-xᵀAx) = √(πⁿ / det A)

    **Proof outline**:
    1. Spectral theorem: A = U * diag(λ) * Uᵀ where U is unitary (orthogonal for ℝ)
       and all eigenvalues λᵢ > 0 (since A is positive-definite).
    2. Quadratic form: xᵀAx = (Uᵀx)ᵀ diag(λ) (Uᵀx) = ∑ᵢ λᵢ (Uᵀx)ᵢ².
    3. Change of variables y = Uᵀx: since U is orthogonal, |det Uᵀ| = 1,
       so the map y ↦ Ux is measure-preserving on (Fin n → ℝ, volume).
    4. Apply diagonal_gaussian with b = eigenvalues.
    5. det A = ∏ λᵢ by IsHermitian.det_eq_prod_eigenvalues.

    The measure-preserving change of variables uses `map_linearMap_volume_pi_eq_smul_volume_pi`
    with |det Uᵀ| = 1, together with `integral_map` to substitute y = Uᵀx. -/
theorem multivariate_gaussian_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∫ x : Fin n → ℝ, Real.exp (-(dotProduct x (A.mulVec x))) =
    Real.sqrt (Real.pi ^ n / A.det) := by
  classical
  have hS := hA.isHermitian
  -- Abbreviation: U = underlying matrix of the eigenvector unitary
  let U : Matrix (Fin n) (Fin n) ℝ := hS.eigenvectorUnitary
  -- Step 1: det A = ∏ eigenvalues
  have hdet : A.det = ∏ i, hS.eigenvalues i := by
    have h := hS.det_eq_prod_eigenvalues (𝕜 := ℝ)
    simp_rw [show ∀ x : ℝ, @RCLike.ofReal ℝ _ x = x from
      fun x => congr_fun RCLike.ofReal_real_eq_id x] at h
    exact h
  rw [hdet]
  -- Step 2: Spectral decomposition A = U * diagonal(λ) * Uᵀ
  have hA_eq : A = U * diagonal hS.eigenvalues * Uᵀ := by
    have h := hS.spectral_theorem (𝕜 := ℝ)
    simp only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at h
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  -- Quadratic form: x ⬝ᵥ A *ᵥ x = ∑ i, λᵢ * (Uᵀ *ᵥ x)ᵢ²
  have hquad : ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) =
      ∑ i, hS.eigenvalues i * (Uᵀ.mulVec x i) ^ 2 := by
    intro x
    conv_lhs => rw [hA_eq]
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec]
    -- x ᵥ* U = Uᵀ *ᵥ x  [vecMul_transpose with A := Uᵀ gives x ᵥ* (Uᵀ)ᵀ = Uᵀ *ᵥ x]
    have hvec : x ᵥ* U = Uᵀ.mulVec x := by
      have h := Matrix.vecMul_transpose Uᵀ x
      simp only [Matrix.transpose_transpose] at h; exact h
    rw [hvec]
    -- Simplify diagonal application: (Uᵀx) ⬝ᵥ (diag(λ) *ᵥ (Uᵀx)) = ∑ λᵢ (Uᵀx)ᵢ²
    simp only [dotProduct, Matrix.mulVec_diagonal]
    congr 1; ext i; ring
  simp_rw [hquad]
  -- Step 3: The map L(x) = Uᵀ *ᵥ x is measure-preserving since |det Uᵀ| = 1
  let L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Uᵀ.mulVecLin
  have hL_det : LinearMap.det L = Uᵀ.det := by
    rw [show L = Matrix.toLin' Uᵀ from (Matrix.toLin'_apply' _).symm, LinearMap.det_toLin']
  -- |det Uᵀ| = |det U| = 1 (U is unitary)
  have hL_det_abs : |Uᵀ.det| = 1 := by
    rw [Matrix.det_transpose]
    have hmem := Matrix.det_of_mem_unitary hS.eigenvectorUnitary.property
    -- hmem : det U ∈ unitary ℝ, i.e., det U * star (det U) = 1
    -- Over ℝ with TrivialStar: star (det U) = det U, so det U * det U = 1
    have h1 : U.det * U.det = 1 := by
      have h := hmem.2  -- det U * star (det U) = 1
      simp only [star_trivial] at h; exact h
    have h_sq : U.det ^ 2 = 1 := by rw [pow_two]; exact h1
    rcases sq_eq_one_iff.mp h_sq with h | h <;> simp [h]
  have hL_det_ne : LinearMap.det L ≠ 0 := by
    rw [hL_det]; intro h
    simp [h] at hL_det_abs
  -- Map volume: Measure.map L volume = volume
  have hmap : Measure.map ⇑L volume = volume := by
    rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hL_det_ne, hL_det]
    rw [show |Uᵀ.det⁻¹| = 1 by rw [abs_inv, hL_det_abs, inv_one]]
    simp
  -- Step 4: Change of variables ∫ x, f(L x) = ∫ y, f y (via integral_map + hmap)
  show ∫ x : Fin n → ℝ, Real.exp (-(∑ i, hS.eigenvalues i * (L x i) ^ 2)) =
       Real.sqrt (Real.pi ^ n / ∏ i, hS.eigenvalues i)
  -- Measurability of g = fun y => exp(-∑ λᵢ yᵢ²) under Measure.map L volume
  have hg : AEStronglyMeasurable
      (fun y : Fin n → ℝ => Real.exp (-(∑ i, hS.eigenvalues i * y i ^ 2)))
      (Measure.map ⇑L volume) := by
    rw [hmap]
    apply Continuous.aestronglyMeasurable
    fun_prop
  -- integral_map: ∫ y, g y ∂(Measure.map L vol) = ∫ x, g (L x) ∂vol
  -- ← integral_map + hmap rewrites the LHS to ∫ y, g y ∂vol
  rw [← integral_map L.continuous_of_finiteDimensional.measurable.aemeasurable hg, hmap]
  exact diagonal_gaussian hS.eigenvalues (fun i => hA.eigenvalues_pos i)

end MultivariateGaussian
