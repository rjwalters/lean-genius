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

## Status
- `prod_sqrt_eq_sqrt_prod` : proved (induction on n)
- `diagonal_gaussian` : proved (Fubini + scalar Gaussian)
- `multivariate_gaussian_integral` : 1 sorry (spectral change of variables)

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

    **Proof outline** (1 sorry remaining):
    1. Spectral theorem: A = U * diag(λ) * Uᵀ where U is unitary (orthogonal for ℝ)
       and all eigenvalues λᵢ > 0 (since A is positive-definite).
    2. Quadratic form: xᵀAx = (Uᵀx)ᵀ diag(λ) (Uᵀx) = ∑ᵢ λᵢ (Uᵀx)ᵢ².
    3. Change of variables y = Uᵀx: since U is orthogonal, |det Uᵀ| = 1,
       so the map y ↦ Ux is measure-preserving on (Fin n → ℝ, volume).
    4. Apply diagonal_gaussian with b = eigenvalues.
    5. det A = ∏ λᵢ by IsHermitian.det_eq_prod_eigenvalues.

    **Proof structure** (1 sorry remaining):
    - `hquad` sorry: matrix algebra using `IsHermitian.spectral_theorem` +
      `dotProduct_mulVec` + `mulVec_diagonal` (HARD — Aristotle candidate).
    All other steps are proved: unitary det = ±1, measure-preserving change of
    variables via `map_matrix_volume_pi_eq_smul_volume_pi`, and `diagonal_gaussian`. -/
theorem multivariate_gaussian_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∫ x : Fin n → ℝ, Real.exp (-(dotProduct x (A.mulVec x))) =
    Real.sqrt (Real.pi ^ n / A.det) := by
  classical
  -- Extract the IsHermitian structure
  have hH := hA.isHermitian
  -- Step 1: All eigenvalues are strictly positive
  have heig_pos : ∀ i : Fin n, 0 < hH.eigenvalues i :=
    fun i => Matrix.PosDef.eigenvalues_pos hA i
  -- Step 2: det A = product of eigenvalues
  -- det_eq_prod_eigenvalues gives ∏ (eigenvalues i : 𝕜) and for 𝕜=ℝ cast is identity
  have hdet : A.det = ∏ i : Fin n, hH.eigenvalues i := by
    simpa using hH.det_eq_prod_eigenvalues (𝕜 := ℝ)
  -- Step 3: Conjugate transpose (= transpose for ℝ) of the eigenvector unitary
  set UT : Matrix (Fin n) (Fin n) ℝ :=
    star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hUT_def
  -- Step 4: Quadratic form in the eigenbasis: x^T A x = ∑ᵢ λᵢ (Uᵀx)ᵢ²
  -- Proof: A = U * diag(λ) * star U (spectral theorem), then
  --   x ⬝ᵥ A *ᵥ x = x ⬝ᵥ (U *ᵥ (diag(λ) *ᵥ (UT *ᵥ x)))
  --   = (UT *ᵥ x) ⬝ᵥ (diag(λ) *ᵥ (UT *ᵥ x))   (dotProduct_mulVec + U orthogonal)
  --   = ∑ᵢ λᵢ * (UT *ᵥ x)ᵢ²                      (mulVec_diagonal)
  have hquad : ∀ x : Fin n → ℝ,
      dotProduct x (A.mulVec x) = ∑ i : Fin n, hH.eigenvalues i * (UT *ᵥ x) i ^ 2 := by
    intro x
    -- HARD: A = conjStarAlgAut ℝ _ hH.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ λ))
    -- = U * diag(λ) * star U. Use dotProduct_mulVec, mulVec_mulVec, mulVec_diagonal.
    sorry
  -- Step 5: Rewrite integrand in terms of eigenbasis coordinates
  simp_rw [hquad]
  -- Step 6: |det UT| = 1 since U is unitary
  -- Proof: det(UT) = det(Uᴴ) = star(det U) = det U for ℝ (TrivialStar).
  -- U ∈ unitaryGroup → det U ∈ unitary ℝ → (star(det U)) * det U = 1
  -- → (det U)^2 = 1 → det U = ±1 → |det U| = 1.
  have habs : |UT.det| = 1 := by
    -- UT.det = U.det (star = conjTranspose = transpose for ℝ, det Mᴴ = star(det M) = det M)
    have hUT_det_eq : UT.det = (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det := by
      simp only [hUT_def, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, star_trivial]
    rw [hUT_det_eq]
    -- U ∈ unitaryGroup n ℝ → det U ∈ unitary ℝ
    have hmem : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.unitaryGroup (Fin n) ℝ := (hH.eigenvectorUnitary).property
    have hdet_mem := Matrix.det_of_mem_unitary hmem
    -- star(det U) * det U = 1, and star(det U) = det U for ℝ, so (det U)^2 = 1
    have hsq : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det ^ 2 = 1 := by
      have h := (Unitary.mem_iff.mp hdet_mem).1  -- star (det U) * det U = 1
      simpa [star_trivial, ← sq] using h
    -- det U = ±1 → |det U| = 1
    have hpm : (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det = 1 ∨
               (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det = -1 := by
      have hfact : ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det - 1) *
                   ((hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).det + 1) = 0 := by
        nlinarith [hsq]
      rcases mul_eq_zero.mp hfact with h | h
      · left; linarith
      · right; linarith
    rcases hpm with h | h <;> simp [h]
  -- Step 7: The map x ↦ UT *ᵥ x preserves Lebesgue measure
  have hUT_det_ne : UT.det ≠ 0 := by
    intro h; simp [h] at habs
  have hmap : Measure.map (Matrix.toLin' UT) volume = volume := by
    rw [map_matrix_volume_pi_eq_smul_volume_pi hUT_det_ne]
    simp only [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_smul]
  -- Step 8: Change of variables y = UT *ᵥ x (measure-preserving)
  -- integral_map: ∫ y, f y ∂(map φ μ) = ∫ x, f(φ x) ∂μ
  -- With hmap: ∫ y, f y = ∫ x, f((toLin' UT) x) = ∫ x, f(UT *ᵥ x)
  have hcov : ∫ x : Fin n → ℝ, Real.exp (-∑ i : Fin n, hH.eigenvalues i * (UT *ᵥ x) i ^ 2) =
      ∫ y : Fin n → ℝ, Real.exp (-∑ i : Fin n, hH.eigenvalues i * y i ^ 2) := by
    have hφ : AEMeasurable (Matrix.toLin' UT) volume :=
      (LinearMap.continuous_on_pi _).measurable.aemeasurable
    have hfm : AEStronglyMeasurable
        (fun y : Fin n → ℝ => Real.exp (-∑ i : Fin n, hH.eigenvalues i * y i ^ 2))
        (Measure.map (Matrix.toLin' UT) volume) := by
      rw [hmap]; exact (continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have key := (integral_map hφ hfm).symm
    simp only [Matrix.toLin'_apply] at key
    rw [hmap] at key
    exact key
  -- Step 9: Apply diagonal_gaussian and connect det to eigenvalues
  rw [hcov, diagonal_gaussian hH.eigenvalues heig_pos, ← hdet]

end MultivariateGaussian
