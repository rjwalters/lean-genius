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

    **Remaining sorry**: The measure-preserving change of variables
    `∫ x, f(Uᵀx) = ∫ y, f(y)` requires constructing the MeasurableEquiv
    from the orthogonal map and proving measure preservation via
    `map_linearMap_volume_pi_eq_smul_volume_pi` with |det Uᵀ| = 1. -/
theorem multivariate_gaussian_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) :
    ∫ x : Fin n → ℝ, Real.exp (-(dotProduct x (A.mulVec x))) =
    Real.sqrt (Real.pi ^ n / A.det) := by
  -- Let hAsymm := hA.isHermitian (over ℝ: IsHermitian = IsSymm)
  -- Let U = hAsymm.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ
  -- Let λ = hAsymm.eigenvalues : Fin n → ℝ, with all λᵢ > 0
  -- Spectral theorem: A = conjStarAlgAut ℝ _ U (diagonal (RCLike.ofReal ∘ λ))
  -- Key steps:
  --   (a) Rewrite xᵀAx = ∑ᵢ λᵢ ((U*ᵥx)ᵢ)² (quadratic form in eigenbasis)
  --   (b) Change variables: ∫ x, f(Uᵀ *ᵥ x) = ∫ y, f y (measure-preserving)
  --   (c) Apply diagonal_gaussian with b = eigenvalues
  --   (d) Use det A = ∏ eigenvalues
  --
  -- SORRY: spectral decomposition + orthogonal change of variables
  -- Needed:
  --   · hAsymm.spectral_theorem (A = U * diag(λ) * U*)
  --   · Matrix.PosDef.eigenvalues_pos (all λᵢ > 0)
  --   · Matrix.IsHermitian.det_eq_prod_eigenvalues (det A = ∏ λᵢ, cast to ℝ)
  --   · map_linearMap_volume_pi_eq_smul_volume_pi with |det U| = 1
  --   · MeasurePreserving.integral_comp' to rewrite the integral
  sorry

end MultivariateGaussian
