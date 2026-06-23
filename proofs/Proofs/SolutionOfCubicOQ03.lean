import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-
# OQ-03: Vieta's Formulas for the Cubic via Cardano's Roots

Proves that the three Cardano roots of the depressed cubic x³ + px + q = 0
satisfy Vieta's formulas:
  x₁ + x₂ + x₃ = 0
  x₁x₂ + x₁x₃ + x₂x₃ = p
  x₁x₂x₃ = -q

where the roots are:
  x₁ = u + v,   x₂ = ωu + ω²v,   x₃ = ω²u + ωv
with u³ + v³ = -q, uv = -p/3, and ω = e^{2πi/3}.

This connects Cardano's explicit radical formula (parent proof) to the
fundamental theorem on symmetric polynomials, and proves the depressed cubic
factors as (x - x₁)(x - x₂)(x - x₃).
-/

set_option linter.unusedVariables false

namespace SolutionOfCubicOQ03

open Complex Polynomial

-- ============================================================
-- SECTION I: Cube Root of Unity
-- ============================================================

/-- The primitive cube root of unity ω = e^(2πi/3) -/
noncomputable def ω : ℂ := exp (2 * Real.pi * I / 3)

/-- ω³ = 1 -/
theorem omega_cubed : ω ^ 3 = 1 := by
  unfold ω
  rw [← exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have h : 3 * (2 * ↑Real.pi * I / 3) = 2 * ↑Real.pi * I := by ring
  rw [h, exp_two_pi_mul_I]

/-- ω ≠ 1 -/
theorem omega_ne_one : ω ≠ 1 := by
  unfold ω
  intro heq
  have him : (exp (2 * ↑Real.pi * I / 3)).im = Real.sin (2 * Real.pi / 3) := by
    have h1 : 2 * ↑Real.pi * I / 3 = (2 * Real.pi / 3 : ℝ) * I := by
      simp only [ofReal_div, ofReal_mul, ofReal_ofNat]; ring
    rw [h1, exp_mul_I]
    simp only [add_im, mul_im, cos_ofReal_im, sin_ofReal_re, mul_zero,
      sin_ofReal_im, add_zero, I_im, I_re, mul_one, mul_zero, add_zero, zero_add]
  rw [heq, one_im] at him
  have hsin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
        Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hsin] at him
  exact (by positivity : Real.sqrt 3 / 2 ≠ 0) him.symm

/-- 1 + ω + ω² = 0 -/
theorem omega_sum : 1 + ω + ω ^ 2 = 0 := by
  have h : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
  have h0 : ω ^ 3 - 1 = 0 := by rw [omega_cubed]; ring
  rw [h] at h0
  cases mul_eq_zero.mp h0 with
  | inl h1 => exact absurd (sub_eq_zero.mp h1) omega_ne_one
  | inr h2 => linear_combination h2

/-- ω² + ω = -1 -/
theorem omega_sq_add_omega : ω ^ 2 + ω = -1 := by
  linear_combination omega_sum

/-- ω⁴ = ω -/
theorem omega_pow_four : ω ^ 4 = ω := by
  have : ω ^ 4 = ω ^ 3 * ω := by ring
  rw [this, omega_cubed, one_mul]

-- ============================================================
-- SECTION II: The Three Cardano Roots
-- ============================================================

/-- First root: x₁ = u + v -/
noncomputable def root₁ (u v : ℂ) : ℂ := u + v

/-- Second root: x₂ = ωu + ω²v -/
noncomputable def root₂ (u v : ℂ) : ℂ := ω * u + ω ^ 2 * v

/-- Third root: x₃ = ω²u + ωv -/
noncomputable def root₃ (u v : ℂ) : ℂ := ω ^ 2 * u + ω * v

-- ============================================================
-- SECTION III: Vieta I — Sum of Roots
-- ============================================================

/-- **Vieta's First Formula**: x₁ + x₂ + x₃ = 0

For the depressed cubic x³ + px + q = 0 (no x² term), the sum of roots
vanishes. This follows immediately from 1 + ω + ω² = 0. -/
theorem vieta_sum (u v : ℂ) :
    root₁ u v + root₂ u v + root₃ u v = 0 := by
  unfold root₁ root₂ root₃
  linear_combination u * omega_sum + v * omega_sum

-- ============================================================
-- SECTION IV: Vieta II — Sum of Pairwise Products
-- ============================================================

/-- **Vieta's Second Formula**: x₁x₂ + x₁x₃ + x₂x₃ = p

The symmetric sum of pairwise products equals p, the linear coefficient.
Expanding and using ω³ = 1, ω⁴ = ω gives coefficient (1+ω+ω²) = 0 for
u² and v² terms, and -3 for the uv term. With uv = -p/3, this gives p. -/
theorem vieta_pairs (u v p : ℂ) (h_prod : u * v = -p / 3) :
    root₁ u v * root₂ u v + root₁ u v * root₃ u v + root₂ u v * root₃ u v = p := by
  unfold root₁ root₂ root₃
  suffices h : (u + v) * (ω * u + ω ^ 2 * v) + (u + v) * (ω ^ 2 * u + ω * v) +
    (ω * u + ω ^ 2 * v) * (ω ^ 2 * u + ω * v) = -3 * (u * v) by
    rw [h, h_prod]; ring
  -- Expand to polynomial in ω, collecting u², uv, v² coefficients
  have expand : (u + v) * (ω * u + ω ^ 2 * v) + (u + v) * (ω ^ 2 * u + ω * v) +
    (ω * u + ω ^ 2 * v) * (ω ^ 2 * u + ω * v) =
    (ω + ω ^ 2 + ω ^ 3) * u ^ 2 + (2 * ω + 3 * ω ^ 2 + ω ^ 4) * (u * v) +
    (ω + ω ^ 2 + ω ^ 3) * v ^ 2 := by ring
  rw [expand, omega_cubed, omega_pow_four]
  -- (ω + ω² + 1) * u² + (3ω + 3ω²) * (u*v) + (ω + ω² + 1) * v² = -3 * (u*v)
  linear_combination u ^ 2 * omega_sum + v ^ 2 * omega_sum + 3 * (u * v) * omega_sum

-- ============================================================
-- SECTION V: Vieta III — Product of All Roots
-- ============================================================

/-- **Vieta's Third Formula**: x₁x₂x₃ = -q

The product of all three Cardano roots equals -q, the negation of the
constant term. The cross-terms (u²v and uv²) vanish by 1 + ω + ω² = 0,
and the remaining ω³(u³ + v³) = u³ + v³ = -q. -/
theorem vieta_product (u v q : ℂ) (h_sum : u ^ 3 + v ^ 3 = -q) :
    root₁ u v * root₂ u v * root₃ u v = -q := by
  unfold root₁ root₂ root₃
  -- Expand the triple product
  have expand : (u + v) * (ω * u + ω ^ 2 * v) * (ω ^ 2 * u + ω * v) =
    ω ^ 3 * u ^ 3 + (ω ^ 2 + ω ^ 3 + ω ^ 4) * (u ^ 2 * v) +
    (ω ^ 2 + ω ^ 3 + ω ^ 4) * (u * v ^ 2) + ω ^ 3 * v ^ 3 := by ring
  rw [expand, omega_cubed, omega_pow_four]
  -- 1 * u³ + (ω² + 1 + ω) * (u²v) + (ω² + 1 + ω) * (uv²) + 1 * v³ = -q
  linear_combination u ^ 2 * v * omega_sum + u * v ^ 2 * omega_sum + h_sum

-- ============================================================
-- SECTION VI: Polynomial Factorization
-- ============================================================

/-- **Cubic Factorization**: x³ + px + q = (x - x₁)(x - x₂)(x - x₃)

The depressed cubic factors completely over ℂ into linear factors at the
three Cardano roots. Combines all three Vieta formulas with the general
expansion (x-r₁)(x-r₂)(x-r₃) = x³ - σ₁x² + σ₂x - σ₃. -/
theorem cubic_factorization (u v p q : ℂ)
    (h_sum : u ^ 3 + v ^ 3 = -q) (h_prod : u * v = -p / 3) (x : ℂ) :
    x ^ 3 + p * x + q =
    (x - root₁ u v) * (x - root₂ u v) * (x - root₃ u v) := by
  have hv1 := vieta_sum u v
  have hv2 := vieta_pairs u v p h_prod
  have hv3 := vieta_product u v q h_sum
  have expand : (x - root₁ u v) * (x - root₂ u v) * (x - root₃ u v) =
    x ^ 3 - (root₁ u v + root₂ u v + root₃ u v) * x ^ 2 +
    (root₁ u v * root₂ u v + root₁ u v * root₃ u v + root₂ u v * root₃ u v) * x -
    root₁ u v * root₂ u v * root₃ u v := by ring
  rw [expand, hv1, hv2, hv3]; ring

-- ============================================================
-- SECTION VII: Each Root Satisfies the Cubic
-- ============================================================

/-- All three roots satisfy the depressed cubic x³ + px + q = 0 -/
theorem all_roots_satisfy (u v p q : ℂ)
    (h_sum : u ^ 3 + v ^ 3 = -q) (h_prod : u * v = -p / 3) :
    (root₁ u v) ^ 3 + p * root₁ u v + q = 0 ∧
    (root₂ u v) ^ 3 + p * root₂ u v + q = 0 ∧
    (root₃ u v) ^ 3 + p * root₃ u v + q = 0 := by
  have hfact₁ := cubic_factorization u v p q h_sum h_prod (root₁ u v)
  have hfact₂ := cubic_factorization u v p q h_sum h_prod (root₂ u v)
  have hfact₃ := cubic_factorization u v p q h_sum h_prod (root₃ u v)
  exact ⟨by rw [hfact₁]; ring, by rw [hfact₂]; ring, by rw [hfact₃]; ring⟩

end SolutionOfCubicOQ03
