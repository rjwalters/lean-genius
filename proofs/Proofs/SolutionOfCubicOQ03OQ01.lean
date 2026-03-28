import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-
# OQ-03-OQ-01: Discriminant of the Depressed Cubic

Formalizes the discriminant Δ = -4p³ - 27q² of the depressed cubic x³ + px + q = 0
and proves it equals the squared product of root differences:
  Δ = (x₁ - x₂)²(x₁ - x₃)²(x₂ - x₃)²

This relates root separation (how far apart the roots are) to coefficient data
(p and q), which is fundamental for:
- Determining when roots are real vs complex
- Computing the nature of singularities
- The Galois group of the cubic

The proof uses the Cardano root expressions and cube root of unity ω.
-/

set_option linter.unusedVariables false

namespace SolutionOfCubicOQ03OQ01

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

/-- ω⁴ = ω -/
theorem omega_pow_four : ω ^ 4 = ω := by
  have : ω ^ 4 = ω ^ 3 * ω := by ring
  rw [this, omega_cubed, one_mul]

-- ============================================================
-- SECTION II: Root Definitions
-- ============================================================

/-- First Cardano root: x₁ = u + v -/
noncomputable def root₁ (u v : ℂ) : ℂ := u + v

/-- Second Cardano root: x₂ = ωu + ω²v -/
noncomputable def root₂ (u v : ℂ) : ℂ := ω * u + ω ^ 2 * v

/-- Third Cardano root: x₃ = ω²u + ωv -/
noncomputable def root₃ (u v : ℂ) : ℂ := ω ^ 2 * u + ω * v

-- ============================================================
-- SECTION III: Discriminant Definitions
-- ============================================================

/-- **Discriminant via coefficients**: Δ = -4p³ - 27q² for the depressed cubic x³ + px + q -/
def discriminant_coeff (p q : ℂ) : ℂ := -4 * p ^ 3 - 27 * q ^ 2

/-- **Discriminant via roots**: Δ = ∏ᵢ<ⱼ (xᵢ - xⱼ)² -/
def discriminant_roots (x₁ x₂ x₃ : ℂ) : ℂ :=
  (x₁ - x₂) ^ 2 * (x₁ - x₃) ^ 2 * (x₂ - x₃) ^ 2

-- ============================================================
-- SECTION IV: Key Omega Identities
-- ============================================================

/-- (1 - ω)(1 - ω²) = 3 -/
theorem one_sub_omega_prod : (1 - ω) * (1 - ω ^ 2) = 3 := by
  have expand : (1 - ω) * (1 - ω ^ 2) = 1 - ω - ω ^ 2 + ω ^ 3 := by ring
  rw [expand, omega_cubed]
  linear_combination -omega_sum

/-- (ω - ω²)² = -3 -/
theorem omega_diff_sq : (ω - ω ^ 2) ^ 2 = -3 := by
  have expand : (ω - ω ^ 2) ^ 2 = ω ^ 2 - 2 * ω ^ 3 + ω ^ 4 := by ring
  rw [expand, omega_cubed, omega_pow_four]
  linear_combination omega_sum

-- ============================================================
-- SECTION V: Root Difference Expressions
-- ============================================================

/-- x₁ - x₂ = (1-ω)u + (1-ω²)v -/
theorem root_diff_12 (u v : ℂ) :
    root₁ u v - root₂ u v = (1 - ω) * u + (1 - ω ^ 2) * v := by
  unfold root₁ root₂; ring

/-- x₁ - x₃ = (1-ω²)u + (1-ω)v -/
theorem root_diff_13 (u v : ℂ) :
    root₁ u v - root₃ u v = (1 - ω ^ 2) * u + (1 - ω) * v := by
  unfold root₁ root₃; ring

/-- x₂ - x₃ = (ω - ω²)(u - v) -/
theorem root_diff_23 (u v : ℂ) :
    root₂ u v - root₃ u v = (ω - ω ^ 2) * (u - v) := by
  unfold root₂ root₃; ring

-- ============================================================
-- SECTION VI: Product of (x₁-x₂)(x₁-x₃)
-- ============================================================

/-- (x₁-x₂)(x₁-x₃) = 3(u² + uv + v²)

The cross terms involve (1-ω)² + (1-ω²)², which equals 3,
and (1-ω)(1-ω²) = 3. -/
theorem root_diff_12_times_13 (u v : ℂ) :
    (root₁ u v - root₂ u v) * (root₁ u v - root₃ u v) =
    3 * (u ^ 2 + u * v + v ^ 2) := by
  rw [root_diff_12, root_diff_13]
  -- Expand to polynomial in ω
  have expand :
    ((1 - ω) * u + (1 - ω ^ 2) * v) * ((1 - ω ^ 2) * u + (1 - ω) * v) =
    (1 - ω) * (1 - ω ^ 2) * u ^ 2 +
    ((1 - ω) ^ 2 + (1 - ω ^ 2) ^ 2) * (u * v) +
    (1 - ω) * (1 - ω ^ 2) * v ^ 2 := by ring
  rw [expand, one_sub_omega_prod]
  -- Need (1-ω)² + (1-ω²)² = 3
  have sum_sq : (1 - ω) ^ 2 + (1 - ω ^ 2) ^ 2 = 3 := by
    have expand2 : (1 - ω) ^ 2 + (1 - ω ^ 2) ^ 2 =
      2 - 2 * ω - 2 * ω ^ 2 + ω ^ 2 + ω ^ 4 := by ring
    rw [expand2, omega_pow_four]
    linear_combination -2 * omega_sum
  rw [sum_sq]; ring

-- ============================================================
-- SECTION VII: Main Discriminant Identity
-- ============================================================

/-- **Discriminant equals -27(u³ - v³)²**

The full squared product of root differences equals -27(u³ - v³)²,
derived from the root difference formulas and omega identities. -/
theorem discriminant_in_uv (u v : ℂ) :
    discriminant_roots (root₁ u v) (root₂ u v) (root₃ u v) =
    -27 * (u ^ 3 - v ^ 3) ^ 2 := by
  unfold discriminant_roots
  have h12_13 := root_diff_12_times_13 u v
  have h23 := root_diff_23 u v
  -- Factor (x₁-x₂)²(x₁-x₃)² = [(x₁-x₂)(x₁-x₃)]² = [3(u²+uv+v²)]²
  have step1 : (root₁ u v - root₂ u v) ^ 2 * (root₁ u v - root₃ u v) ^ 2 =
    (3 * (u ^ 2 + u * v + v ^ 2)) ^ 2 := by
    have : (root₁ u v - root₂ u v) ^ 2 * (root₁ u v - root₃ u v) ^ 2 =
      ((root₁ u v - root₂ u v) * (root₁ u v - root₃ u v)) ^ 2 := by ring
    rw [this, h12_13]
  -- Factor (x₂-x₃)² = (ω-ω²)²(u-v)² = -3(u-v)²
  have step2 : (root₂ u v - root₃ u v) ^ 2 = -3 * (u - v) ^ 2 := by
    rw [h23]
    have : ((ω - ω ^ 2) * (u - v)) ^ 2 = (ω - ω ^ 2) ^ 2 * (u - v) ^ 2 := by ring
    rw [this, omega_diff_sq]; ring
  -- Combine: [3(u²+uv+v²)]² · [-3(u-v)²] = -27[(u²+uv+v²)(u-v)]² = -27(u³-v³)²
  rw [step1, step2]
  rw [show (3 * (u ^ 2 + u * v + v ^ 2)) ^ 2 * (-3 * (u - v) ^ 2) =
    -27 * ((u ^ 2 + u * v + v ^ 2) * (u - v)) ^ 2 from by ring]
  rw [show (u ^ 2 + u * v + v ^ 2) * (u - v) = u ^ 3 - v ^ 3 from by ring]

/-- **u³ - v³ squared in terms of p, q**

(u³ - v³)² = (u³+v³)² - 4(uv)³ = q² + 4p³/27 -/
theorem uv_diff_cubed_sq (u v p q : ℂ) (h_sum : u ^ 3 + v ^ 3 = -q)
    (h_prod : u * v = -p / 3) :
    (u ^ 3 - v ^ 3) ^ 2 = q ^ 2 + 4 * p ^ 3 / 27 := by
  -- (u³-v³)² = (u³+v³)² - 4u³v³
  have key : (u ^ 3 - v ^ 3) ^ 2 = (u ^ 3 + v ^ 3) ^ 2 - 4 * (u * v) ^ 3 := by ring
  rw [key, h_sum, h_prod]; ring

/-- **Main Theorem: Discriminant Identity**

For the depressed cubic x³ + px + q = 0 with Cardano roots
x₁ = u+v, x₂ = ωu+ω²v, x₃ = ω²u+ωv where u³+v³ = -q and uv = -p/3:

  (x₁-x₂)²(x₁-x₃)²(x₂-x₃)² = -4p³ - 27q²

This connects the geometric separation of roots to the algebraic discriminant. -/
theorem discriminant_identity (u v p q : ℂ)
    (h_sum : u ^ 3 + v ^ 3 = -q) (h_prod : u * v = -p / 3) :
    discriminant_roots (root₁ u v) (root₂ u v) (root₃ u v) =
    discriminant_coeff p q := by
  rw [discriminant_in_uv, uv_diff_cubed_sq u v p q h_sum h_prod]
  unfold discriminant_coeff; ring

-- ============================================================
-- SECTION VIII: Consequences
-- ============================================================

/-- Δ > 0 implies (u³-v³)² < 0, which is impossible over ℝ — all three roots
    are distinct. Over ℂ this means the squared root product is positive. -/
theorem discriminant_positive_iff (u v : ℂ) (hΔ : discriminant_roots (root₁ u v) (root₂ u v) (root₃ u v) ≠ 0) :
    root₁ u v ≠ root₂ u v ∧ root₁ u v ≠ root₃ u v ∧ root₂ u v ≠ root₃ u v := by
  unfold discriminant_roots at hΔ
  constructor
  · intro h; apply hΔ; rw [h]; ring
  constructor
  · intro h; apply hΔ; rw [h]; ring
  · intro h; apply hΔ; rw [h]; ring

/-- When Δ = 0, at least two roots coincide. -/
theorem discriminant_zero_repeated (u v : ℂ)
    (hΔ : discriminant_roots (root₁ u v) (root₂ u v) (root₃ u v) = 0) :
    root₁ u v = root₂ u v ∨ root₁ u v = root₃ u v ∨ root₂ u v = root₃ u v := by
  unfold discriminant_roots at hΔ
  rcases mul_eq_zero.mp hΔ with h | h
  · rcases mul_eq_zero.mp h with h1 | h2
    · left; exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0).mp h1)
    · right; left; exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0).mp h2)
  · right; right; exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0).mp h)

end SolutionOfCubicOQ03OQ01
