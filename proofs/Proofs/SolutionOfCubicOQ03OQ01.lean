/-
  Discriminant of the Depressed Cubic

  For the depressed cubic x³ + px + q = 0 with roots x₁, x₂, x₃,
  the discriminant Δ = -4p³ - 27q² equals (x₁-x₂)²(x₁-x₃)²(x₂-x₃)².

  This connects the coefficient-based discriminant formula to the
  root-separation interpretation, and determines the nature of the roots:
  - Δ > 0: three distinct real roots
  - Δ = 0: repeated root
  - Δ < 0: one real root and two complex conjugate roots
-/
import Mathlib

namespace CubicDiscriminant

variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Discriminant Definition
-- ============================================================

/-- The discriminant of the depressed cubic x³ + px + q. -/
def discriminant (p q : R) : R := -4 * p ^ 3 - 27 * q ^ 2

/-- The root-separation form of the discriminant. -/
def rootDiscriminant (x₁ x₂ x₃ : R) : R :=
  (x₁ - x₂) ^ 2 * (x₁ - x₃) ^ 2 * (x₂ - x₃) ^ 2

-- ============================================================
-- SECTION II: Vieta's Formulas for Depressed Cubic
-- ============================================================

/-- Vieta's formulas for the depressed cubic x³ + px + q = 0:
    x₁ + x₂ + x₃ = 0, x₁x₂ + x₁x₃ + x₂x₃ = p, x₁x₂x₃ = -q. -/
structure IsRootTriple (p q : R) (x₁ x₂ x₃ : R) : Prop where
  sum_zero : x₁ + x₂ + x₃ = 0
  sum_products : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = p
  product : x₁ * x₂ * x₃ = -q

-- ============================================================
-- SECTION III: Main Theorem
-- ============================================================

/-- The discriminant equals the root-separation product:
    -4p³ - 27q² = (x₁-x₂)²(x₁-x₃)²(x₂-x₃)²
    when x₁, x₂, x₃ are roots satisfying Vieta's formulas. -/
theorem discriminant_eq_root_form (p q x₁ x₂ x₃ : R)
    (h : IsRootTriple p q x₁ x₂ x₃) :
    discriminant p q = rootDiscriminant x₁ x₂ x₃ := by
  unfold discriminant rootDiscriminant
  -- Substitute p = x₁x₂ + x₁x₃ + x₂x₃ and q = -(x₁x₂x₃)
  -- using x₁ + x₂ + x₃ = 0, then verify by ring
  rw [← h.sum_products, ← show q = -(x₁ * x₂ * x₃) from by linarith [h.product]]
  -- With x₃ = -(x₁ + x₂) from sum_zero:
  have hx₃ : x₃ = -(x₁ + x₂) := by linarith [h.sum_zero]
  rw [hx₃]
  ring

-- ============================================================
-- SECTION IV: Sign Determines Root Nature (over ℝ)
-- ============================================================

/-- When Δ > 0 over ℝ, all three root differences are nonzero,
    meaning all roots are distinct. -/
theorem distinct_roots_of_pos_discriminant (p q x₁ x₂ x₃ : ℝ)
    (h : IsRootTriple p q x₁ x₂ x₃)
    (hΔ : discriminant p q > 0) :
    x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  rw [discriminant_eq_root_form p q x₁ x₂ x₃ h] at hΔ
  unfold rootDiscriminant at hΔ
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> simp [heq] at hΔ

/-- When Δ = 0, at least two roots coincide. -/
theorem repeated_root_of_zero_discriminant (p q x₁ x₂ x₃ : ℝ)
    (h : IsRootTriple p q x₁ x₂ x₃)
    (hΔ : discriminant p q = 0) :
    x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  rw [discriminant_eq_root_form p q x₁ x₂ x₃ h] at hΔ
  unfold rootDiscriminant at hΔ
  by_contra h_all_ne
  push_neg at h_all_ne
  obtain ⟨h12, h13, h23⟩ := h_all_ne
  have h1 : (x₁ - x₂) ^ 2 > 0 := by positivity
  have h2 : (x₁ - x₃) ^ 2 > 0 := by positivity
  have h3 : (x₂ - x₃) ^ 2 > 0 := by positivity
  linarith [mul_pos (mul_pos h1 h2) h3]

end CubicDiscriminant
