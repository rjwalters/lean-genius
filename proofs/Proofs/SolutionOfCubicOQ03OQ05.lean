/-
  Vieta's Formulas for the General Cubic

  For the general (non-depressed) cubic x³ + ax² + bx + c = 0 with roots
  r₁, r₂, r₃ in a commutative ring R, Vieta's formulas state:

    σ₁ = r₁ + r₂ + r₃ = -a
    σ₂ = r₁r₂ + r₁r₃ + r₂r₃ = b
    σ₃ = r₁r₂r₃ = -c

  These are proved by direct expansion of (x - r₁)(x - r₂)(x - r₃) and
  comparing coefficients with x³ + ax² + bx + c.

  This extends the depressed cubic Vieta's (OQ-03) to the general case.
-/
import Mathlib

namespace VietaCubic

variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Expansion of Product of Linear Factors
-- ============================================================

/-- Expanding (x - r₁)(x - r₂)(x - r₃) gives
    x³ - (r₁+r₂+r₃)x² + (r₁r₂+r₁r₃+r₂r₃)x - r₁r₂r₃ -/
theorem cubic_factor_expansion (r₁ r₂ r₃ : R) :
    (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
    (Polynomial.X - Polynomial.C r₃) =
    Polynomial.X ^ 3 -
    Polynomial.C (r₁ + r₂ + r₃) * Polynomial.X ^ 2 +
    Polynomial.C (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) * Polynomial.X -
    Polynomial.C (r₁ * r₂ * r₃) := by
  ring

-- ============================================================
-- SECTION II: Vieta's Formulas (Coefficient Matching)
-- ============================================================

/-- If x³ + ax² + bx + c = (x - r₁)(x - r₂)(x - r₃), then a = -(r₁+r₂+r₃). -/
theorem vieta_sigma1 (a b c r₁ r₂ r₃ : R)
    (h : Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
         Polynomial.C b * Polynomial.X + Polynomial.C c =
         (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
         (Polynomial.X - Polynomial.C r₃)) :
    a = -(r₁ + r₂ + r₃) := by
  rw [cubic_factor_expansion] at h
  have := congr_arg (fun p => Polynomial.coeff p 2) h
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_mul,
        Polynomial.coeff_sub, Polynomial.coeff_add] at this
  linarith

/-- If x³ + ax² + bx + c = (x - r₁)(x - r₂)(x - r₃), then b = r₁r₂+r₁r₃+r₂r₃. -/
theorem vieta_sigma2 (a b c r₁ r₂ r₃ : R)
    (h : Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
         Polynomial.C b * Polynomial.X + Polynomial.C c =
         (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
         (Polynomial.X - Polynomial.C r₃)) :
    b = r₁ * r₂ + r₁ * r₃ + r₂ * r₃ := by
  rw [cubic_factor_expansion] at h
  have := congr_arg (fun p => Polynomial.coeff p 1) h
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_mul,
        Polynomial.coeff_sub, Polynomial.coeff_add] at this
  linarith

/-- If x³ + ax² + bx + c = (x - r₁)(x - r₂)(x - r₃), then c = -r₁r₂r₃. -/
theorem vieta_sigma3 (a b c r₁ r₂ r₃ : R)
    (h : Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
         Polynomial.C b * Polynomial.X + Polynomial.C c =
         (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
         (Polynomial.X - Polynomial.C r₃)) :
    c = -(r₁ * r₂ * r₃) := by
  rw [cubic_factor_expansion] at h
  have := congr_arg (fun p => Polynomial.coeff p 0) h
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_mul,
        Polynomial.coeff_sub, Polynomial.coeff_add] at this
  linarith

-- ============================================================
-- SECTION III: Combined Vieta's Formulas
-- ============================================================

/-- Vieta's formulas for the general cubic: all three relations at once. -/
theorem vieta_cubic (a b c r₁ r₂ r₃ : R)
    (h : Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
         Polynomial.C b * Polynomial.X + Polynomial.C c =
         (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
         (Polynomial.X - Polynomial.C r₃)) :
    a = -(r₁ + r₂ + r₃) ∧
    b = r₁ * r₂ + r₁ * r₃ + r₂ * r₃ ∧
    c = -(r₁ * r₂ * r₃) :=
  ⟨vieta_sigma1 a b c r₁ r₂ r₃ h,
   vieta_sigma2 a b c r₁ r₂ r₃ h,
   vieta_sigma3 a b c r₁ r₂ r₃ h⟩

-- ============================================================
-- SECTION IV: Converse — Roots Satisfy the Polynomial
-- ============================================================

/-- Each root rᵢ satisfies x³ + ax² + bx + c = 0 when the polynomial factors. -/
theorem root_satisfies (a b c r₁ r₂ r₃ : R)
    (h : Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
         Polynomial.C b * Polynomial.X + Polynomial.C c =
         (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) *
         (Polynomial.X - Polynomial.C r₃)) :
    Polynomial.eval r₁ (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c) = 0 := by
  rw [h]
  simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

end VietaCubic
