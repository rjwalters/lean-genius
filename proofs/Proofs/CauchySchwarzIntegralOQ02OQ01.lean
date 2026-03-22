/-
# Strict Minkowski Inequality: Equality iff Proportional

Equality in Minkowski (‖f+g‖ = ‖f‖+‖g‖) holds iff f, g are
non-negatively proportional: ‖f‖•g = ‖g‖•f.

Proof: equality ⟺ ⟪f,g⟫ = ‖f‖·‖g‖ (C-S equality) ⟺ ‖‖f‖•g - ‖g‖•f‖ = 0.
-/
import Mathlib

set_option linter.unusedVariables false

namespace StrictMinkowski

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ============================================================
-- SECTION I: Key Algebraic Facts
-- ============================================================

/-- Inner product with proportional vectors: if ‖f‖•g = ‖g‖•f then ⟪f,g⟫ = ‖f‖·‖g‖. -/
theorem inner_eq_of_proportional (f g : E) (h : ‖f‖ • g = ‖g‖ • f) :
    ⟪f, g⟫_ℝ = ‖f‖ * ‖g‖ := by
  by_cases hf : f = 0
  · simp [hf]
  · -- Apply ⟪f, ·⟫ to both sides: ‖f‖⟪f,g⟫ = ‖g‖⟪f,f⟫ = ‖g‖·‖f‖²
    have h1 : ⟪f, ‖f‖ • g⟫_ℝ = ⟪f, ‖g‖ • f⟫_ℝ := by rw [h]
    simp only [real_inner_smul_right] at h1
    rw [real_inner_self_eq_norm_sq] at h1
    -- h1: ‖f‖ * ⟪f,g⟫ = ‖g‖ * ‖f‖²
    have hfn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
    have h2 : ⟪f, g⟫_ℝ = ‖g‖ * ‖f‖ := by
      have := mul_right_cancel₀ hfn (show ⟪f, g⟫_ℝ * ‖f‖ = ‖g‖ * ‖f‖ * ‖f‖ by nlinarith)
      linarith
    linarith

/-- Cauchy-Schwarz equality implies proportionality:
    ⟪f,g⟫ = ‖f‖·‖g‖ → ‖‖f‖•g - ‖g‖•f‖² = 0. -/
theorem proportional_of_inner_eq (f g : E) (h : ⟪f, g⟫_ℝ = ‖f‖ * ‖g‖) :
    ‖f‖ • g = ‖g‖ • f := by
  -- Show ‖‖f‖•g - ‖g‖•f‖ = 0
  rw [← sub_eq_zero]
  rw [← norm_eq_zero]
  rw [← sq_eq_zero_iff]
  -- Expand ‖a - b‖² = ‖a‖² + ‖b‖² - 2⟪a,b⟫
  rw [@norm_sub_sq_real E]
  -- Simplify norms: ‖c • x‖ = |c| * ‖x‖
  simp only [norm_smul, Real.norm_of_nonneg (norm_nonneg f),
    Real.norm_of_nonneg (norm_nonneg g)]
  -- Simplify inner product: ⟪‖f‖•g, ‖g‖•f⟫ = ‖f‖*‖g‖*⟪g,f⟫
  rw [real_inner_smul_left, real_inner_smul_right]
  -- Use ⟪g,f⟫ = ⟪f,g⟫ = ‖f‖*‖g‖
  rw [real_inner_comm, h]
  ring

-- ============================================================
-- SECTION II: Strict Minkowski Inequality (Main Result)
-- ============================================================

/-- **Strict Minkowski inequality** for real inner product spaces:
    ‖f+g‖ = ‖f‖ + ‖g‖ iff ‖f‖ • g = ‖g‖ • f (non-negative proportionality).

    The proof reduces Minkowski equality to Cauchy-Schwarz equality:
    ‖f+g‖² = ‖f‖² + 2⟪f,g⟫ + ‖g‖² vs (‖f‖+‖g‖)² = ‖f‖² + 2‖f‖‖g‖ + ‖g‖².
    Equal iff ⟪f,g⟫ = ‖f‖‖g‖, which characterizes proportionality. -/
theorem norm_add_eq_iff_proportional (f g : E) :
    ‖f + g‖ = ‖f‖ + ‖g‖ ↔ ‖f‖ • g = ‖g‖ • f := by
  constructor
  · -- Forward: Minkowski equality → proportionality
    intro h
    -- ⟪f,g⟫ = ‖f‖·‖g‖ (squaring both sides)
    have hi : ⟪f, g⟫_ℝ = ‖f‖ * ‖g‖ := by
      have hsq : ‖f + g‖ ^ 2 = (‖f‖ + ‖g‖) ^ 2 := by rw [h]
      rw [@norm_add_sq_real E] at hsq
      linarith
    exact proportional_of_inner_eq f g hi
  · -- Backward: proportionality → Minkowski equality
    intro h
    have hi := inner_eq_of_proportional f g h
    -- ‖f+g‖² = (‖f‖+‖g‖)²
    have hsq : ‖f + g‖ ^ 2 = (‖f‖ + ‖g‖) ^ 2 := by
      rw [@norm_add_sq_real E]; nlinarith
    -- Square root: a² = b² with a,b ≥ 0 → a = b
    have : (‖f + g‖ - (‖f‖ + ‖g‖)) * (‖f + g‖ + (‖f‖ + ‖g‖)) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith [norm_nonneg (f + g), norm_nonneg f, norm_nonneg g]

end StrictMinkowski
