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
  by_cases hf : ‖f‖ = 0
  · rw [norm_eq_zero] at hf; simp [hf]
  · have h1 : ⟪f, ‖f‖ • g⟫_ℝ = ⟪f, ‖g‖ • f⟫_ℝ := by rw [h]
    rw [inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have hfpos : (0 : ℝ) < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf)
    field_simp at h1; linarith

/-- Cauchy-Schwarz equality implies proportionality:
    ⟪f,g⟫ = ‖f‖·‖g‖ → ‖‖f‖•g - ‖g‖•f‖² = 0. -/
theorem proportional_of_inner_eq (f g : E) (h : ⟪f, g⟫_ℝ = ‖f‖ * ‖g‖) :
    ‖f‖ • g = ‖g‖ • f := by
  have key : ‖‖f‖ • g - ‖g‖ • f‖ ^ 2 = 0 := by
    have h1 : ⟪‖f‖ • g, ‖g‖ • f⟫_ℝ = ‖f‖ * ‖g‖ * ⟪g, f⟫_ℝ := by
      simp [inner_smul_left, inner_smul_right, star_trivial]; ring
    have h2 : ⟪g, f⟫_ℝ = ‖f‖ * ‖g‖ := by rw [real_inner_comm]; exact h
    rw [@norm_sub_sq_real E, h1, h2]
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    ring
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at key
  exact key

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
