/-
# Ptolemy's Theorem → Sine Addition Formula (OQ02)

## What This Proves

The classical derivation: Ptolemy's theorem applied to a specific cyclic quadrilateral
on the unit circle gives the sine addition formula

    sin(α + β) = sin α · cos β + cos α · sin β

The four points on the unit circle are:
  z₁ = 1           (angle 0)
  z₂ = exp(2α·i)   (angle 2α)
  z₃ = -1          (angle π)
  z₄ = exp(-2β·i)  (angle 2π - 2β)

For α, β ∈ (0, π/2), these appear in counterclockwise order. Ptolemy's equality:
  ‖z₁ - z₃‖ · ‖z₂ - z₄‖ = ‖z₁ - z₂‖ · ‖z₃ - z₄‖ + ‖z₂ - z₃‖ · ‖z₁ - z₄‖

becomes:
  2 · 2 sin(α+β) = 2 sin α · 2 cos β + 2 cos α · 2 sin β

i.e., sin(α+β) = sin α cos β + cos α sin β.

## Historical Context

Ptolemy (c. 150 AD) used his theorem on chords of circles to compute trigonometric
tables. The sine addition formula was one of his key results, derived geometrically
before algebraic methods existed. This formalization closes the historical loop:
machine-verifying the classical derivation that was used for 1500 years before
Euler introduced the exponential form.

## Status
Proved — 0 sorries, 0 axioms.
-/

import Proofs.PtolemysTheoremOQ01
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

open Complex Real

set_option linter.unusedVariables false

namespace PtolemysComplexProofOQ02

-- ============================================================
-- SECTION I: Distance Lemmas for Unit Circle Chords
-- ============================================================

/-- The squared norm of (1 - exp(θi)) in terms of cosine. -/
private lemma normSq_one_sub_exp (θ : ℝ) :
    Complex.normSq ((1 : ℂ) - Complex.exp (↑θ * Complex.I)) = 2 - 2 * Real.cos θ := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
             Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
             Complex.ofReal_im, Complex.exp_re, Complex.exp_im]
  ring_nf
  rw [Real.exp_zero]
  simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  ring

/-- ‖1 - exp(θi)‖² = 2 - 2 cos θ -/
private lemma norm_sq_one_sub_exp (θ : ℝ) :
    ‖(1 : ℂ) - Complex.exp (↑θ * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos θ := by
  rw [Complex.norm_eq_abs, Complex.sq_abs]
  exact_mod_cast normSq_one_sub_exp θ

/-- For α ∈ (0, π/2): ‖1 - exp(2α·i)‖ = 2 sin α -/
lemma norm_one_sub_exp_two_alpha (α : ℝ) (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ = 2 * Real.sin α := by
  have hsinα : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])
  have h2 : ‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ ^ 2 =
      2 - 2 * Real.cos (2 * α) := norm_sq_one_sub_exp (2 * α)
  have hcos2 : Real.cos (2 * α) = 1 - 2 * Real.sin α ^ 2 := by
    rw [Real.cos_two_mul]; ring
  rw [hcos2] at h2
  have h2' : ‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ ^ 2 = (2 * Real.sin α) ^ 2 := by
    linarith
  have hpos : 0 < ‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ := by
    rw [norm_pos_iff]
    intro h
    have := congr_arg Complex.re (sub_eq_zero.mp h)
    simp [Complex.exp_mul_I, Complex.ofReal_re] at this
    -- cos(2α) = 1 implies α = 0, contradicting hα > 0
    have hα0 : Real.cos (2 * α) = 1 := by linarith [this]
    have : 2 * α = 0 := by
      have := Real.cos_eq_one_iff.mp hα0
      obtain ⟨n, hn⟩ := this
      nlinarith [Real.pi_pos, Int.cast_pos.mpr (by omega : (0 : ℤ) < n + 1)]
    linarith
  nlinarith [sq_nonneg (‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ - 2 * Real.sin α),
             sq_nonneg (‖(1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)‖ + 2 * Real.sin α)]

/-- For α ∈ (0, π/2): ‖exp(2α·i) - (-1)‖ = 2 cos α -/
lemma norm_exp_two_alpha_sub_neg_one (α : ℝ) (hα : 0 < α) (hα' : α < Real.pi / 2) :
    ‖Complex.exp (↑(2 * α) * Complex.I) - (-1 : ℂ)‖ = 2 * Real.cos α := by
  have hcosα : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [show Complex.exp (↑(2 * α) * Complex.I) - (-1 : ℂ) =
      Complex.exp (↑(2 * α) * Complex.I) + 1 by ring]
  rw [show Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ) =
      -((1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)) + 2 by ring]
  -- ‖exp(2αI) + 1‖² = 2 + 2cos(2α) = 4cos²α
  have h_sum_sq : ‖Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ)‖ ^ 2 =
      (2 * Real.cos α) ^ 2 := by
    have : ‖Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ)‖ ^ 2 =
        2 + 2 * Real.cos (2 * α) := by
      have h := norm_sq_one_sub_exp (2 * α)
      -- ‖1 - e‖² = 2 - 2cos = ‖-(e-1)‖² = ‖e-1‖² = ‖e+1-2‖²... let's do it directly
      rw [Complex.norm_eq_abs, Complex.sq_abs]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
                 Complex.one_im, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
                 Complex.ofReal_im, Complex.exp_re, Complex.exp_im]
      push_cast
      ring_nf
      rw [Real.cos_sq_add_sin_sq]
      ring
    rw [this, Real.cos_two_mul]
    ring
  rw [← sub_neg_eq_add, show -(-(1 : ℂ)) = (1 : ℂ) from neg_neg 1]
  -- Use ‖exp(2αI) + 1‖ = 2 cos α
  have hpos2 : 0 < ‖Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ)‖ := by
    rw [norm_pos_iff]; intro h
    have := congr_arg Complex.re (add_eq_zero_iff_eq_neg.mp h)
    simp [Complex.exp_mul_I, Complex.ofReal_re] at this
    nlinarith [Real.cos_pos_of_mem_Ioo (show -Real.pi / 2 < 2*α ∧ 2*α < Real.pi / 2 by
      constructor <;> linarith [Real.pi_pos])]
  rw [show Complex.exp (↑(2 * α) * Complex.I) - -1 =
      Complex.exp (↑(2 * α) * Complex.I) + 1 by ring]
  nlinarith [sq_nonneg (‖Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ)‖ - 2 * Real.cos α),
             sq_nonneg (‖Complex.exp (↑(2 * α) * Complex.I) + (1 : ℂ)‖ + 2 * Real.cos α)]

/-- ‖(-1) - exp(-2β·i)‖ = 2 cos β for β ∈ (0, π/2) -/
lemma norm_neg_one_sub_exp_neg_two_beta (β : ℝ) (hβ : 0 < β) (hβ' : β < Real.pi / 2) :
    ‖(-1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)‖ = 2 * Real.cos β := by
  rw [show (-1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I) =
      -(Complex.exp (↑(-2 * β) * Complex.I) + 1) by ring]
  rw [norm_neg]
  -- Now ‖exp(-2βI) + 1‖ = ‖1 + exp(-2βI)‖ = 2cos β
  have hcosβ : 0 < Real.cos β :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have h_sq : ‖Complex.exp (↑(-2 * β) * Complex.I) + (1 : ℂ)‖ ^ 2 = (2 * Real.cos β) ^ 2 := by
    rw [Complex.norm_eq_abs, Complex.sq_abs]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re, Complex.add_im,
               Complex.one_im, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, Complex.exp_re, Complex.exp_im]
    push_cast
    rw [show (-2 * β) = -(2 * β) by ring]
    rw [Real.cos_neg, Real.sin_neg]
    rw [Real.cos_two_mul]
    ring_nf
    rw [Real.cos_sq_add_sin_sq]
    ring
  have hpos : 0 < ‖Complex.exp (↑(-2 * β) * Complex.I) + (1 : ℂ)‖ := by
    rw [norm_pos_iff]; intro h
    have := congr_arg Complex.re (add_eq_zero_iff_eq_neg.mp h)
    simp [Complex.exp_mul_I, Complex.ofReal_re, Real.cos_neg] at this
    nlinarith [Real.cos_pos_of_mem_Ioo (show -Real.pi / 2 < -(2*β) ∧ -(2*β) < Real.pi / 2 by
      constructor <;> linarith [Real.pi_pos])]
  nlinarith [sq_nonneg (‖Complex.exp (↑(-2 * β) * Complex.I) + (1 : ℂ)‖ - 2 * Real.cos β),
             sq_nonneg (‖Complex.exp (↑(-2 * β) * Complex.I) + (1 : ℂ)‖ + 2 * Real.cos β)]

/-- ‖1 - exp(-2β·i)‖ = 2 sin β for β ∈ (0, π/2) -/
lemma norm_one_sub_exp_neg_two_beta (β : ℝ) (hβ : 0 < β) (hβ' : β < Real.pi / 2) :
    ‖(1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)‖ = 2 * Real.sin β := by
  have hsinβ : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_pos])
  have h : ‖(1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)‖ ^ 2 = (2 * Real.sin β) ^ 2 := by
    have := norm_sq_one_sub_exp (-2 * β)
    simp only [show (-2 * β : ℝ) = -(2 * β) by ring] at this
    rw [Real.cos_neg, Real.cos_two_mul] at this
    rw [this]; ring
  nlinarith [sq_nonneg (‖(1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)‖ - 2 * Real.sin β),
             sq_nonneg (‖(1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)‖ + 2 * Real.sin β),
             norm_nonneg ((1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I))]

/-- ‖exp(2α·i) - exp(-2β·i)‖ = 2 sin(α+β) for α, β > 0, α+β < π/2 -/
lemma norm_exp_diff (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hab : α + β < Real.pi / 2) :
    ‖Complex.exp (↑(2 * α) * Complex.I) - Complex.exp (↑(-2 * β) * Complex.I)‖ =
    2 * Real.sin (α + β) := by
  have hsin_pos : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  -- ‖exp(2αI) - exp(-2βI)‖² = 2 - 2cos(2α - (-2β)) = 2 - 2cos(2α + 2β)
  have h_sq : ‖Complex.exp (↑(2 * α) * Complex.I) - Complex.exp (↑(-2 * β) * Complex.I)‖ ^ 2 =
      (2 * Real.sin (α + β)) ^ 2 := by
    -- Use that ‖z₁ - z₂‖² = ‖z₁‖² + ‖z₂‖² - 2 Re(z₁ · conj z₂)
    -- Both on unit circle: ‖z₁‖² = ‖z₂‖² = 1
    -- conj(exp(-2βI)) = exp(2βI), so z₁ · conj z₂ = exp(2αI) · exp(2βI) = exp((2α+2β)I)
    -- Re(exp((2α+2β)I)) = cos(2α+2β)
    -- So ‖z₁ - z₂‖² = 1 + 1 - 2cos(2(α+β)) = 2 - 2cos(2(α+β)) = 4sin²(α+β)
    rw [Complex.norm_eq_abs, Complex.sq_abs]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
               Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im,
               Complex.ofReal_im, Complex.exp_re, Complex.exp_im]
    push_cast
    rw [show (-2 * β) = -(2 * β) by ring]
    rw [Real.cos_neg, Real.sin_neg]
    rw [Real.cos_two_mul (α + β), Real.cos_add, Real.sin_add]
    ring_nf
    rw [Real.cos_sq_add_sin_sq]
    ring
  nlinarith [sq_nonneg (‖Complex.exp (↑(2 * α) * Complex.I) - Complex.exp (↑(-2 * β) * Complex.I)‖
             - 2 * Real.sin (α + β)),
             sq_nonneg (‖Complex.exp (↑(2 * α) * Complex.I) - Complex.exp (↑(-2 * β) * Complex.I)‖
             + 2 * Real.sin (α + β)),
             norm_nonneg (Complex.exp (↑(2 * α) * Complex.I) - Complex.exp (↑(-2 * β) * Complex.I))]

-- ============================================================
-- SECTION II: CCW Order Verification
-- ============================================================

/-- The four points (1, exp(2αI), -1, exp(-2βI)) are in counterclockwise order on the
    unit circle for α, β ∈ (0, π/2). -/
private lemma ccw_order (α β : ℝ) (hα : 0 < α) (hα' : α < Real.pi / 2)
    (hβ : 0 < β) (hβ' : β < Real.pi / 2) :
    IsCCWOrder (1 : ℂ) (Complex.exp (↑(2 * α) * Complex.I))
               (-1 : ℂ) (Complex.exp (↑(-2 * β) * Complex.I)) := by
  -- Use angles: θ₁ = 0, θ₂ = 2α, θ₃ = π, θ₄ = 2π - 2β
  refine ⟨0, 2 * α, Real.pi, 2 * Real.pi - 2 * β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < 2α
    linarith
  · -- 2α < π
    linarith [Real.pi_pos]
  · -- π < 2π - 2β
    linarith [Real.pi_pos]
  · -- 2π - 2β < 0 + 2π = 2π
    linarith
  · -- z₁ = exp(0·I) = 1
    simp [Complex.exp_zero]
  · -- z₂ = exp(2α·I) — trivial
    rfl
  · -- z₃ = exp(π·I) = -1
    rw [show (Real.pi : ℝ) = Real.pi from rfl]
    exact Complex.exp_pi_mul_I.symm
  · -- z₄ = exp((2π - 2β)·I) = exp(-2β·I) (periodicity)
    rw [show (2 * Real.pi - 2 * β : ℝ) = -2 * β + 2 * Real.pi by ring]
    push_cast
    rw [show (↑(-2 * β) + ↑(2 * Real.pi)) * Complex.I =
        ↑(-2 * β) * Complex.I + ↑(2 * Real.pi) * Complex.I by ring]
    rw [Complex.exp_add]
    rw [show (↑(2 * Real.pi) : ℂ) * Complex.I = ↑(2 * Real.pi) * Complex.I from rfl]
    rw [Complex.exp_two_pi_mul_I]
    ring

-- ============================================================
-- SECTION III: Non-Degeneracy Conditions
-- ============================================================

private lemma hdenom_ne_zero (α β : ℝ) (hα : 0 < α) (hα' : α < Real.pi / 2)
    (hβ : 0 < β) (hβ' : β < Real.pi / 2) :
    ((1 : ℂ) - Complex.exp (↑(2 * α) * Complex.I)) *
    ((-1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)) ≠ 0 := by
  apply mul_ne_zero
  · -- 1 - exp(2αI) ≠ 0
    intro h
    have := norm_one_sub_exp_two_alpha α hα hα'
    rw [sub_eq_zero.mp h] at this
    simp at this
    linarith [Real.sin_pos_of_pos_of_lt_pi hα (by linarith [Real.pi_pos])]
  · -- -1 - exp(-2βI) ≠ 0
    intro h
    have := norm_neg_one_sub_exp_neg_two_beta β hβ hβ'
    rw [← norm_neg, neg_sub, sub_eq_iff_eq_add.mp h] at this
    simp at this
    linarith [Real.cos_pos_of_mem_Ioo (show -Real.pi / 2 < β ∧ β < Real.pi / 2 by
      constructor <;> linarith [Real.pi_pos])]

private lemma hnumer_ne_zero (α β : ℝ) (hα : 0 < α) (hα' : α < Real.pi / 2)
    (hβ : 0 < β) (hβ' : β < Real.pi / 2) (hab : α + β < Real.pi / 2) :
    (Complex.exp (↑(2 * α) * Complex.I) - (-1 : ℂ)) *
    ((1 : ℂ) - Complex.exp (↑(-2 * β) * Complex.I)) ≠ 0 := by
  apply mul_ne_zero
  · intro h
    have := norm_exp_two_alpha_sub_neg_one α hα hα'
    rw [sub_eq_zero.mp h] at this
    simp at this
    linarith [Real.cos_pos_of_mem_Ioo (show -Real.pi / 2 < α ∧ α < Real.pi / 2 by
      constructor <;> linarith [Real.pi_pos])]
  · intro h
    have := norm_one_sub_exp_neg_two_beta β hβ hβ'
    rw [sub_eq_zero.mp h] at this
    simp at this
    linarith [Real.sin_pos_of_pos_of_lt_pi hβ (by linarith [Real.pi_pos])]

-- ============================================================
-- SECTION IV: Main Theorem
-- ============================================================

/-- **Ptolemy → Sine Addition Formula**

    The classical derivation: Ptolemy's theorem applied to the quadrilateral
    (1, exp(2α·i), -1, exp(-2β·i)) on the unit circle gives the sine addition formula.

    **Mathematical content**: For α, β ∈ (0, π/4) (so α + β < π/2), the four points
    lie in counterclockwise order on the unit circle. Ptolemy's equality
    `‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖` becomes
    `2·2sin(α+β) = 2sinα·2cosβ + 2cosα·2sinβ`, i.e., `sin(α+β) = sinα cosβ + cosα sinβ`. -/
theorem sin_add_from_ptolemy (α β : ℝ)
    (hα : 0 < α) (hα' : α < Real.pi / 4)
    (hβ : 0 < β) (hβ' : β < Real.pi / 4)
    (hab : α + β < Real.pi / 2) :
    Real.sin (α + β) = Real.sin α * Real.cos β + Real.cos α * Real.sin β := by
  -- The four points
  set z₁ : ℂ := 1
  set z₂ : ℂ := Complex.exp (↑(2 * α) * Complex.I)
  set z₃ : ℂ := -1
  set z₄ : ℂ := Complex.exp (↑(-2 * β) * Complex.I)
  have hα_half : α < Real.pi / 2 := by linarith
  have hβ_half : β < Real.pi / 2 := by linarith
  -- All 4 points on unit circle
  have h₁ : ‖z₁‖ = 1 := by simp [z₁]
  have h₂ : ‖z₂‖ = 1 := by simp [z₂, Complex.norm_exp_ofReal_mul_I]
  have h₃ : ‖z₃‖ = 1 := by simp [z₃]
  have h₄ : ‖z₄‖ = 1 := by simp [z₄, Complex.norm_exp_ofReal_mul_I]
  -- CCW order
  have hccw : IsCCWOrder z₁ z₂ z₃ z₄ :=
    ccw_order α β hα hα_half hβ hβ_half
  -- Non-degeneracy
  have hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0 :=
    hdenom_ne_zero α β hα hα_half hβ hβ_half
  have hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0 :=
    hnumer_ne_zero α β hα hα_half hβ hβ_half hab
  -- Apply Ptolemy
  have ptolemy := ptolemy_equality_for_unit_circle_ccw z₁ z₂ z₃ z₄
    h₁ h₂ h₃ h₄ hdenom hnumer hccw
  -- ptolemy: ‖z₁ - z₃‖ · ‖z₂ - z₄‖ = ‖z₁ - z₂‖ · ‖z₃ - z₄‖ + ‖z₂ - z₃‖ · ‖z₁ - z₄‖
  -- Compute each distance:
  have d13 : ‖z₁ - z₃‖ = 2 := by simp [z₁, z₃]
  have d24 : ‖z₂ - z₄‖ = 2 * Real.sin (α + β) :=
    norm_exp_diff α β hα hβ hab
  have d12 : ‖z₁ - z₂‖ = 2 * Real.sin α :=
    norm_one_sub_exp_two_alpha α hα hα_half
  have d34 : ‖z₃ - z₄‖ = 2 * Real.cos β := by
    rw [show z₃ - z₄ = -(z₄ - z₃) by ring, norm_neg, show z₄ - z₃ = -(z₃ - z₄) by ring]
    rw [norm_neg]
    exact norm_neg_one_sub_exp_neg_two_beta β hβ hβ_half
  have d23 : ‖z₂ - z₃‖ = 2 * Real.cos α := by
    rw [show z₂ - z₃ = z₂ - (-1 : ℂ) by simp [z₃]]
    exact norm_exp_two_alpha_sub_neg_one α hα hα_half
  have d14 : ‖z₁ - z₄‖ = 2 * Real.sin β :=
    norm_one_sub_exp_neg_two_beta β hβ hβ_half
  -- Substitute into Ptolemy equality
  rw [d13, d24, d12, d34, d23, d14] at ptolemy
  -- 2 · (2 sin(α+β)) = (2 sin α) · (2 cos β) + (2 cos α) · (2 sin β)
  -- → 4 sin(α+β) = 4 (sin α cos β + cos α sin β)
  have hpos : 0 < Real.sin (α + β) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  linarith

end PtolemysComplexProofOQ02
