/-!
# Completing the Ptolemy Concyclicity Characterization (OQ-01 Incomplete-01)

## What This File Proves

This file completes the concyclicity characterization of Ptolemy's theorem by providing
the **converse direction**: for four distinct unit-circle points, if Ptolemy's equality
holds, then the points must be in CCW or CW order.

Combined with `ptolemy_equality_for_unit_circle_ccw` (from PtolemysTheoremOQ01.lean),
this gives the **full biconditional** for unit-circle points:

  **Ptolemy equality** ↔ **CCW order** (or its reverse, CW order)

## Historical Context: Completing the Sorry

PtolemysTheoremOQ01.lean was initially marked "sorry" for `ptolemy_ratio_pos_of_ccw`:

  > "R > 0 [requires ptolemy_ratio_pos_of_ccw, currently sorry]"

The sorry was resolved without the inscribed angle theorem, using the **exponential
difference factorization**:

  exp(iα) - exp(iβ) = 2I·sin((α-β)/2)·exp(i(α+β)/2)

For CCW order θ₁<θ₂<θ₃<θ₄<θ₁+2π, all four half-angle sines are negative,
giving R = (−)(−)/((−)(−)) > 0.

## The Converse Direction (New)

The completed OQ01 file proves (4) → (3) → (2) → (1):
  4. CCW order → 3. Ratio R > 0 → 2. SameRay → 1. Ptolemy equality

This file proves (1) → (4): Ptolemy equality → CCW or CW order.
This closes the equivalence chain:
  Ptolemy equality ↔ SameRay ↔ Ratio R > 0 ↔ CCW or CW order

## Proof Strategy for the Converse

Given Ptolemy equality for distinct unit-circle points:
1. Apply `ptolemy_equality_implies_proportional`: ∃ t > 0, (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)
2. Write zₖ = exp(i·arg(zₖ)), substitute the exp_diff_factor formula
3. Derive: t = sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2) / (sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2))
4. Since t > 0, both products have the same sign
5. Sign analysis: the only sign patterns consistent with unit-circle distinctness
   are all-negative (→ CCW: θ₁<θ₂<θ₃<θ₄) or all-positive (→ CW: θ₁>θ₂>θ₃>θ₄)
   or two specific mixed patterns (which reduce to cyclic rotations of CCW/CW)

## Status

- Main theorem `ptolemy_equality_implies_ccw_or_cw`: **fully proved, 0 sorries**
- Theorem `ptolemy_equality_iff_ccw_or_cw`: **fully proved, 0 sorries**
- Both sorries eliminated: (1) algebraic derivation via mul_left_cancel₀ + calc;
  (2) 8-case sign analysis was already in place from prior work
-/

import Proofs.PtolemysTheoremOQ01
import Proofs.PtolemysComplexProofOQ01
import Proofs.PtolemysComplexProof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Complex Real

namespace PtolemysTheoremOQ01Incomplete01

/-! ## Section I: Angle Extraction for Unit-Circle Points -/

/-- Every unit-circle point equals exp(i·arg(z)). -/
private lemma unit_circle_eq_exp_arg (z : ℂ) (hz : ‖z‖ = 1) :
    z = Complex.exp (↑(Complex.arg z) * Complex.I) := by
  have habs : Complex.abs z = 1 := by rwa [Complex.norm_eq_abs] at hz
  conv_lhs => rw [← Complex.abs_mul_exp_arg_mul_I z, habs]
  simp

/-- For distinct unit-circle points, their args are distinct. -/
private lemma arg_ne_of_ne {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (hne : z ≠ w) :
    Complex.arg z ≠ Complex.arg w := by
  intro h
  apply hne
  rw [unit_circle_eq_exp_arg z hz, unit_circle_eq_exp_arg w hw, h]

/-! ## Section II: Half-Angle Sine Sign Lemmas -/

/-- For args in (-π, π] with distinct values, sin((θ-φ)/2) is nonzero. -/
private lemma sin_half_ne_zero_of_ne {θ φ : ℝ}
    (hθ : Complex.arg (Complex.exp (↑θ * Complex.I)) = θ ∨ True)
    (hne : θ ≠ φ)
    (hbnd : (θ - φ) ∈ Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)) :
    Real.sin ((θ - φ) / 2) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro ⟨n, hn⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  have : (θ - φ) / 2 ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> [linarith [hbnd.1]; linarith [hbnd.2]]
  have hn0 : n = 0 := by
    have hlo : -Real.pi < ↑n * Real.pi := by rw [hn]; linarith [this.1]
    have hhi : ↑n * Real.pi < Real.pi := by rw [hn]; linarith [this.2]
    have : (-1 : ℤ) < n := by
      apply Int.cast_lt (R := ℝ) |>.mp; push_cast; linarith
    have : n < (1 : ℤ) := by
      apply Int.cast_lt (R := ℝ) |>.mp; push_cast; linarith
    omega
  simp [hn0] at hn; linarith

/-- For args θ, φ ∈ (-π, π] with θ ≠ φ:
    sin((θ-φ)/2) > 0 iff θ > φ,  sin((θ-φ)/2) < 0 iff θ < φ. -/
private lemma sin_half_sign_iff {θ φ : ℝ}
    (hbnd : (θ - φ) ∈ Set.Ioo (-(2 * Real.pi)) (2 * Real.pi)) (hne : θ ≠ φ) :
    (0 < Real.sin ((θ - φ) / 2) ↔ φ < θ) ∧
    (Real.sin ((θ - φ) / 2) < 0 ↔ θ < φ) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrange : (θ - φ) / 2 ∈ Set.Ioo (-Real.pi) Real.pi := by
    constructor <;> [linarith [hbnd.1]; linarith [hbnd.2]]
  have hne2 : θ - φ ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · constructor
    · intro h
      by_contra h'
      push_neg at h'
      have : Real.sin ((θ - φ) / 2) ≤ 0 := by
        apply Real.sin_nonpos_of_nonneg_of_nonpos
        · linarith [hrange.1]
        · linarith
      linarith
    · intro h
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith
      · linarith [hrange.2]
  · constructor
    · intro h
      by_contra h'
      push_neg at h'
      have : Real.sin ((θ - φ) / 2) ≥ 0 := by
        rcases lt_or_eq_of_le h' with hlt | heq
        · apply Real.sin_nonneg_of_nonneg_of_le_pi
          · linarith
          · linarith [hrange.2]
        · rw [← heq]; simp
      linarith
    · intro h
      have : Real.sin ((θ - φ) / 2) < 0 := by
        apply Real.sin_neg_of_neg_of_neg_pi_lt
        · linarith
        · linarith [hrange.1]
      exact this

/-! ## Section III: The Sine Ratio Identity -/

/-- The key algebraic identity: the ratio t from Ptolemy equality equals the sine ratio.
For unit-circle points zₖ = exp(iθₖ), if (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄) then:
  t = sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2) / (sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2)) -/
private lemma t_eq_sine_ratio {θ₁ θ₂ θ₃ θ₄ : ℝ} {t : ℝ}
    (ht_pos : 0 < t)
    (ht_eq : (Complex.exp (↑θ₂ * Complex.I) - Complex.exp (↑θ₃ * Complex.I)) *
             (Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₄ * Complex.I)) =
             (t : ℂ) *
             ((Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₂ * Complex.I)) *
              (Complex.exp (↑θ₃ * Complex.I) - Complex.exp (↑θ₄ * Complex.I))))
    (hs₁₂_ne : Real.sin ((θ₁ - θ₂) / 2) ≠ 0)
    (hs₃₄_ne : Real.sin ((θ₃ - θ₄) / 2) ≠ 0) :
    t = Real.sin ((θ₂ - θ₃) / 2) * Real.sin ((θ₁ - θ₄) / 2) /
        (Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2)) := by
  -- Half-angle factorization: exp(ia)-exp(ib) = 2I·sin((a-b)/2)·exp(i(a+b)/2)
  have hha : ∀ a b : ℝ, Complex.exp (↑a * Complex.I) - Complex.exp (↑b * Complex.I) =
      2 * Complex.I * ↑(Real.sin ((a - b) / 2)) *
      Complex.exp (↑((a + b) / 2) * Complex.I) := by
    intro a b
    have h1 : Complex.exp (↑a * Complex.I) =
        Complex.exp (↑((a + b) / 2) * Complex.I) * Complex.exp (↑((a - b) / 2) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have h2 : Complex.exp (↑b * Complex.I) =
        Complex.exp (↑((a + b) / 2) * Complex.I) * Complex.exp (-(↑((a - b) / 2) * Complex.I)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, h2, ← mul_sub]
    have h2isin : Complex.exp (↑((a - b) / 2) * Complex.I) -
                  Complex.exp (-(↑((a - b) / 2) * Complex.I)) =
                  2 * Complex.I * ↑(Real.sin ((a - b) / 2)) := by
      rw [show -(↑((a - b) / 2) : ℂ) * Complex.I = ↑(-((a - b) / 2)) * Complex.I from by push_cast; ring]
      simp only [Complex.exp_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [h2isin]; ring
  -- Phase cancellation: E₂₃·E₁₄ = E₁₂·E₃₄
  have hE : Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
            Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I) =
            Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I) *
            Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  -- Rewrite ht_eq using hha
  rw [hha θ₂ θ₃, hha θ₁ θ₄, hha θ₁ θ₂, hha θ₃ θ₄] at ht_eq
  -- Both sides: (2I)²·s·E where s and E are the sine product and phase
  -- LHS = -4·s₂₃·s₁₄·E₂₃E₁₄, RHS = t·(-4)·s₁₂·s₃₄·E₁₂E₃₄
  -- After canceling -4 and E: s₂₃·s₁₄ = t·s₁₂·s₃₄
  have hE_ne : Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I) *
               Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hs₁₂_ne' : (↑(Real.sin ((θ₁ - θ₂) / 2)) : ℂ) ≠ 0 := by exact_mod_cast hs₁₂_ne
  have hs₃₄_ne' : (↑(Real.sin ((θ₃ - θ₄) / 2)) : ℂ) ≠ 0 := by exact_mod_cast hs₃₄_ne
  -- After factoring out -4 and E, the complex equation reduces to a real equation
  have hcx : (↑(Real.sin ((θ₂ - θ₃) / 2)) : ℂ) * ↑(Real.sin ((θ₁ - θ₄) / 2)) =
             ↑t * (↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2))) := by
    -- Strategy: factor (2I)² · E₂₃E₁₄ from both sides.
    -- LHS side: ↑s₂₃ · ↑s₁₄ · (2I)² · E₂₃E₁₄ = (2I·↑s₂₃·E₂₃) · (2I·↑s₁₄·E₁₄) [ring]
    --   = ht_eq LHS (after hha substitution already done at line 189)
    --   = ht_eq RHS = t · (2I·↑s₁₂·E₁₂) · (2I·↑s₃₄·E₃₄)
    --   = ↑t · ↑s₁₂ · ↑s₃₄ · (2I)² · E₁₂E₃₄ [ring]
    --   = ↑t · ↑s₁₂ · ↑s₃₄ · (2I)² · E₂₃E₁₄ [hE: E₂₃E₁₄ = E₁₂E₃₄, so ← hE]
    -- Then cancel (2I)² · E₂₃E₁₄ ≠ 0.
    have hI2_ne : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
    have hfactor_ne : (2 * Complex.I) ^ 2 * (Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
        Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hI2_ne) (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
    exact mul_right_cancel₀ hfactor_ne (by
      calc (↑(Real.sin ((θ₂ - θ₃) / 2)) : ℂ) * ↑(Real.sin ((θ₁ - θ₄) / 2)) *
            ((2 * Complex.I) ^ 2 * (Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
              Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)))
           = (2 * Complex.I * ↑(Real.sin ((θ₂ - θ₃) / 2)) *
                Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I)) *
             (2 * Complex.I * ↑(Real.sin ((θ₁ - θ₄) / 2)) *
                Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)) := by ring
         _ = ↑t * ((2 * Complex.I * ↑(Real.sin ((θ₁ - θ₂) / 2)) *
                       Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I)) *
                   (2 * Complex.I * ↑(Real.sin ((θ₃ - θ₄) / 2)) *
                       Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I))) := ht_eq
         _ = ↑t * (↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2))) *
             ((2 * Complex.I) ^ 2 * (Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I) *
               Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I))) := by ring
         _ = ↑t * (↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2))) *
             ((2 * Complex.I) ^ 2 * (Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I) *
               Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I))) := by rw [← hE])
  have hR : Real.sin ((θ₂ - θ₃) / 2) * Real.sin ((θ₁ - θ₄) / 2) =
            t * (Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2)) :=
    by exact_mod_cast hcx
  have hden_ne : Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2) ≠ 0 :=
    mul_ne_zero hs₁₂_ne hs₃₄_ne
  field_simp [hden_ne]
  linarith [hR]

/-! ## Section IV: The Main Converse Theorem -/

/-- **Converse Theorem**: Ptolemy equality for distinct unit-circle points implies CCW or CW order.

For four distinct unit-circle points where neither product of opposite sides is zero:
  Ptolemy equality → IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCCWOrder z₁ z₄ z₃ z₂

**Proof structure**:
1. Ptolemy equality + nonzero products → ∃ t > 0, (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)
2. Write zₖ = exp(i·arg(zₖ)), derive t = sine product ratio
3. Since t > 0, sign analysis of four sines → θ₁<θ₂<θ₃<θ₄ (CCW) or θ₁>θ₂>θ₃>θ₄ (CW)
   (other sign patterns give t < 0, contradiction)

**Status**: Fully proved (0 sorries). -/
theorem ptolemy_equality_implies_ccw_or_cw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdist₁₂ : z₁ ≠ z₂) (hdist₁₃ : z₁ ≠ z₃) (hdist₁₄ : z₁ ≠ z₄)
    (hdist₂₃ : z₂ ≠ z₃) (hdist₂₄ : z₂ ≠ z₄) (hdist₃₄ : z₃ ≠ z₄)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0)
    (hptolemy : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
                ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCCWOrder z₁ z₄ z₃ z₂ := by
  -- Step 1: Ptolemy equality → ∃ t > 0, (z₂-z₃)(z₁-z₄) = t·(z₁-z₂)(z₃-z₄)
  obtain ⟨t, ht_pos, ht_eq⟩ :=
    ptolemy_equality_implies_proportional z₁ z₂ z₃ z₄
      hdenom hnumer hptolemy
  -- Step 2: Extract angles θₖ = arg(zₖ) ∈ (-π, π]
  set θ₁ := Complex.arg z₁; set θ₂ := Complex.arg z₂
  set θ₃ := Complex.arg z₃; set θ₄ := Complex.arg z₄
  have hz₁ : z₁ = Complex.exp (↑θ₁ * Complex.I) := unit_circle_eq_exp_arg z₁ h₁
  have hz₂ : z₂ = Complex.exp (↑θ₂ * Complex.I) := unit_circle_eq_exp_arg z₂ h₂
  have hz₃ : z₃ = Complex.exp (↑θ₃ * Complex.I) := unit_circle_eq_exp_arg z₃ h₃
  have hz₄ : z₄ = Complex.exp (↑θ₄ * Complex.I) := unit_circle_eq_exp_arg z₄ h₄
  -- Args in (-π, π]
  have hθ₁_bd : θ₁ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z₁, Complex.arg_le_pi z₁⟩
  have hθ₂_bd : θ₂ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z₂, Complex.arg_le_pi z₂⟩
  have hθ₃_bd : θ₃ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z₃, Complex.arg_le_pi z₃⟩
  have hθ₄_bd : θ₄ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨Complex.neg_pi_lt_arg z₄, Complex.arg_le_pi z₄⟩
  -- Angles are distinct (from distinct points on unit circle)
  have hθ₁₂ : θ₁ ≠ θ₂ := arg_ne_of_ne h₁ h₂ hdist₁₂
  have hθ₁₃ : θ₁ ≠ θ₃ := arg_ne_of_ne h₁ h₃ hdist₁₃
  have hθ₁₄ : θ₁ ≠ θ₄ := arg_ne_of_ne h₁ h₄ hdist₁₄
  have hθ₂₃ : θ₂ ≠ θ₃ := arg_ne_of_ne h₂ h₃ hdist₂₃
  have hθ₂₄ : θ₂ ≠ θ₄ := arg_ne_of_ne h₂ h₄ hdist₂₄
  have hθ₃₄ : θ₃ ≠ θ₄ := arg_ne_of_ne h₃ h₄ hdist₃₄
  -- Bounds on differences: arg values in (-π, π] → differences in (-2π, 2π)
  have hπ := Real.pi_pos
  have hbnd₁₂ : θ₁ - θ₂ ∈ Set.Ioo (-(2*Real.pi)) (2*Real.pi) := by
    constructor <;> [linarith [hθ₁_bd.1, hθ₂_bd.2]; linarith [hθ₁_bd.2, hθ₂_bd.1]]
  have hbnd₂₃ : θ₂ - θ₃ ∈ Set.Ioo (-(2*Real.pi)) (2*Real.pi) := by
    constructor <;> [linarith [hθ₂_bd.1, hθ₃_bd.2]; linarith [hθ₂_bd.2, hθ₃_bd.1]]
  have hbnd₃₄ : θ₃ - θ₄ ∈ Set.Ioo (-(2*Real.pi)) (2*Real.pi) := by
    constructor <;> [linarith [hθ₃_bd.1, hθ₄_bd.2]; linarith [hθ₃_bd.2, hθ₄_bd.1]]
  have hbnd₁₄ : θ₁ - θ₄ ∈ Set.Ioo (-(2*Real.pi)) (2*Real.pi) := by
    constructor <;> [linarith [hθ₁_bd.1, hθ₄_bd.2]; linarith [hθ₁_bd.2, hθ₄_bd.1]]
  -- Step 3: Sine values are nonzero
  have hs₁₂_ne : Real.sin ((θ₁ - θ₂) / 2) ≠ 0 :=
    sin_half_ne_zero_of_ne (Or.inr trivial) hθ₁₂ hbnd₁₂
  have hs₂₃_ne : Real.sin ((θ₂ - θ₃) / 2) ≠ 0 :=
    sin_half_ne_zero_of_ne (Or.inr trivial) hθ₂₃ hbnd₂₃
  have hs₃₄_ne : Real.sin ((θ₃ - θ₄) / 2) ≠ 0 :=
    sin_half_ne_zero_of_ne (Or.inr trivial) hθ₃₄ hbnd₃₄
  have hs₁₄_ne : Real.sin ((θ₁ - θ₄) / 2) ≠ 0 :=
    sin_half_ne_zero_of_ne (Or.inr trivial) hθ₁₄ hbnd₁₄
  -- Step 4: t = sine ratio (from exp factorization)
  rw [hz₁, hz₂, hz₃, hz₄] at ht_eq
  have ht_ratio : t = Real.sin ((θ₂ - θ₃) / 2) * Real.sin ((θ₁ - θ₄) / 2) /
                      (Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2)) :=
    t_eq_sine_ratio ht_pos ht_eq hs₁₂_ne hs₃₄_ne
  -- Step 5: Sign analysis — t > 0 constrains the signs of the four sines
  rw [ht_ratio] at ht_pos
  have hden_ne : Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2) ≠ 0 :=
    mul_ne_zero hs₁₂_ne hs₃₄_ne
  rw [div_pos_iff] at ht_pos
  -- Sign lemmas for ordering
  have hsgn₁₂ := sin_half_sign_iff hbnd₁₂ hθ₁₂
  have hsgn₂₃ := sin_half_sign_iff hbnd₂₃ hθ₂₃
  have hsgn₃₄ := sin_half_sign_iff hbnd₃₄ hθ₃₄
  have hsgn₁₄ := sin_half_sign_iff hbnd₁₄ hθ₁₄
  -- Period lemmas for witness construction
  have hexp_add2pi : ∀ θ : ℝ, Complex.exp (↑(θ + 2 * Real.pi) * Complex.I) =
      Complex.exp (↑θ * Complex.I) := by
    intro θ
    have h2pi : Complex.exp (↑(2 * Real.pi) * Complex.I) = 1 := by
      rw [Complex.exp_mul_I]
      simp [Real.cos_two_pi, Real.sin_two_pi]
    rw [show (↑(θ + 2 * Real.pi) : ℂ) * Complex.I = ↑θ * Complex.I + ↑(2 * Real.pi) * Complex.I
        from by push_cast; ring,
        Complex.exp_add, h2pi, mul_one]
  have hexp_sub2pi : ∀ θ : ℝ, Complex.exp (↑(θ - 2 * Real.pi) * Complex.I) =
      Complex.exp (↑θ * Complex.I) := fun θ => by
    have := hexp_add2pi (θ - 2 * Real.pi)
    simp only [sub_add_cancel] at this
    exact this.symm
  -- Sign analysis: t > 0 constrains angle orderings to 8 cases, each giving CCW or CW
  -- Case split: (num>0 ∧ den>0) or (num<0 ∧ den<0)
  -- Each case splits further by mul_pos_iff into 4 sub-cases (8 total)
  -- All 8 cases produce IsCCWOrder z₁ z₂ z₃ z₄ or IsCCWOrder z₁ z₄ z₃ z₂
  -- with witnesses derived from the angle orderings + periodicity
  -- [HARD sorry: 8-case sign analysis — suitable for Aristotle]
  rcases ht_pos with ⟨hnum_pos, hden_pos⟩ | ⟨hnum_neg, hden_neg⟩
  · rcases mul_pos_iff.mp hnum_pos with ⟨hs₂₃p, hs₁₄p⟩ | ⟨hs₂₃n, hs₁₄n⟩ <;>
    rcases mul_pos_iff.mp hden_pos with ⟨hs₁₂p, hs₃₄p⟩ | ⟨hs₁₂n, hs₃₄n⟩
    · -- A: s₂₃>0, s₁₄>0, s₁₂>0, s₃₄>0 → θ₄<θ₃<θ₂<θ₁ → CW (IsCCWOrder z₁ z₄ z₃ z₂)
      have hθ₃₂ : θ₃ < θ₂ := hsgn₂₃.1.mp hs₂₃p
      have hθ₄₁ : θ₄ < θ₁ := hsgn₁₄.1.mp hs₁₄p
      have hθ₂₁ : θ₂ < θ₁ := hsgn₁₂.1.mp hs₁₂p
      have hθ₄₃ : θ₄ < θ₃ := hsgn₃₄.1.mp hs₃₄p
      -- θ₄ < θ₃ < θ₂ < θ₁; CW: witnesses (θ₁-2π, θ₄, θ₃, θ₂) for IsCCWOrder z₁ z₄ z₃ z₂
      exact Or.inr ⟨θ₁ - 2 * Real.pi, θ₄, θ₃, θ₂,
        by linarith, by linarith, by linarith, by linarith,
        by rw [hexp_sub2pi]; exact hz₁,
        hz₄, hz₃, hz₂⟩
    · -- B: s₂₃>0, s₁₄>0, s₁₂<0, s₃₄<0 → θ₃<θ₄<θ₁<θ₂ → CCW (IsCCWOrder z₁ z₂ z₃ z₄)
      have hθ₃₂ := (hsgn₂₃.1.mp hs₂₃p)  -- θ₃ < θ₂
      have hθ₄₁ := (hsgn₁₄.1.mp hs₁₄p)  -- θ₄ < θ₁
      have hθ₁₂ := (hsgn₁₂.2.mp hs₁₂n)  -- θ₁ < θ₂
      have hθ₃₄ := (hsgn₃₄.2.mp hs₃₄n)  -- θ₃ < θ₄
      -- θ₃ < θ₄ < θ₁ < θ₂; witnesses (θ₁, θ₂, θ₃+2π, θ₄+2π) for IsCCWOrder z₁ z₂ z₃ z₄
      exact Or.inl ⟨θ₁, θ₂, θ₃ + 2 * Real.pi, θ₄ + 2 * Real.pi,
        by linarith,
        by linarith [hθ₂_bd.2, hθ₃_bd.1, hπ],
        by linarith,
        by linarith [hθ₄_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₂,
        by rw [hexp_add2pi]; exact hz₃,
        by rw [hexp_add2pi]; exact hz₄⟩
    · -- C: s₂₃<0, s₁₄<0, s₁₂>0, s₃₄>0 → θ₂<θ₁<θ₄<θ₃ → CW (IsCCWOrder z₁ z₄ z₃ z₂)
      have hθ₂₃ := (hsgn₂₃.2.mp hs₂₃n)  -- θ₂ < θ₃
      have hθ₁₄ := (hsgn₁₄.2.mp hs₁₄n)  -- θ₁ < θ₄
      have hθ₂₁ := (hsgn₁₂.1.mp hs₁₂p)  -- θ₂ < θ₁
      have hθ₄₃ := (hsgn₃₄.1.mp hs₃₄p)  -- θ₄ < θ₃... wait: s₃₄ = sin((θ₃-θ₄)/2), >0 ↔ θ₄<θ₃
      -- θ₂ < θ₁ < θ₄ < θ₃; witnesses (θ₁, θ₄, θ₃, θ₂+2π) for IsCCWOrder z₁ z₄ z₃ z₂
      exact Or.inr ⟨θ₁, θ₄, θ₃, θ₂ + 2 * Real.pi,
        by linarith,
        by linarith,
        by linarith [hθ₃_bd.2, hθ₂_bd.1, hπ],
        by linarith [hθ₂_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₄, hz₃,
        by rw [hexp_add2pi]; exact hz₂⟩
    · -- D: s₂₃<0, s₁₄<0, s₁₂<0, s₃₄<0 → θ₁<θ₂<θ₃<θ₄ → CCW (IsCCWOrder z₁ z₂ z₃ z₄)
      have hθ₂₃ := (hsgn₂₃.2.mp hs₂₃n)  -- θ₂ < θ₃
      have hθ₁₄ := (hsgn₁₄.2.mp hs₁₄n)  -- θ₁ < θ₄
      have hθ₁₂ := (hsgn₁₂.2.mp hs₁₂n)  -- θ₁ < θ₂
      have hθ₃₄ := (hsgn₃₄.2.mp hs₃₄n)  -- θ₃ < θ₄
      -- θ₁ < θ₂ < θ₃ < θ₄; direct witnesses (θ₁, θ₂, θ₃, θ₄) for IsCCWOrder z₁ z₂ z₃ z₄
      exact Or.inl ⟨θ₁, θ₂, θ₃, θ₄,
        by linarith, by linarith, by linarith,
        by linarith [hθ₄_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₂, hz₃, hz₄⟩
  · rcases mul_neg_iff.mp hnum_neg with ⟨hs₂₃p, hs₁₄n⟩ | ⟨hs₂₃n, hs₁₄p⟩ <;>
    rcases mul_neg_iff.mp hden_neg with ⟨hs₁₂p, hs₃₄n⟩ | ⟨hs₁₂n, hs₃₄p⟩
    · -- E: s₂₃>0, s₁₄<0, s₁₂>0, s₃₄<0 → θ₃<θ₂<θ₁<θ₄ → CW (IsCCWOrder z₁ z₄ z₃ z₂)
      have hθ₃₂ := (hsgn₂₃.1.mp hs₂₃p)
      have hθ₁₄ := (hsgn₁₄.2.mp hs₁₄n)
      have hθ₂₁ := (hsgn₁₂.1.mp hs₁₂p)
      have hθ₃₄ := (hsgn₃₄.2.mp hs₃₄n)
      -- θ₃ < θ₂ < θ₁ < θ₄; witnesses (θ₁, θ₄, θ₃+2π, θ₂+2π) for IsCCWOrder z₁ z₄ z₃ z₂
      exact Or.inr ⟨θ₁, θ₄, θ₃ + 2 * Real.pi, θ₂ + 2 * Real.pi,
        by linarith,
        by linarith [hθ₄_bd.2, hθ₃_bd.1, hπ],
        by linarith,
        by linarith [hθ₂_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₄,
        by rw [hexp_add2pi]; exact hz₃,
        by rw [hexp_add2pi]; exact hz₂⟩
    · -- F: s₂₃>0, s₁₄<0, s₁₂<0, s₃₄>0 → θ₁<θ₄<θ₃<θ₂ → CW (IsCCWOrder z₁ z₄ z₃ z₂)
      have hθ₃₂ := (hsgn₂₃.1.mp hs₂₃p)  -- θ₃ < θ₂
      have hθ₁₄ := (hsgn₁₄.2.mp hs₁₄n)  -- θ₁ < θ₄
      have hθ₁₂ := (hsgn₁₂.2.mp hs₁₂n)  -- θ₁ < θ₂
      have hθ₄₃ := (hsgn₃₄.1.mp hs₃₄p)  -- θ₄ < θ₃
      -- θ₁ < θ₄ < θ₃ < θ₂; direct witnesses for IsCCWOrder z₁ z₄ z₃ z₂
      exact Or.inr ⟨θ₁, θ₄, θ₃, θ₂,
        by linarith, by linarith, by linarith,
        by linarith [hθ₂_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₄, hz₃, hz₂⟩
    · -- G: s₂₃<0, s₁₄>0, s₁₂>0, s₃₄<0 → θ₂<θ₃<θ₄<θ₁ → CCW (IsCCWOrder z₁ z₂ z₃ z₄)
      have hθ₂₃ := (hsgn₂₃.2.mp hs₂₃n)  -- θ₂ < θ₃
      have hθ₄₁ := (hsgn₁₄.1.mp hs₁₄p)  -- θ₄ < θ₁
      have hθ₂₁ := (hsgn₁₂.1.mp hs₁₂p)  -- θ₂ < θ₁
      have hθ₃₄ := (hsgn₃₄.2.mp hs₃₄n)  -- θ₃ < θ₄
      -- θ₂ < θ₃ < θ₄ < θ₁; witnesses (θ₁-2π, θ₂, θ₃, θ₄) for IsCCWOrder z₁ z₂ z₃ z₄
      exact Or.inl ⟨θ₁ - 2 * Real.pi, θ₂, θ₃, θ₄,
        by linarith [hθ₁_bd.2, hθ₂_bd.1, hπ],
        by linarith, by linarith, by linarith,
        by rw [hexp_sub2pi]; exact hz₁,
        hz₂, hz₃, hz₄⟩
    · -- H: s₂₃<0, s₁₄>0, s₁₂<0, s₃₄>0 → θ₄<θ₁<θ₂<θ₃ → CCW (IsCCWOrder z₁ z₂ z₃ z₄)
      have hθ₂₃ := (hsgn₂₃.2.mp hs₂₃n)  -- θ₂ < θ₃
      have hθ₄₁ := (hsgn₁₄.1.mp hs₁₄p)  -- θ₄ < θ₁
      have hθ₁₂ := (hsgn₁₂.2.mp hs₁₂n)  -- θ₁ < θ₂
      have hθ₄₃ := (hsgn₃₄.1.mp hs₃₄p)  -- θ₄ < θ₃
      -- θ₄ < θ₁ < θ₂ < θ₃; witnesses (θ₁, θ₂, θ₃, θ₄+2π) for IsCCWOrder z₁ z₂ z₃ z₄
      exact Or.inl ⟨θ₁, θ₂, θ₃, θ₄ + 2 * Real.pi,
        by linarith, by linarith,
        by linarith [hθ₃_bd.2, hθ₄_bd.1, hπ],
        by linarith [hθ₄_bd.2, hθ₁_bd.1, hπ],
        hz₁, hz₂, hz₃,
        by rw [hexp_add2pi]; exact hz₄⟩

/-! ## Section V: The Full Biconditional -/

/-- **Ptolemy Biconditional for Unit-Circle Points**:

For four distinct unit-circle points with nonzero opposite-side products:
  Ptolemy equality ↔ CCW order ∨ CW order (= IsCCWOrder z₁ z₄ z₃ z₂)

**Proof**:
- (←): Follows from `ptolemy_ratio_pos_of_ccw` (completed in PtolemysTheoremOQ01.lean)
  and `ptolemy_equality_of_proportional`.
- (→): New converse direction from `ptolemy_equality_implies_ccw_or_cw`.

**Significance**: Completes the equivalence chain from PtolemysTheoremOQ01.lean:
  Ptolemy equality ↔ SameRay ↔ R > 0 ↔ CCW or CW order -/
theorem ptolemy_equality_iff_ccw_or_cw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hdist₁₂ : z₁ ≠ z₂) (hdist₁₃ : z₁ ≠ z₃) (hdist₁₄ : z₁ ≠ z₄)
    (hdist₂₃ : z₂ ≠ z₃) (hdist₂₄ : z₂ ≠ z₄) (hdist₃₄ : z₃ ≠ z₄)
    (hdenom : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hnumer : (z₂ - z₃) * (z₁ - z₄) ≠ 0) :
    (‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) ↔
    (IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCCWOrder z₁ z₄ z₃ z₂) := by
  constructor
  · -- (→) Ptolemy equality → CCW or CW
    exact ptolemy_equality_implies_ccw_or_cw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄
      hdist₁₂ hdist₁₃ hdist₁₄ hdist₂₃ hdist₂₄ hdist₃₄ hdenom hnumer
  · -- (←) CCW or CW → Ptolemy equality
    rintro (hccw | hcw)
    · -- CCW → Ptolemy (from PtolemysTheoremOQ01)
      obtain ⟨t, ht_pos, ht_eq⟩ := ptolemy_ratio_pos_of_ccw z₁ z₂ z₃ z₄ hccw
      exact ptolemy_equality_of_proportional z₁ z₂ z₃ z₄ t ht_pos.le ht_eq
    · -- CW → Ptolemy: apply the CCW Ptolemy result to the reversed labeling (z₁ z₄ z₃ z₂)
      -- ptolemy_ratio_pos_of_ccw z₁ z₄ z₃ z₂ gives (z₄-z₃)(z₁-z₂) = t·(z₁-z₄)(z₃-z₂)
      -- ptolemy_equality_of_proportional z₁ z₄ z₃ z₂ gives ‖z₁-z₃‖·‖z₄-z₂‖ = ‖z₁-z₄‖·‖z₃-z₂‖ + ‖z₄-z₃‖·‖z₁-z₂‖
      -- which equals the target by norm_sub_rev and commutativity
      obtain ⟨t, ht_pos, ht_eq⟩ := ptolemy_ratio_pos_of_ccw z₁ z₄ z₃ z₂ hcw
      have h := ptolemy_equality_of_proportional z₁ z₄ z₃ z₂ t ht_pos.le ht_eq
      -- h : ‖z₁-z₃‖*‖z₄-z₂‖ = ‖z₁-z₄‖*‖z₃-z₂‖ + ‖z₄-z₃‖*‖z₁-z₂‖
      rw [norm_sub_rev z₄ z₂, norm_sub_rev z₃ z₂, norm_sub_rev z₄ z₃] at h
      -- h : ‖z₁-z₃‖*‖z₂-z₄‖ = ‖z₁-z₄‖*‖z₂-z₃‖ + ‖z₃-z₄‖*‖z₁-z₂‖
      linarith [mul_comm ‖z₁ - z₄‖ ‖z₂ - z₃‖, mul_comm ‖z₃ - z₄‖ ‖z₁ - z₂‖]

#check @ptolemy_equality_implies_ccw_or_cw
#check @ptolemy_equality_iff_ccw_or_cw

end PtolemysTheoremOQ01Incomplete01
