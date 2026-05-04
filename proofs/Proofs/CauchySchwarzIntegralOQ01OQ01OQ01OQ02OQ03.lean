/-
Weighted Power Mean Inequality Chain

Open Question (cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03):
The weighted power mean M_p^w(a,b) = (w₁ aᵖ + w₂ bᵖ)^{1/p} for weights
w₁ + w₂ = 1 satisfies the same monotonicity. Does Mathlib contain the
infrastructure needed to formalize this generalization?

Answer: YES. Mathlib's Real.geom_mean_le_arith_mean2_weighted directly proves
wGM ≤ wAM. The wAM ≤ wQM step uses Jensen's inequality for x² (algebraic).
The wHM ≤ wGM step applies weighted AM-GM to the reciprocals a⁻¹, b⁻¹ via
Real.inv_rpow, then inverts the resulting bound.
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open Real

namespace WeightedPowerMean

variable {w₁ w₂ a b : ℝ}

-- ============================================================
-- Part I: Definitions
-- ============================================================

/-- Weighted harmonic mean: 1 / (w₁/a + w₂/b) for weights w₁ + w₂ = 1. -/
noncomputable def wHM (w₁ w₂ a b : ℝ) : ℝ := 1 / (w₁ / a + w₂ / b)

/-- Weighted geometric mean: a^w₁ · b^w₂ (real exponents via rpow). -/
noncomputable def wGM (w₁ w₂ a b : ℝ) : ℝ := a ^ w₁ * b ^ w₂

/-- Weighted arithmetic mean: w₁·a + w₂·b. -/
noncomputable def wAM (w₁ w₂ a b : ℝ) : ℝ := w₁ * a + w₂ * b

/-- Weighted quadratic mean: √(w₁·a² + w₂·b²). -/
noncomputable def wQM (w₁ w₂ a b : ℝ) : ℝ := Real.sqrt (w₁ * a ^ 2 + w₂ * b ^ 2)

-- ============================================================
-- Part II: wGM ≤ wAM (Weighted AM-GM — direct Mathlib application)
-- ============================================================

/-- **Weighted AM-GM**: a^w₁ · b^w₂ ≤ w₁·a + w₂·b for weights w₁ + w₂ = 1.
    A direct application of Real.geom_mean_le_arith_mean2_weighted. -/
theorem wGM_le_wAM (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hwsum : w₁ + w₂ = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    wGM w₁ w₂ a b ≤ wAM w₁ w₂ a b :=
  Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ ha hb hwsum

-- ============================================================
-- Part III: wAM ≤ wQM (Jensen for x²)
-- ============================================================

/-- **Weighted AM ≤ Weighted QM**: Jensen for convex x².
    Proof: (w₁a + w₂b)² ≤ w₁a² + w₂b² ⟺ w₁w₂(a-b)² ≥ 0. -/
theorem wAM_le_wQM (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hwsum : w₁ + w₂ = 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    wAM w₁ w₂ a b ≤ wQM w₁ w₂ a b := by
  unfold wAM wQM
  have ham_nn : 0 ≤ w₁ * a + w₂ * b := by positivity
  rw [← Real.sqrt_sq ham_nn]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - b), mul_nonneg hw₁ hw₂,
             mul_nonneg (mul_nonneg hw₁ hw₂) (sq_nonneg (a - b))]

-- ============================================================
-- Part IV: wHM ≤ wGM (reciprocal argument)
-- ============================================================

/-- **Weighted HM ≤ Weighted GM**: Apply weighted AM-GM to a⁻¹ and b⁻¹.
    Key: (a⁻¹)^w₁ · (b⁻¹)^w₂ = (a^w₁ · b^w₂)⁻¹ ≤ w₁/a + w₂/b;
    inverting (both sides positive) yields 1/(w₁/a+w₂/b) ≤ a^w₁·b^w₂. -/
theorem wHM_le_wGM (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hwsum : w₁ + w₂ = 1)
    (ha : 0 < a) (hb : 0 < b) :
    wHM w₁ w₂ a b ≤ wGM w₁ w₂ a b := by
  unfold wHM wGM
  have hgm_pos : 0 < a ^ w₁ * b ^ w₂ :=
    mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  have hwab_pos : 0 < w₁ / a + w₂ / b := by positivity
  -- Apply weighted AM-GM to a⁻¹ and b⁻¹
  have h := Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂
    (le_of_lt (inv_pos.mpr ha)) (le_of_lt (inv_pos.mpr hb)) hwsum
  -- h : a⁻¹ ^ w₁ * b⁻¹ ^ w₂ ≤ w₁ * a⁻¹ + w₂ * b⁻¹
  rw [Real.inv_rpow ha.le, Real.inv_rpow hb.le, ← mul_inv] at h
  -- h : (a ^ w₁ * b ^ w₂)⁻¹ ≤ w₁ * a⁻¹ + w₂ * b⁻¹
  have h2 : (a ^ w₁ * b ^ w₂)⁻¹ ≤ w₁ / a + w₂ / b := by
    convert h using 1
    simp [div_eq_mul_inv]
  -- Invert: 1/(w₁/a + w₂/b) ≤ a^w₁ * b^w₂
  have hgm_inv_pos : 0 < (a ^ w₁ * b ^ w₂)⁻¹ := inv_pos.mpr hgm_pos
  have key := one_div_le_one_div_of_le hgm_inv_pos h2
  simp only [one_div, inv_inv] at key
  rwa [one_div]

-- ============================================================
-- Part V: The Full Weighted Chain
-- ============================================================

/-- **Full Weighted Mean Chain**: For w₁, w₂ ≥ 0 with w₁ + w₂ = 1 and
    positive reals a, b: wHM ≤ wGM ≤ wAM ≤ wQM. -/
theorem weighted_mean_chain (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hwsum : w₁ + w₂ = 1)
    (ha : 0 < a) (hb : 0 < b) :
    wHM w₁ w₂ a b ≤ wGM w₁ w₂ a b ∧
    wGM w₁ w₂ a b ≤ wAM w₁ w₂ a b ∧
    wAM w₁ w₂ a b ≤ wQM w₁ w₂ a b :=
  ⟨wHM_le_wGM hw₁ hw₂ hwsum ha hb,
   wGM_le_wAM hw₁ hw₂ hwsum ha.le hb.le,
   wAM_le_wQM hw₁ hw₂ hwsum ha.le hb.le⟩

-- ============================================================
-- Part VI: Connection to Standard Means (w₁ = w₂ = 1/2)
-- ============================================================

/-- Equal weights (1/2, 1/2) recover the standard geometric and arithmetic means. -/
theorem equal_weight_recovers_gm (ha : 0 ≤ a) (hb : 0 ≤ b) :
    wGM (1/2) (1/2) a b = Real.sqrt (a * b) := by
  unfold wGM
  simp only [← Real.sqrt_eq_rpow]
  exact (Real.sqrt_mul ha b).symm

theorem equal_weight_recovers_am (a b : ℝ) :
    wAM (1/2) (1/2) a b = (a + b) / 2 := by
  unfold wAM; ring

/-- The equal-weight chain specializes to the standard HM-GM-AM-QM chain. -/
theorem equal_weight_chain (ha : 0 < a) (hb : 0 < b) :
    wHM (1/2) (1/2) a b ≤ wGM (1/2) (1/2) a b ∧
    wGM (1/2) (1/2) a b ≤ wAM (1/2) (1/2) a b ∧
    wAM (1/2) (1/2) a b ≤ wQM (1/2) (1/2) a b :=
  weighted_mean_chain (by norm_num) (by norm_num) (by norm_num) ha hb

-- ============================================================
-- Part VII: Equality Condition
-- ============================================================

/-- All weighted means coincide when a = b. -/
theorem weighted_means_eq_at_diagonal (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hwsum : w₁ + w₂ = 1) (ha : 0 < a) :
    wHM w₁ w₂ a a = a ∧
    wGM w₁ w₂ a a = a ∧
    wAM w₁ w₂ a a = a ∧
    wQM w₁ w₂ a a = a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- wHM
    unfold wHM
    field_simp [ha.ne']
    linarith
  · -- wGM
    unfold wGM
    rw [← Real.rpow_add ha, hwsum, Real.rpow_one]
  · -- wAM
    unfold wAM; linarith
  · -- wQM
    unfold wQM
    have h : w₁ * a ^ 2 + w₂ * a ^ 2 = a ^ 2 := by nlinarith
    rw [h, Real.sqrt_sq ha.le]

end WeightedPowerMean
