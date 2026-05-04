import Mathlib

/-
# Weighted Power Mean Chain: WHM ≤ WGM ≤ WAM ≤ WQM

## Research Problem: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03

The parent file `CauchySchwarzIntegralOQ01OQ01OQ01OQ02.lean` proved the unweighted
power mean chain HM ≤ GM ≤ AM ≤ QM for two positive reals. The sibling OQ02 showed
that `ring + positivity` automation closes all goals hint-free. Here we answer:

> Does the full chain generalize to WEIGHTED means with weights w₁, w₂ > 0, w₁ + w₂ = 1?

Weighted definitions:
  WHM(a,b) = (w₁/a + w₂/b)⁻¹         (weighted harmonic mean)
  WGM(a,b) = a^w₁ · b^w₂              (weighted geometric mean)
  WAM(a,b) = w₁·a + w₂·b              (weighted arithmetic mean)
  WQM(a,b) = √(w₁·a² + w₂·b²)        (weighted quadratic mean)

## Answer: YES

We prove WHM ≤ WGM ≤ WAM ≤ WQM for all a, b > 0 and weights w₁, w₂ > 0 with
w₁ + w₂ = 1. Each step uses a different technique:

- WGM ≤ WAM: Directly from Mathlib's `Real.geom_mean_le_arith_mean2_weighted`
- WAM ≤ WQM: Jensen's inequality: w₁·a² + w₂·b² - (w₁·a + w₂·b)² = w₁·w₂·(a-b)² ≥ 0
- WHM ≤ WGM: Apply WGM ≤ WAM to (1/a, 1/b), then take reciprocals (inv-antitone)

## Specialization to Equal Weights

Setting w₁ = w₂ = 1/2 recovers the unweighted chain: HM = 2ab/(a+b),
GM = √(ab), AM = (a+b)/2, QM = √((a²+b²)/2).

Tags: inequalities, power-means, weighted, AM-GM, Jensen, research
-/

namespace WeightedPowerMeanChain

open Real

variable {a b w₁ w₂ : ℝ}

-- ============================================================
-- Part I: Definitions
-- ============================================================

/-- Weighted harmonic mean: (w₁/a + w₂/b)⁻¹ -/
noncomputable def WHM (w₁ w₂ a b : ℝ) : ℝ := (w₁ / a + w₂ / b)⁻¹

/-- Weighted geometric mean: a^w₁ · b^w₂ -/
noncomputable def WGM (w₁ w₂ a b : ℝ) : ℝ := a ^ w₁ * b ^ w₂

/-- Weighted arithmetic mean: w₁·a + w₂·b -/
noncomputable def WAM (w₁ w₂ a b : ℝ) : ℝ := w₁ * a + w₂ * b

/-- Weighted quadratic mean: √(w₁·a² + w₂·b²) -/
noncomputable def WQM (w₁ w₂ a b : ℝ) : ℝ := Real.sqrt (w₁ * a ^ 2 + w₂ * b ^ 2)

-- ============================================================
-- Part II: Positivity Lemmas
-- ============================================================

lemma whm_pos (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    0 < WHM w₁ w₂ a b := by
  unfold WHM
  apply inv_pos.mpr
  positivity

lemma wgm_pos (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    0 < WGM w₁ w₂ a b := by
  unfold WGM
  positivity

lemma wam_pos (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    0 < WAM w₁ w₂ a b := by
  unfold WAM
  positivity

lemma wqm_nonneg (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    0 ≤ WQM w₁ w₂ a b := by
  unfold WQM
  positivity

-- ============================================================
-- Part III: WGM ≤ WAM (Weighted AM-GM)
-- ============================================================

/-- Weighted AM-GM: a^w₁ · b^w₂ ≤ w₁·a + w₂·b.
    Direct corollary of Mathlib's `Real.geom_mean_le_arith_mean2_weighted`. -/
theorem wgm_le_wam (ha : 0 ≤ a) (hb : 0 ≤ b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : w₁ + w₂ = 1) : WGM w₁ w₂ a b ≤ WAM w₁ w₂ a b := by
  unfold WGM WAM
  exact Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ ha hb hw

-- ============================================================
-- Part IV: WAM ≤ WQM (Weighted AM-QM via Jensen)
-- ============================================================

/-- Jensen's inequality for f(x) = x²: the weighted variance is nonneg.
    Key identity: w₁·a² + w₂·b² - (w₁·a + w₂·b)² = w₁·w₂·(a - b)². -/
lemma weighted_variance_nonneg (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw : w₁ + w₂ = 1) :
    (w₁ * a + w₂ * b) ^ 2 ≤ w₁ * a ^ 2 + w₂ * b ^ 2 := by
  have hw₂_eq : w₂ = 1 - w₁ := by linarith
  rw [hw₂_eq]
  have key : w₁ * (1 - w₁) * (a - b) ^ 2 =
      w₁ * a ^ 2 + (1 - w₁) * b ^ 2 - (w₁ * a + (1 - w₁) * b) ^ 2 := by ring
  linarith [mul_nonneg (mul_nonneg hw₁ (by linarith : 0 ≤ 1 - w₁)) (sq_nonneg (a - b))]

/-- Weighted AM ≤ weighted QM: w₁·a + w₂·b ≤ √(w₁·a² + w₂·b²). -/
theorem wam_le_wqm (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : w₁ + w₂ = 1) : WAM w₁ w₂ a b ≤ WQM w₁ w₂ a b := by
  unfold WAM WQM
  have h_wam_nn : 0 ≤ w₁ * a + w₂ * b := by positivity
  rw [← Real.sqrt_sq h_wam_nn]
  apply Real.sqrt_le_sqrt
  exact weighted_variance_nonneg hw₁ hw₂ hw

-- ============================================================
-- Part V: WHM ≤ WGM (Weighted HM-GM via reciprocals)
-- ============================================================

/-- Auxiliary: (1/a)^w₁ · (1/b)^w₂ = (a^w₁ · b^w₂)⁻¹ for a, b > 0. -/
private lemma inv_wgm_eq (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) :
    (1 / a) ^ w₁ * (1 / b) ^ w₂ = (a ^ w₁ * b ^ w₂)⁻¹ := by
  have ha' := Real.rpow_pos_of_pos ha w₁
  have hb' := Real.rpow_pos_of_pos hb w₂
  rw [Real.div_rpow (by norm_num) ha.le, Real.div_rpow (by norm_num) hb.le,
      Real.one_rpow, Real.one_rpow]
  field_simp [ne_of_gt ha', ne_of_gt hb']

/-- Weighted HM ≤ weighted GM.
    Strategy: apply WGM ≤ WAM to (1/a, 1/b) with the same weights to get
      (1/a)^w₁·(1/b)^w₂ ≤ w₁·(1/a) + w₂·(1/b)
    i.e., WGM(a,b)⁻¹ ≤ WHM(a,b)⁻¹. Since both are positive, taking reciprocals gives
    WHM(a,b) ≤ WGM(a,b). -/
theorem whm_le_wgm (ha : 0 < a) (hb : 0 < b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (hw : w₁ + w₂ = 1) : WHM w₁ w₂ a b ≤ WGM w₁ w₂ a b := by
  unfold WHM WGM
  have hWGM_pos : 0 < a ^ w₁ * b ^ w₂ := by positivity
  have hWHM_inv_pos : 0 < w₁ / a + w₂ / b := by positivity
  -- Apply weighted AM-GM to (1/a) and (1/b)
  have h_amgm := Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂
    (by positivity : (0 : ℝ) ≤ 1 / a) (by positivity : (0 : ℝ) ≤ 1 / b) hw
  -- Rewrite LHS: (1/a)^w₁ * (1/b)^w₂ = WGM(a,b)⁻¹
  rw [inv_wgm_eq ha hb hw₁ hw₂] at h_amgm
  -- Rewrite RHS: w₁*(1/a) + w₂*(1/b) = w₁/a + w₂/b = WHM(a,b)⁻¹
  have hrhs : w₁ * (1 / a) + w₂ * (1 / b) = w₁ / a + w₂ / b := by ring
  rw [hrhs] at h_amgm
  -- Now h_amgm : WGM⁻¹ ≤ WHM_inv where WHM = WHM_inv⁻¹
  -- i.e., (a^w₁ * b^w₂)⁻¹ ≤ (w₁/a + w₂/b)
  -- Goal: (w₁/a + w₂/b)⁻¹ ≤ a^w₁ * b^w₂
  -- This follows from inv-antitone: x⁻¹ ≤ y → y⁻¹ ≤ x (for x,y > 0)
  rwa [inv_le_comm₀ hWHM_inv_pos hWGM_pos]

-- ============================================================
-- Part VI: Main Chain Theorem
-- ============================================================

/-- **Weighted Power Mean Chain**: WHM ≤ WGM ≤ WAM ≤ WQM.
    Holds for all a, b > 0 and weights w₁, w₂ > 0 with w₁ + w₂ = 1. -/
theorem weighted_mean_chain (ha : 0 < a) (hb : 0 < b)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hw : w₁ + w₂ = 1) :
    WHM w₁ w₂ a b ≤ WGM w₁ w₂ a b ∧
    WGM w₁ w₂ a b ≤ WAM w₁ w₂ a b ∧
    WAM w₁ w₂ a b ≤ WQM w₁ w₂ a b := by
  exact ⟨whm_le_wgm ha hb hw₁.le hw₂.le hw,
         wgm_le_wam ha.le hb.le hw₁.le hw₂.le hw,
         wam_le_wqm ha hb hw₁.le hw₂.le hw⟩

-- ============================================================
-- Part VII: Specialization to Equal Weights
-- ============================================================

/-- At equal weights w₁ = w₂ = 1/2, WHM equals the standard harmonic mean 2ab/(a+b). -/
theorem whm_half_eq_hm (ha : 0 < a) (hb : 0 < b) :
    WHM (1/2) (1/2) a b = 2 * a * b / (a + b) := by
  unfold WHM
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hab' : a + b ≠ 0 := by linarith
  field_simp [ha', hb', hab']
  ring

/-- At equal weights, WGM equals the standard geometric mean √(ab). -/
theorem wgm_half_eq_gm (ha : 0 ≤ a) (hb : 0 ≤ b) :
    WGM (1/2) (1/2) a b = Real.sqrt (a * b) := by
  unfold WGM
  rw [← Real.mul_rpow ha hb, ← Real.sqrt_eq_rpow]

/-- At equal weights, WAM equals the standard arithmetic mean (a+b)/2. -/
theorem wam_half_eq_am : WAM (1/2) (1/2) a b = (a + b) / 2 := by
  unfold WAM; ring

/-- At equal weights, WQM equals the standard quadratic mean √((a²+b²)/2). -/
theorem wqm_half_eq_qm : WQM (1/2) (1/2) a b = Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  unfold WQM
  congr 1
  ring

/-- The unweighted power mean chain HM ≤ GM ≤ AM ≤ QM is a special case
    of the weighted chain at w₁ = w₂ = 1/2. -/
theorem unweighted_chain_from_weighted (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ≤ Real.sqrt (a * b) ∧
    Real.sqrt (a * b) ≤ (a + b) / 2 ∧
    (a + b) / 2 ≤ Real.sqrt ((a ^ 2 + b ^ 2) / 2) := by
  have ⟨h1, h2, h3⟩ := weighted_mean_chain ha hb (by norm_num) (by norm_num) (by ring)
  rw [whm_half_eq_hm ha hb, wgm_half_eq_gm ha.le hb.le, wam_half_eq_am, wqm_half_eq_qm] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

end WeightedPowerMeanChain
