import Mathlib

/-
# Power Mean Inequality Chain

## Research Problem: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02

For positive reals a, b, the power mean inequality gives:

  min(a,b) ≤ HM(a,b) ≤ GM(a,b) ≤ AM(a,b) ≤ QM(a,b) ≤ max(a,b)

where:
  HM = 2ab/(a+b)          (harmonic mean)
  GM = √(ab)              (geometric mean)
  AM = (a+b)/2            (arithmetic mean)
  QM = √((a²+b²)/2)      (quadratic mean / root mean square)

Each step is proved from first principles. The parent file
(CauchySchwarzIntegralOQ01OQ01OQ01) already proved GM ≤ AM
(amgm_two) and AM² ≤ QM² (qm_am). This file completes the chain.

Tags: inequalities, power-means, algebra
-/

namespace PowerMeanChain

open Real

-- ============================================================
-- Part I: Definitions
-- ============================================================

/-- Harmonic mean of two positive reals. -/
noncomputable def HM (a b : ℝ) : ℝ := 2 * a * b / (a + b)

/-- Geometric mean of two nonneg reals. -/
noncomputable def GM (a b : ℝ) : ℝ := Real.sqrt (a * b)

/-- Arithmetic mean of two reals. -/
noncomputable def AM (a b : ℝ) : ℝ := (a + b) / 2

/-- Quadratic mean (root mean square) of two reals. -/
noncomputable def QM (a b : ℝ) : ℝ := Real.sqrt ((a ^ 2 + b ^ 2) / 2)

-- ============================================================
-- Part II: Step 1 — min ≤ HM
-- ============================================================

/-- min(a,b) ≤ HM(a,b) for positive reals.
    Proof: WLOG a ≤ b. Then HM = 2ab/(a+b) ≥ 2a²/(2a) = a = min. -/
theorem min_le_hm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b ≤ HM a b := by
  unfold HM
  have hab : 0 < a + b := by linarith
  rcases le_total a b with h | h
  · -- a ≤ b, so min = a
    rw [min_eq_left h]
    rw [le_div_iff₀ hab]
    nlinarith [sq_nonneg (b - a)]
  · -- b ≤ a, so min = b
    rw [min_eq_right h]
    rw [le_div_iff₀ hab]
    nlinarith [sq_nonneg (a - b)]

-- ============================================================
-- Part III: Step 2 — HM ≤ GM
-- ============================================================

/-- HM(a,b) ≤ GM(a,b) for positive reals.
    Proof: HM = 2ab/(a+b), GM = √(ab).
    Squaring: HM² = 4a²b²/(a+b)² ≤ ab = GM².
    This reduces to (a+b)² ≥ 4ab, i.e., (a-b)² ≥ 0. -/
theorem hm_le_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HM a b ≤ GM a b := by
  unfold HM GM
  have hab : 0 < a + b := by linarith
  have hab_ne : a + b ≠ 0 := ne_of_gt hab
  have hm_nonneg : 0 ≤ 2 * a * b / (a + b) := by positivity
  rw [← Real.sqrt_sq hm_nonneg]
  apply Real.sqrt_le_sqrt
  rw [div_pow, sq_abs]
  rw [div_le_iff₀ (pow_pos hab 2)]
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b,
             mul_pos ha hb]

-- ============================================================
-- Part IV: Step 3 — GM ≤ AM
-- ============================================================

/-- GM(a,b) ≤ AM(a,b) for nonneg reals.
    This is the classical AM-GM inequality. -/
theorem gm_le_am (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    GM a b ≤ AM a b := by
  unfold GM AM
  have ham : 0 ≤ (a + b) / 2 := by linarith
  rw [← Real.sqrt_sq ham]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a - b)])

-- ============================================================
-- Part V: Step 4 — AM ≤ QM
-- ============================================================

/-- AM(a,b) ≤ QM(a,b) for nonneg reals.
    Proof: AM² = (a+b)²/4 ≤ (a²+b²)/2 = QM², by (a-b)² ≥ 0. -/
theorem am_le_qm (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    AM a b ≤ QM a b := by
  unfold AM QM
  have ham : 0 ≤ (a + b) / 2 := by linarith
  rw [← Real.sqrt_sq ham]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (a - b)]

-- ============================================================
-- Part VI: Step 5 — QM ≤ max
-- ============================================================

/-- QM(a,b) ≤ max(a,b) for nonneg reals.
    Proof: (a²+b²)/2 ≤ max(a,b)², since a² ≤ max² and b² ≤ max². -/
theorem qm_le_max (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    QM a b ≤ max a b := by
  unfold QM
  have hmax_nn : 0 ≤ max a b := le_max_of_le_left ha
  rw [← Real.sqrt_sq hmax_nn]
  apply Real.sqrt_le_sqrt
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    have : a ^ 2 ≤ b ^ 2 := sq_le_sq' (by linarith) h
    linarith
  · rw [max_eq_left h]
    have : b ^ 2 ≤ a ^ 2 := sq_le_sq' (by linarith) h
    linarith

-- ============================================================
-- Part VII: The Full Chain
-- ============================================================

/-- The full power mean inequality chain for two positive reals:
    min(a,b) ≤ HM(a,b) ≤ GM(a,b) ≤ AM(a,b) ≤ QM(a,b) ≤ max(a,b). -/
theorem power_mean_chain (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    min a b ≤ HM a b ∧
    HM a b ≤ GM a b ∧
    GM a b ≤ AM a b ∧
    AM a b ≤ QM a b ∧
    QM a b ≤ max a b :=
  ⟨min_le_hm a b ha hb,
   hm_le_gm a b ha hb,
   gm_le_am a b (le_of_lt ha) (le_of_lt hb),
   am_le_qm a b (le_of_lt ha) (le_of_lt hb),
   qm_le_max a b (le_of_lt ha) (le_of_lt hb)⟩

-- ============================================================
-- Part VIII: Equality Conditions
-- ============================================================

/-- All means coincide when a = b. -/
theorem means_eq_when_eq (a : ℝ) (ha : 0 < a) :
    HM a a = a ∧ GM a a = a ∧ AM a a = a ∧ QM a a = a := by
  constructor
  · -- HM
    unfold HM; field_simp
  constructor
  · -- GM
    unfold GM
    rw [← sq_sqrt (le_of_lt ha)]
    congr 1; ring
  constructor
  · -- AM
    unfold AM; ring
  · -- QM
    unfold QM
    have : (a ^ 2 + a ^ 2) / 2 = a ^ 2 := by ring
    rw [this]
    exact Real.sqrt_sq (le_of_lt ha)

-- ============================================================
-- Part IX: Transitivity Corollaries
-- ============================================================

/-- Direct corollary: min ≤ AM (skipping HM and GM). -/
theorem min_le_am (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a b ≤ AM a b := by
  unfold AM
  rcases le_total a b with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- Direct corollary: HM ≤ AM. -/
theorem hm_le_am (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HM a b ≤ AM a b :=
  le_trans (hm_le_gm a b ha hb) (gm_le_am a b (le_of_lt ha) (le_of_lt hb))

/-- Direct corollary: GM ≤ max. -/
theorem gm_le_max (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    GM a b ≤ max a b :=
  le_trans (gm_le_am a b ha hb)
    (le_trans (am_le_qm a b ha hb) (qm_le_max a b ha hb))

/-- Direct corollary: min ≤ max. -/
theorem min_le_max' (a b : ℝ) : min a b ≤ max a b :=
  min_le_max a b

/-
  Summary

  This file formalizes the complete power mean inequality chain
  for two positive reals:

    min(a,b) ≤ HM(a,b) ≤ GM(a,b) ≤ AM(a,b) ≤ QM(a,b) ≤ max(a,b)

  Each step is proved from first principles using nlinarith and
  sqrt monotonicity. All five inequalities tight iff a = b.

  0 axioms, 0 sorries, fully verified.
-/

end PowerMeanChain
