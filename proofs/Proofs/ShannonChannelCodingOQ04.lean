/-
  Binary Entropy Function

  Formalizes h(p) = -p·ln(p) - (1-p)·ln(1-p) and its fundamental properties.
  Uses natural logarithm (consistent with Shannon entropy framework).

  Key results:
  - Boundary values: h(0) = h(1) = 0
  - Symmetry: h(p) = h(1-p)
  - Non-negativity on [0,1]
  - Maximum value: h(1/2) = ln 2 (= 1 bit)
  - Upper bound: h(p) ≤ ln 2 via binary Gibbs inequality
  - Characterization: h(p) = 0 iff p ∈ {0, 1}
  - Concavity on [0,1]

  Part of Shannon information theory formalization.
  Claude Shannon (1948)
-/
import Mathlib

namespace InformationTheory.BinaryEntropy

open Real

/-- Binary entropy function (natural logarithm).
    h(p) = -(p · log p + (1-p) · log(1-p))
    Convention: 0 · log 0 = 0 (Mathlib: Real.log 0 = 0). -/
noncomputable def h (p : ℝ) : ℝ :=
  -(p * log p + (1 - p) * log (1 - p))

/-- Binary entropy in bits (base 2). h₂(p) = h(p) / ln 2 -/
noncomputable def hBits (p : ℝ) : ℝ := h p / log 2

-- ============================================================
-- Boundary Values
-- ============================================================

@[simp] theorem h_zero : h 0 = 0 := by
  simp [h, log_one]

@[simp] theorem h_one : h 1 = 0 := by
  simp [h, log_one]

-- ============================================================
-- Symmetry
-- ============================================================

/-- Binary entropy is symmetric: h(p) = h(1-p). -/
theorem h_symm (p : ℝ) : h p = h (1 - p) := by
  simp only [h, sub_sub_cancel]
  ring

-- ============================================================
-- Value at 1/2
-- ============================================================

/-- h(1/2) = ln 2. This is the maximum entropy for a binary source. -/
theorem h_half : h (1 / 2) = log 2 := by
  simp only [h]
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by ring
  rw [h1]
  have h2 : (1 / 2 : ℝ) * log (1 / 2) + 1 / 2 * log (1 / 2) = log (1 / 2) := by ring
  rw [h2]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by norm_num]
  rw [log_inv, neg_neg]

/-- h₂(1/2) = 1 bit. The maximum binary entropy. -/
theorem hBits_half : hBits (1 / 2) = 1 := by
  simp only [hBits, h_half]
  exact div_self (ne_of_gt (log_pos (by norm_num : (1 : ℝ) < 2)))

-- ============================================================
-- Non-negativity
-- ============================================================

/-- For 0 < t ≤ 1: t · log t ≤ 0. -/
private lemma mul_log_nonpos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * log t ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) (log_nonpos (le_of_lt ht0) ht1)

/-- Binary entropy is non-negative on [0,1]. -/
theorem h_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ h p := by
  simp only [h, neg_nonneg]
  apply add_nonpos
  · rcases eq_or_lt_of_le hp0 with rfl | hp_pos
    · simp
    · exact mul_log_nonpos hp_pos hp1
  · rcases eq_or_lt_of_le (show 0 ≤ 1 - p by linarith) with h1p_eq | h1p_pos
    · simp [← h1p_eq]
    · exact mul_log_nonpos h1p_pos (by linarith)

-- ============================================================
-- Upper Bound: h(p) ≤ ln 2
-- ============================================================

/-- KL divergence term bound: p·log(p/q) ≥ p - q for p, q > 0.
    The kernel of Gibbs inequality. From log(x) ≤ x - 1. -/
private lemma kl_term_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p * log (p / q) ≥ p - q := by
  have h1 : log (q / p) ≤ q / p - 1 := log_le_sub_one_of_pos (div_pos hq hp)
  have h2 : p * log (q / p) ≤ q - p :=
    calc p * log (q / p)
        ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
      _ = q - p := by field_simp
  have h3 : log (p / q) = -log (q / p) := by
    rw [log_div (ne_of_gt hp) (ne_of_gt hq), log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  have h4 : p * log (p / q) = -(p * log (q / p)) := by rw [h3]; ring
  linarith

/-- Binary entropy is at most ln 2 (= 1 bit).
    Proof via binary Gibbs inequality with uniform reference measure. -/
theorem h_le_log_two {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : h p ≤ log 2 := by
  -- Boundary cases
  rcases eq_or_lt_of_le hp0 with rfl | hp_pos
  · rw [h_zero]; exact le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))
  rcases eq_or_lt_of_le hp1 with rfl | hp_lt1
  · rw [h_one]; exact le_of_lt (log_pos (by norm_num : (1 : ℝ) < 2))
  -- Interior: 0 < p < 1. Apply KL term bound with reference q = 1/2.
  have h1p : 0 < 1 - p := by linarith
  have hkl1 := kl_term_bound hp_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have hkl2 := kl_term_bound h1p (show (0 : ℝ) < 1 / 2 by norm_num)
  -- Simplify: p/(1/2) = 2p
  have hs1 : p / (1 / 2 : ℝ) = 2 * p := by ring
  have hs2 : (1 - p) / (1 / 2 : ℝ) = 2 * (1 - p) := by ring
  rw [hs1] at hkl1; rw [hs2] at hkl2
  -- Expand log(2x) = log 2 + log x
  have hl1 : log (2 * p) = log 2 + log p :=
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hp_pos)
  have hl2 : log (2 * (1 - p)) = log 2 + log (1 - p) :=
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt h1p)
  rw [hl1] at hkl1; rw [hl2] at hkl2
  -- hkl1: p * (log 2 + log p) ≥ p - 1/2  (i.e., p - 1/2 ≤ LHS)
  -- hkl2: (1-p) * (log 2 + log(1-p)) ≥ (1-p) - 1/2  (i.e., 1/2-p ≤ LHS)
  -- Sum: 0 ≤ p*(log 2 + log p) + (1-p)*(log 2 + log(1-p))
  --      = log 2 + (p*log p + (1-p)*log(1-p))
  have sum := add_le_add hkl1 hkl2
  have sum_lhs : (p - 1 / 2) + ((1 - p) - 1 / 2) = (0 : ℝ) := by ring
  have expand : p * (log 2 + log p) + (1 - p) * (log 2 + log (1 - p)) =
    log 2 + (p * log p + (1 - p) * log (1 - p)) := by ring
  rw [sum_lhs, expand] at sum
  -- sum: 0 ≤ log 2 + (p * log p + (1-p) * log(1-p))
  -- Goal: h p = -(p * log p + (1-p) * log(1-p)) ≤ log 2
  simp only [h]
  linarith

/-- Binary entropy in bits is at most 1. -/
theorem hBits_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : hBits p ≤ 1 := by
  simp only [hBits]
  rw [div_le_one (log_pos (by norm_num : (1 : ℝ) < 2))]
  exact h_le_log_two hp0 hp1

-- ============================================================
-- Characterization: h(p) = 0 iff p ∈ {0, 1}
-- ============================================================

/-- Binary entropy vanishes only for deterministic distributions. -/
theorem h_eq_zero_iff {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    h p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor
  · intro hzero
    simp only [h, neg_eq_zero] at hzero
    -- Both terms ≤ 0 and sum = 0, so each = 0
    by_contra hne
    push_neg at hne
    obtain ⟨hp_ne0, hp_ne1⟩ := hne
    have hp_pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp_ne0)
    have hp_lt1 : p < 1 := lt_of_le_of_ne hp1 hp_ne1
    have h1p_pos : 0 < 1 - p := by linarith
    have h1p_lt1 : 1 - p < 1 := by linarith
    -- Each term is strictly negative for 0 < x < 1
    have hlog_p : log p < 0 := by
      have := log_lt_log hp_pos hp_lt1
      rwa [log_one] at this
    have hlog_1p : log (1 - p) < 0 := by
      have := log_lt_log h1p_pos h1p_lt1
      rwa [log_one] at this
    have hterm1 : p * log p < 0 := mul_neg_of_pos_of_neg hp_pos hlog_p
    have hterm2 : (1 - p) * log (1 - p) < 0 := mul_neg_of_pos_of_neg h1p_pos hlog_1p
    linarith
  · rintro (rfl | rfl)
    · exact h_zero
    · exact h_one

-- ============================================================
-- Concavity
-- ============================================================

/-- Binary entropy is concave on [0,1].
    Proof: directly from convexity of x·log(x) on [0,∞) (Mathlib). -/
theorem h_concaveOn : ConcaveOn ℝ (Set.Icc 0 1) h := by
  have hconv := convexOn_mul_log
  constructor
  · exact convex_Icc 0 1
  · intro x hx y hy a b ha hb hab
    simp only [h, smul_eq_mul]
    -- Apply convexity of t*log(t) at points x, y and at 1-x, 1-y
    have hx_mem : x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hx.1
    have hy_mem : y ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr hy.1
    have h1x_mem : 1 - x ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith [hx.2])
    have h1y_mem : 1 - y ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.mpr (by linarith [hy.2])
    have hI_raw := hconv.2 hx_mem hy_mem ha hb hab
    have hII_raw := hconv.2 h1x_mem h1y_mem ha hb hab
    -- Extract concrete inequalities from ConvexOn
    have hI : (a * x + b * y) * log (a * x + b * y) ≤
        a * (x * log x) + b * (y * log y) := by
      have := hI_raw; simp only [smul_eq_mul] at this; exact this
    have hII_pre : (a * (1 - x) + b * (1 - y)) * log (a * (1 - x) + b * (1 - y)) ≤
        a * ((1 - x) * log (1 - x)) + b * ((1 - y) * log (1 - y)) := by
      have := hII_raw; simp only [smul_eq_mul] at this; exact this
    -- Substitute: a*(1-x) + b*(1-y) = 1 - (a*x + b*y)
    have hsub : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by nlinarith
    rw [hsub] at hII_pre
    -- Add (I) and (II), then negate to get the goal
    have combined := add_le_add hI hII_pre
    -- Ring identity: goal LHS = -(RHS of combined)
    have lhs_eq : a * -(x * log x + (1 - x) * log (1 - x)) +
        b * -(y * log y + (1 - y) * log (1 - y)) =
        -(a * (x * log x) + b * (y * log y) +
         (a * ((1 - x) * log (1 - x)) + b * ((1 - y) * log (1 - y)))) := by ring
    rw [lhs_eq]
    linarith

end InformationTheory.BinaryEntropy
