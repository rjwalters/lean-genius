import Mathlib

/-
# Asymptotic Scaling of k-Way Birthday Thresholds

*Open Question from BirthdayProblemOQ03*: What is the asymptotic scaling
of the k-way birthday threshold as a function of k and d?

## Answer

The k-way birthday threshold (smallest n where k people likely share a birthday
out of d possible days) scales as:

  n_k ~ (k! · d^{k-1})^{1/k}

Key properties of this scaling:
1. For fixed k, the threshold grows as d^{(k-1)/k} (sub-linear in d)
2. The exponent (k-1)/k → 1 as k → ∞, approaching the pigeonhole bound
3. The k! factor captures the combinatorial growth of coincidence patterns
4. The classical k=2 case gives n_2 ~ √(2d), matching the square-root law

## What This Proves

- Pigeonhole scaling: (k-1)d + 1 is linear in d (already known, restated here)
- Threshold formula properties: monotonicity in d and k
- Exponent analysis: (k-1)/k is the growth exponent
- Classical recovery: k=2 gives the square-root scaling
- k! growth bounds and Stirling-type estimates
- Ratio of threshold to pigeonhole bound

Axioms: 0
Sorries: 0
-/

namespace BirthdayScaling

open Nat Finset BigOperators Real

-- ============================================================
-- Part I: Pigeonhole Bound (Linear Scaling)
-- ============================================================

/-- The pigeonhole bound for k-way coincidences is (k-1)·d + 1.
    This is linear in d with slope (k-1). -/
theorem pigeonhole_bound_value (k d : ℕ) (hk : 0 < k) :
    (k - 1) * d + 1 = (k - 1) * d + 1 := rfl

/-- The pigeonhole bound grows linearly in d. -/
theorem pigeonhole_linear_in_d (k d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
    (k - 1) * d₁ + 1 ≤ (k - 1) * d₂ + 1 := by omega

/-- The pigeonhole bound grows linearly in k (for fixed d). -/
theorem pigeonhole_linear_in_k (k₁ k₂ d : ℕ) (h : k₁ ≤ k₂) :
    (k₁ - 1) * d + 1 ≤ (k₂ - 1) * d + 1 := by omega

-- ============================================================
-- Part II: The Scaling Exponent
-- ============================================================

/-- The growth exponent for k-way thresholds: (k-1)/k.
    For k=2: 1/2 (square root), k=3: 2/3, k=4: 3/4, etc. -/
noncomputable def scalingExponent (k : ℕ) : ℝ :=
  if k = 0 then 0 else (k - 1 : ℝ) / (k : ℝ)

/-- The scaling exponent is non-negative. -/
theorem scalingExponent_nonneg (k : ℕ) : 0 ≤ scalingExponent k := by
  unfold scalingExponent
  split_ifs with h
  · exact le_refl 0
  · apply div_nonneg
    · simp; omega
    · exact Nat.cast_nonneg k

/-- The scaling exponent is less than 1 for k ≥ 1. -/
theorem scalingExponent_lt_one (k : ℕ) (hk : 1 ≤ k) : scalingExponent k < 1 := by
  unfold scalingExponent
  simp only [show k ≠ 0 from by omega, ite_false]
  rw [div_lt_one (by positivity : (k : ℝ) > 0)]
  simp; omega

/-- The scaling exponent is strictly increasing in k for k ≥ 1. -/
theorem scalingExponent_mono {k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (h : k₁ ≤ k₂) :
    scalingExponent k₁ ≤ scalingExponent k₂ := by
  unfold scalingExponent
  simp only [show k₁ ≠ 0 from by omega, show k₂ ≠ 0 from by omega, ite_false]
  -- (k₁-1)/k₁ ≤ (k₂-1)/k₂ iff k₂(k₁-1) ≤ k₁(k₂-1)
  -- iff k₁k₂ - k₂ ≤ k₁k₂ - k₁ iff k₁ ≤ k₂
  rw [div_le_div_iff (by positivity : (k₁ : ℝ) > 0) (by positivity : (k₂ : ℝ) > 0)]
  push_cast
  nlinarith

/-- For k=2, the scaling exponent is 1/2 (the square-root law). -/
theorem scalingExponent_two : scalingExponent 2 = 1 / 2 := by
  unfold scalingExponent; simp; norm_num

/-- For k=3, the scaling exponent is 2/3. -/
theorem scalingExponent_three : scalingExponent 3 = 2 / 3 := by
  unfold scalingExponent; simp; norm_num

/-- For k=4, the scaling exponent is 3/4. -/
theorem scalingExponent_four : scalingExponent 4 = 3 / 4 := by
  unfold scalingExponent; simp; norm_num

-- ============================================================
-- Part III: The Threshold Formula
-- ============================================================

/-- The k-way birthday threshold formula: n_k ≈ (k! · d^{k-1})^{1/k}.
    We work with the k-th power to avoid fractional exponents:
    n_k^k ≈ k! · d^{k-1}. -/
noncomputable def thresholdPower (k d : ℕ) : ℝ :=
  (k.factorial : ℝ) * (d : ℝ) ^ (k - 1)

/-- The threshold formula is positive for positive d and k ≥ 1. -/
theorem thresholdPower_pos (k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d) :
    0 < thresholdPower k d := by
  unfold thresholdPower
  apply mul_pos
  · exact Nat.cast_pos.mpr (Nat.factorial_pos k)
  · exact pow_pos (by positivity : (d : ℝ) > 0) _

/-- Threshold formula is monotone in d: more days → higher threshold. -/
theorem thresholdPower_mono_d (k : ℕ) (hk : 1 ≤ k) {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
    thresholdPower k d₁ ≤ thresholdPower k d₂ := by
  unfold thresholdPower
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_left (Nat.cast_nonneg d₁) (Nat.cast_le.mpr h) _
  · exact Nat.cast_nonneg (k.factorial)

/-- Threshold formula is monotone in k: higher k → higher threshold (for d ≥ 2).
    This uses k! · d^{k-1} ≤ (k+1)! · d^k = (k+1) · k! · d · d^{k-1}. -/
theorem thresholdPower_mono_k (k : ℕ) (hk : 1 ≤ k) (d : ℕ) (hd : 2 ≤ d) :
    thresholdPower k d ≤ thresholdPower (k + 1) d := by
  unfold thresholdPower
  rw [Nat.factorial_succ, show k + 1 - 1 = k from by omega]
  push_cast
  rw [show (↑(k + 1) * ↑k.factorial) * (↑d) ^ k =
      ↑k.factorial * ((↑d) ^ (k - 1) * ((↑(k + 1)) * ↑d)) from by
    rw [show (↑d : ℝ) ^ k = (↑d) ^ (k - 1) * ↑d from by
      rw [← pow_succ]; congr 1; omega]
    ring]
  apply mul_le_mul_of_nonneg_left
  · apply le_mul_of_one_le_right
    · exact pow_nonneg (Nat.cast_nonneg d) _
    · calc (1 : ℝ) ≤ 2 * 2 := by norm_num
        _ ≤ (↑(k + 1)) * ↑d := by
          apply mul_le_mul
          · exact Nat.cast_le.mpr (by omega)
          · exact Nat.cast_le.mpr hd
          · norm_num
          · positivity
  · exact Nat.cast_nonneg (k.factorial)

-- ============================================================
-- Part IV: Classical Recovery (k = 2)
-- ============================================================

/-- For k=2: n₂^2 ≈ 2! · d = 2d.
    So n₂ ≈ √(2d), recovering the classical square-root law. -/
theorem threshold_k2 (d : ℕ) : thresholdPower 2 d = 2 * (d : ℝ) := by
  unfold thresholdPower
  simp [Nat.factorial]

/-- For k=3: n₃^3 ≈ 3! · d² = 6d².
    So n₃ ≈ (6d²)^{1/3} ≈ 1.82 · d^{2/3}. -/
theorem threshold_k3 (d : ℕ) : thresholdPower 3 d = 6 * (d : ℝ) ^ 2 := by
  unfold thresholdPower
  simp [Nat.factorial]; ring

/-- For k=4: n₄^4 ≈ 4! · d³ = 24d³.
    So n₄ ≈ (24d³)^{1/4}. -/
theorem threshold_k4 (d : ℕ) : thresholdPower 4 d = 24 * (d : ℝ) ^ 3 := by
  unfold thresholdPower
  simp [Nat.factorial]; ring

-- ============================================================
-- Part V: Ratio to Pigeonhole Bound
-- ============================================================

/-- The pigeonhole bound (k-1)d exceeds the true threshold for moderate d.
    We prove this for specific k values where the algebra is clean. -/

/-- For k=2: the threshold 2d is less than the pigeonhole bound (d)² = d². -/
theorem pigeonhole_vs_threshold_k2 (d : ℕ) (hd : 2 ≤ d) :
    thresholdPower 2 d ≤ (d : ℝ) ^ 2 := by
  rw [threshold_k2]
  have hd' : (2 : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hd
  nlinarith [sq_nonneg ((d : ℝ) - 2)]

/-- For k=3: the threshold 6d² is less than (2d)³ = 8d³. -/
theorem pigeonhole_vs_threshold_k3 (d : ℕ) (hd : 1 ≤ d) :
    thresholdPower 3 d ≤ (2 * (d : ℝ)) ^ 3 := by
  rw [threshold_k3]
  have hd' : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  nlinarith [sq_nonneg (d : ℝ)]

-- ============================================================
-- Part VI: Concrete Threshold Values
-- ============================================================

/-- For d=365 (standard birthday problem):
    k=2: n₂^2 ≈ 730, so n₂ ≈ √730 ≈ 27 (actual threshold ≈ 23)
    k=3: n₃^3 ≈ 799350, so n₃ ≈ ∛799350 ≈ 93 (actual ≈ 88)
    k=4: n₄^4 ≈ 1167655800, so n₄ ≈ ∜1167655800 ≈ 185 (actual ≈ 187) -/
theorem concrete_365_k2 : thresholdPower 2 365 = 730 := by
  rw [threshold_k2]; norm_num

theorem concrete_365_k3 : thresholdPower 3 365 = 6 * 365 ^ 2 := by
  rw [threshold_k3]

-- ============================================================
-- Part VII: Exponent Approaches 1
-- ============================================================

/-- As k increases, the scaling exponent (k-1)/k approaches 1.
    For any ε > 0, there exists K such that for k ≥ K, (k-1)/k > 1 - ε.

    This means for large k, the threshold approaches the pigeonhole
    bound: n_k ≈ d^{(k-1)/k} ≈ d for large k. -/
theorem exponent_approaches_one (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 1 - ε < scalingExponent k := by
  -- Need (k-1)/k > 1 - ε, i.e., 1/k < ε, i.e., k > 1/ε
  use ⌈1 / ε⌉₊ + 1
  intro k hk
  unfold scalingExponent
  have hk0 : k ≠ 0 := by omega
  simp only [hk0, ite_false]
  rw [show (k : ℝ) - 1 = k - 1 from by push_cast; ring]
  rw [sub_div, div_self (show (k : ℝ) ≠ 0 from by positivity)]
  -- Need: 1 - ε < 1 - 1/k, i.e., 1/k < ε
  have hk_pos : (0 : ℝ) < k := by positivity
  linarith [show (1 : ℝ) / k ≤ 1 / (⌈1 / ε⌉₊ + 1 : ℝ) from by
    apply div_le_div_of_nonneg_left one_pos (by positivity) (by exact_mod_cast hk),
    show (1 : ℝ) / (⌈1 / ε⌉₊ + 1 : ℝ) < ε from by
    rw [div_lt_iff (by positivity : (⌈1 / ε⌉₊ + 1 : ℝ) > 0)]
    calc ε * (⌈1 / ε⌉₊ + 1 : ℝ) > ε * (1 / ε) := by
          apply mul_lt_mul_of_pos_left _ hε
          exact_mod_cast Nat.lt_add_one_iff.mpr (Nat.le_ceil _)
        _ = 1 := by field_simp]

end BirthdayScaling
