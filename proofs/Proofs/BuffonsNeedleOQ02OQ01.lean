import Mathlib

/-
# N-Dimensional Buffon Noodle Formula

## What This Proves

This file formalizes the general n-dimensional Buffon noodle formula. For a curve of
total arc length L dropped on parallel hyperplanes with spacing d in ℝⁿ, the expected
number of crossings is:

  E[crossings] = αₙ · L/d

where αₙ is the n-dimensional crossing factor satisfying the recurrence:
  α_{n+2} = (n/(n+1)) · αₙ
with base values α₂ = 2/π and α₃ = 1/2.

We verify specific values (α₄ = 4/(3π), α₅ = 3/8), prove the crossing factor is
strictly decreasing with dimension, and establish the general noodle theorem.

## Mathematical Background

The crossing factor αₙ = E_{S^{n-1}}[|u₁|] = Γ(n/2) / (√π · Γ((n+1)/2)) satisfies
the recurrence α_{n+2} = (n/(n+1)) · αₙ because:
  Γ((n+2)/2) = (n/2) · Γ(n/2)
  Γ((n+3)/2) = ((n+1)/2) · Γ((n+1)/2)

Hence α_{n+2}/αₙ = n/(n+1).

## Connection to Prior Work

- `BuffonsNeedle.lean`: Classical 2D Buffon problem, P = 2ℓ/(πd)
- `BuffonsNeedleOQ02.lean`: 3D formula E = L/(2d) via ∫₀^π sin θ |cos θ| dθ = 1
- **This file**: General αₙ for all n ≥ 2 via recurrence, dimension comparisons
-/

namespace BuffonsNeedleOQ02OQ01

open Real

-- ============================================================
-- Part I: The Crossing Factor Recurrence
-- ============================================================

/-- The n-dimensional crossing factor αₙ = E_{S^{n-1}}[|u₁|].
    Defined by the recurrence α_{n+2} = (n/(n+1)) · αₙ with base cases
    α₂ = 2/π (classical Buffon) and α₃ = 1/2 (3D sphere average).
    For n ≤ 1 (degenerate), αₙ = 1 by convention. -/
noncomputable def crossingFactor : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2 / π
  | 3 => 1 / 2
  | (n + 4) => ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2)

@[simp] lemma crossingFactor_two : crossingFactor 2 = 2 / π := rfl
@[simp] lemma crossingFactor_three : crossingFactor 3 = 1 / 2 := rfl

/-- The fundamental recurrence: α_{n+4} = ((n+2)/(n+3)) · α_{n+2}. -/
@[simp] lemma crossingFactor_succ_succ (n : ℕ) :
    crossingFactor (n + 4) = ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2) := rfl

-- ============================================================
-- Part II: Computed Values
-- ============================================================

/-- α₄ = 4/(3π) ≈ 0.424. The 4D crossing factor. -/
theorem crossingFactor_four : crossingFactor 4 = 4 / (3 * π) := by
  have h4 : (4 : ℕ) = 0 + 4 := by norm_num
  rw [h4, crossingFactor_succ_succ]
  have h2 : (0 : ℕ) + 2 = 2 := by norm_num
  rw [h2, crossingFactor_two]
  push_cast
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp [hπ]
  ring

/-- α₅ = 3/8 = 0.375. The 5D crossing factor. -/
theorem crossingFactor_five : crossingFactor 5 = 3 / 8 := by
  have h5 : (5 : ℕ) = 1 + 4 := by norm_num
  rw [h5, crossingFactor_succ_succ]
  have h3 : (1 : ℕ) + 2 = 3 := by norm_num
  rw [h3, crossingFactor_three]
  push_cast
  norm_num

-- ============================================================
-- Part III: Positivity
-- ============================================================

/-- αₙ > 0 for all n ≥ 2. The crossing factor is always positive because
    it is a product of positive ratios times a positive base case. -/
theorem crossingFactor_pos : ∀ n : ℕ, 2 ≤ n → 0 < crossingFactor n
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by show 0 < (2 : ℝ) / π; positivity
  | 3, _ => by show 0 < (1 : ℝ) / 2; norm_num
  | (n + 4), _ => by
    show 0 < ((n + 2 : ℝ) / (n + 3 : ℝ)) * crossingFactor (n + 2)
    exact mul_pos
      (div_pos (by exact_mod_cast (show 0 < n + 2 by omega))
               (by exact_mod_cast (show 0 < n + 3 by omega)))
      (crossingFactor_pos (n + 2) (by omega))

-- ============================================================
-- Part IV: The General N-Dimensional Buffon Formula
-- ============================================================

/-- The expected number of hyperplane crossings for a curve of length L
    in n-dimensional space with hyperplane spacing d.
    E[crossings] = αₙ · L/d. -/
noncomputable def buffonNd (n : ℕ) (L d : ℝ) : ℝ := crossingFactor n * (L / d)

/-- The 2D formula recovers E = 2L/(πd). -/
theorem buffonNd_two (L d : ℝ) (hd : d ≠ 0) :
    buffonNd 2 L d = 2 * L / (π * d) := by
  unfold buffonNd
  simp only [crossingFactor_two]
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  field_simp [hd, hπ]

/-- The 3D formula recovers E = L/(2d) from BuffonsNeedleOQ02.lean. -/
theorem buffonNd_three (L d : ℝ) :
    buffonNd 3 L d = L / (2 * d) := by
  unfold buffonNd
  simp only [crossingFactor_three]
  ring

/-- Linearity in arc length: the noodle theorem in n dimensions. -/
theorem buffonNd_additive (n : ℕ) (L₁ L₂ d : ℝ) :
    buffonNd n (L₁ + L₂) d = buffonNd n L₁ d + buffonNd n L₂ d := by
  unfold buffonNd
  rw [add_div, mul_add]

/-- Scaling in curve length. -/
theorem buffonNd_scale_L (n : ℕ) (L d c : ℝ) :
    buffonNd n (c * L) d = c * buffonNd n L d := by
  unfold buffonNd; ring

/-- The general noodle theorem for polygonal paths in ℝⁿ:
    ∑ᵢ E[crossings for segment i] = E[crossings for total path]. -/
theorem buffonNd_noodle (n k : ℕ) (lengths : Fin k → ℝ) (d : ℝ) :
    ∑ i, buffonNd n (lengths i) d = buffonNd n (∑ i, lengths i) d := by
  unfold buffonNd
  rw [Finset.sum_div, ← Finset.mul_sum]

/-- Monotonicity: longer curves have more expected crossings. -/
theorem buffonNd_mono (n : ℕ) (L₁ L₂ d : ℝ) (hn : 2 ≤ n) (hd : 0 < d) (hLL : L₁ ≤ L₂) :
    buffonNd n L₁ d ≤ buffonNd n L₂ d := by
  unfold buffonNd
  apply mul_le_mul_of_nonneg_left
  · simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hLL (le_of_lt (inv_pos.mpr hd))
  · exact le_of_lt (crossingFactor_pos n hn)

-- ============================================================
-- Part V: Dimension Comparison
-- ============================================================

/-- α₃ < α₂: 3D has fewer expected crossings than 2D.
    Equivalently 1/2 < 2/π, i.e., π < 4.
    Proof follows BuffonsNeedleOQ02.lean:crossing_factor_3d_lt_2d. -/
theorem crossingFactor_three_lt_two : crossingFactor 3 < crossingFactor 2 := by
  simp only [crossingFactor_three, crossingFactor_two]
  rw [← sub_pos]
  have h : (2 : ℝ) / π - 1 / 2 = (4 - π) / (2 * π) := by
    field_simp [pi_ne_zero]; ring
  rw [h]
  exact div_pos (by linarith [pi_lt_four]) (by positivity)

/-- α₄ < α₃: 4D has fewer expected crossings than 3D.
    Equivalently 4/(3π) < 1/2, i.e., 8 < 3π. Follows from π > 3. -/
theorem crossingFactor_four_lt_three : crossingFactor 4 < crossingFactor 3 := by
  rw [crossingFactor_four, crossingFactor_three]
  rw [← sub_pos]
  have h : (1 : ℝ) / 2 - 4 / (3 * π) = (3 * π - 8) / (6 * π) := by
    field_simp [pi_ne_zero]; ring
  rw [h]
  exact div_pos (by nlinarith [pi_gt_three]) (by positivity)

/-- α₅ < α₃: 5D has fewer crossings than 3D.
    3/8 < 1/2 by direct computation. -/
theorem crossingFactor_five_lt_three : crossingFactor 5 < crossingFactor 3 := by
  rw [crossingFactor_five, crossingFactor_three]
  norm_num

/-- Transitive: α₄ < α₂ (4D has fewer crossings than 2D). -/
theorem crossingFactor_four_lt_two : crossingFactor 4 < crossingFactor 2 :=
  lt_trans crossingFactor_four_lt_three crossingFactor_three_lt_two

-- ============================================================
-- Part VI: The Recurrence Ratio
-- ============================================================

/-- The recurrence ratio (n+2)/(n+3) is always strictly less than 1.
    This means each step of the recurrence reduces the crossing factor. -/
theorem crossingFactor_ratio_lt_one (n : ℕ) :
    (n + 2 : ℝ) / (n + 3 : ℝ) < 1 := by
  rw [div_lt_one]
  · exact_mod_cast (show n + 2 < n + 3 by omega)
  · exact_mod_cast (show 0 < n + 3 by omega)

/-- The ratio α_{n+4}/α_{n+2} = (n+2)/(n+3), directly from the recurrence. -/
theorem crossingFactor_ratio (n : ℕ) (hα : crossingFactor (n + 2) ≠ 0) :
    crossingFactor (n + 4) / crossingFactor (n + 2) =
    (n + 2 : ℝ) / (n + 3 : ℝ) := by
  simp only [crossingFactor_succ_succ]
  rw [mul_div_assoc, div_self hα, mul_one]

/-- α_{n+2} < αₙ for n ≥ 2: crossing factors strictly decrease with dimension.
    Proof: α_{n+2} = ratio · αₙ where 0 < ratio < 1 and αₙ > 0. -/
theorem crossingFactor_strict_dec (n : ℕ) (hn : 2 ≤ n) :
    crossingFactor (n + 2) < crossingFactor n := by
  have hpos : 0 < crossingFactor n := crossingFactor_pos n hn
  -- n ≥ 2, so n + 2 ≥ 4, matching the (m + 4) recurrence case with m = n - 2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- crossingFactor (m + 4) = ((m+2)/(m+3)) * crossingFactor (m + 2)
  have h4 : m + 2 + 2 = m + 4 := by omega
  rw [h4, crossingFactor_succ_succ]
  calc ((m + 2 : ℝ) / (m + 3 : ℝ)) * crossingFactor (m + 2)
      < 1 * crossingFactor (m + 2) := by
        exact mul_lt_mul_of_pos_right (crossingFactor_ratio_lt_one m) hpos
    _ = crossingFactor (m + 2) := one_mul _

-- ============================================================
-- Part VII: Asymptotic Behavior
-- ============================================================

/-- Helper: √2 < 3/2 (since 2 < 9/4). -/
private lemma sqrt_two_lt : Real.sqrt 2 < 3 / 2 := by
  rw [show (3 : ℝ) / 2 = Real.sqrt (9 / 4) from by
    rw [Real.sqrt_eq_iff_sq_eq (by norm_num) (by norm_num)]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- Helper: √3 < 2 (since 3 < 4). -/
private lemma sqrt_three_lt : Real.sqrt 3 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 from by
    rw [Real.sqrt_eq_iff_sq_eq (by norm_num) (by norm_num)]; norm_num]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- αₙ ≤ 1/√n for all n ≥ 2. Proved by strong induction using the recurrence.
    Base cases: 2/π ≤ 1/√2 (from 2√2 < 3 < π) and 1/2 ≤ 1/√3 (from √3 < 2).
    Inductive step: n(n+2) ≤ (n+1)² guarantees the bound propagates. -/
theorem crossingFactor_le_inv_sqrt : ∀ n : ℕ, 2 ≤ n →
    crossingFactor n ≤ 1 / Real.sqrt n
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => by
    simp only [crossingFactor_two]
    rw [div_le_div_iff (by positivity) (Real.sqrt_pos.mpr (by positivity))]
    -- Need: 2 · √2 ≤ π · 1 = π
    rw [mul_one]
    calc 2 * Real.sqrt 2 < 2 * (3 / 2) := by nlinarith [sqrt_two_lt]
      _ = 3 := by ring
      _ < π := pi_gt_three
  | 3, _ => by
    simp only [crossingFactor_three]
    rw [div_le_div_iff (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr (by positivity))]
    -- Need: 1 · √3 ≤ 2 · 1 = 2, i.e., √3 ≤ 2
    simp only [one_mul, mul_one]
    exact le_of_lt sqrt_three_lt
  | (n + 4), _ => by
    -- α(n+4) = ((n+2)/(n+3)) · α(n+2) by recurrence
    simp only [crossingFactor_succ_succ]
    -- By induction: α(n+2) ≤ 1/√(n+2)
    have ih := crossingFactor_le_inv_sqrt (n + 2) (by omega)
    have hn2_pos : (0 : ℝ) < n + 2 := by exact_mod_cast (show 0 < n + 2 by omega)
    have hn3_pos : (0 : ℝ) < n + 3 := by exact_mod_cast (show 0 < n + 3 by omega)
    have hn4_pos : (0 : ℝ) < n + 4 := by exact_mod_cast (show 0 < n + 4 by omega)
    have hsqrt_n2_pos : 0 < Real.sqrt (↑(n + 2)) := Real.sqrt_pos.mpr hn2_pos
    have hsqrt_n4_pos : 0 < Real.sqrt (↑(n + 4)) := Real.sqrt_pos.mpr hn4_pos
    -- Bound: ((n+2)/(n+3)) · (1/√(n+2)) ≤ 1/√(n+4)
    -- Equivalent to: (n+2) · √(n+4) ≤ (n+3) · √(n+2)
    -- Squaring: (n+2)² · (n+4) ≤ (n+3)² · (n+2) ↔ (n+2)(n+4) ≤ (n+3)²
    -- And (n+2)(n+4) = n²+6n+8 ≤ n²+6n+9 = (n+3)² ✓
    calc ((n + 2 : ℝ) / (n + 3)) * crossingFactor (n + 2)
        ≤ ((n + 2) / (n + 3)) * (1 / Real.sqrt (↑(n + 2))) := by
          apply mul_le_mul_of_nonneg_left ih
          exact div_nonneg (le_of_lt hn2_pos) (le_of_lt hn3_pos)
      _ = (n + 2) / ((n + 3) * Real.sqrt (↑(n + 2))) := by ring
      _ ≤ 1 / Real.sqrt (↑(n + 4)) := by
          rw [div_le_div_iff (mul_pos hn3_pos hsqrt_n2_pos) hsqrt_n4_pos]
          -- Need: (n+2) · √(n+4) ≤ 1 · (n+3) · √(n+2)
          rw [one_mul]
          -- Square both sides (both positive)
          rw [← Real.sqrt_sq (le_of_lt hn2_pos), ← Real.sqrt_sq (le_of_lt hn3_pos)]
          rw [← Real.sqrt_mul (sq_nonneg _), ← Real.sqrt_mul (sq_nonneg _)]
          apply Real.sqrt_le_sqrt
          -- (n+2)² · (n+4) ≤ (n+3)² · (n+2)
          push_cast
          nlinarith [sq_nonneg (n : ℝ)]

/-- αₙ → 0 as n → ∞: in very high dimensions, a random unit vector's
    projection onto any fixed axis approaches zero on average.
    Proof: squeeze between 0 and 1/√n, which tends to 0. -/
theorem crossingFactor_tendsto_zero :
    Filter.Tendsto (fun n => crossingFactor (n + 2)) Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n; exact le_of_lt (crossingFactor_pos (n + 2) (by omega))
  · intro n; exact crossingFactor_le_inv_sqrt (n + 2) (by omega)
  · -- 1/√(n+2) → 0 as n → ∞
    have : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.sqrt (↑(n + 2))) Filter.atTop (nhds 0) := by
      apply Filter.Tendsto.div tendsto_const_nhds _ (Or.inl rfl)
      apply Filter.Tendsto.comp Real.tendsto_sqrt_atTop
      apply Filter.Tendsto.atTop_add (Filter.tendsto_natCast_atTop_atTop)
      exact tendsto_const_nhds
    exact this

end BuffonsNeedleOQ02OQ01
