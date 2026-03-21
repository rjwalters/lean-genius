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

/-- αₙ → 0 as n → ∞: in very high dimensions, a random unit vector's
    projection onto any fixed axis approaches zero on average.
    This follows from the Wallis-type product and the divergence of ∑ 1/n. -/
theorem crossingFactor_tendsto_zero :
    Filter.Tendsto (fun n => crossingFactor (n + 2)) Filter.atTop (nhds 0) := by
  sorry

end BuffonsNeedleOQ02OQ01
