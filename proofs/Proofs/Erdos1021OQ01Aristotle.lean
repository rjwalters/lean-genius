/-
  Aristotle targets for Erdős Problem #1021 OQ-01
  Supporting analysis lemmas for automated proof search.
  See Erdos1021OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep extremal results
  - Routine analysis / arithmetic facts about the exponent 3/2 - 1/(k-1)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1021OQ01Aristotle

open Filter Real Topology

/-- For k ≥ 2, (k : ℝ) - 1 > 0. -/
theorem real_cast_sub_one_pos (k : ℕ) (hk : k ≥ 2) : (k : ℝ) - 1 > 0 := by
  sorry

/-- (k : ℝ) - 1 → +∞ as k → ∞ (as a nat). -/
theorem nat_cast_sub_one_atTop :
    Tendsto (fun k : ℕ => (k : ℝ) - 1) atTop atTop := by
  sorry

/-- 1 / ((k : ℝ) - 1) → 0 as k → +∞. -/
theorem inv_nat_cast_sub_one_tendsto_zero :
    Tendsto (fun k : ℕ => 1 / ((k : ℝ) - 1)) atTop (nhds 0) := by
  sorry

/-- 3/2 - 1/((k : ℝ) - 1) → 3/2 as k → +∞. -/
theorem lower_bound_exponent_tendsto :
    Tendsto (fun k : ℕ => (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1)) atTop (nhds (3 / 2)) := by
  sorry

/-- For k ≥ 4, the lower bound exponent 3/2 - 1/(k-1) > 1. -/
theorem exponent_gt_one (k : ℕ) (hk : k ≥ 4) :
    (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1) > 1 := by
  sorry

/-- For k ≥ 3, the lower bound exponent 3/2 - 1/(k-1) ≥ 1. -/
theorem exponent_ge_one (k : ℕ) (hk : k ≥ 3) :
    (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1) ≥ 1 := by
  sorry

/-- For k ≥ 2, the lower bound exponent 3/2 - 1/(k-1) > 0. -/
theorem exponent_pos (k : ℕ) (hk : k ≥ 2) :
    (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1) > 0 := by
  sorry

/-- For k ≥ 2, the lower bound exponent 3/2 - 1/(k-1) < 3/2. -/
theorem exponent_lt_three_halves (k : ℕ) (hk : k ≥ 2) :
    (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1) < 3 / 2 := by
  sorry

/-- The exponent 3/2 - 1/(k-1) is strictly increasing in k for k ≥ 2. -/
theorem exponent_strictMono :
    StrictMonoOn (fun k : ℕ => (3 : ℝ) / 2 - 1 / ((k : ℝ) - 1)) {k | k ≥ 2} := by
  sorry

/-- For k₁ ≤ k₂ (with k₁ ≥ 2), exponent at k₁ ≤ exponent at k₂. -/
theorem exponent_mono (k₁ k₂ : ℕ) (hk₁ : k₁ ≥ 2) (hk₂ : k₂ ≥ 2) (h : k₁ ≤ k₂) :
    (3 : ℝ) / 2 - 1 / ((k₁ : ℝ) - 1) ≤ (3 : ℝ) / 2 - 1 / ((k₂ : ℝ) - 1) := by
  sorry

/-- For k = 3, the exponent 3/2 - 1/2 = 1. -/
theorem exponent_at_three : (3 : ℝ) / 2 - 1 / ((3 : ℝ) - 1) = 1 := by
  sorry

/-- For k = 4, the exponent 3/2 - 1/3 = 7/6. -/
theorem exponent_at_four : (3 : ℝ) / 2 - 1 / ((4 : ℝ) - 1) = 7 / 6 := by
  sorry

/-- For k = 5, the exponent 3/2 - 1/4 = 5/4. -/
theorem exponent_at_five : (3 : ℝ) / 2 - 1 / ((5 : ℝ) - 1) = 5 / 4 := by
  sorry

end Erdos1021OQ01Aristotle
