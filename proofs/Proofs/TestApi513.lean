import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.LiminfLimsup

-- Test: division lemmas for ratio proofs
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b) : a / b ≤ 1 := by
  rw [div_le_one hb]
  exact hab

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
  div_nonneg ha (le_of_lt hb)

-- Test: 1/2 < 2/π
example : (1 : ℝ) / 2 < 2 / Real.pi := by
  have hpi : Real.pi > 3 := Real.pi_gt_three
  have hpi_pos : (0 : ℝ) < Real.pi := by linarith
  rw [div_lt_div_iff (by norm_num : (0:ℝ) < 2) hpi_pos]
  -- Need: 1 * π < 2 * 2 = 4, i.e., π < 4
  have : Real.pi < 4 := by linarith [Real.pi_lt_3141593]
  linarith

-- Test: if_neg simplification
example (h : ¬ (3 : ℝ) = 0) : (if (3 : ℝ) = 0 then 0 else 5 / 3) = 5 / 3 := by
  simp [h]
