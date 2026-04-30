/-
  Aristotle targets for Erdős Problem #608: Edges in 5-Cycles

  Routine numerical lemmas for automated proof search.
  See Erdos608Problem.lean for the main formalization.

  Candidates:
  - c_approx: c = (2 + √2)/16 satisfies 0.213 < c < 0.214
  - c_lt_two_ninths: c < 2/9
-/
import Mathlib

namespace Erdos608

open Real

/-- The correct constant c = (2 + √2) / 16 ≈ 0.2134. -/
noncomputable def c : ℝ := (2 + Real.sqrt 2) / 16

/-- c ≈ 0.2134, so 0.213 < c < 0.214. -/
lemma c_approx : c > 0.213 ∧ c < 0.214 := by
  unfold c
  -- √2 > 1.408 since 1.408² = 1.982464 < 2
  have h_lo : (1.408 : ℝ) < Real.sqrt 2 := by
    rw [show (1.408 : ℝ) = Real.sqrt (1.408 ^ 2 : ℝ) from
      (Real.sqrt_sq (by norm_num : (1.408 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  -- √2 < 1.424 since 1.424² = 2.027776 > 2
  have h_hi : Real.sqrt 2 < 1.424 := by
    rw [show (1.424 : ℝ) = Real.sqrt (1.424 ^ 2 : ℝ) from
      (Real.sqrt_sq (by norm_num : (1.424 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · rw [gt_iff_lt, lt_div_iff (by norm_num : (16 : ℝ) > 0)]; linarith
  · rw [div_lt_iff (by norm_num : (16 : ℝ) > 0)]; linarith

/-- c < 2/9, proving Erdős's original conjecture is false. -/
lemma c_lt_two_ninths : c < 2/9 := by
  unfold c
  -- √2 < 14/9 since (14/9)² = 196/81 > 2
  have h : Real.sqrt 2 < 14 / 9 := by
    rw [show (14 / 9 : ℝ) = Real.sqrt ((14 / 9 : ℝ) ^ 2) from
      (Real.sqrt_sq (by norm_num : (14 / 9 : ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [div_lt_div_iff (by norm_num : (16 : ℝ) > 0) (by norm_num : (9 : ℝ) > 0)]
  linarith

/-- c > 0. -/
lemma c_pos : c > 0 := by
  unfold c; positivity

end Erdos608
