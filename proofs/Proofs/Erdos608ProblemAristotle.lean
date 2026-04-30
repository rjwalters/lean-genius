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
  constructor
  · rw [gt_iff_lt, lt_div_iff (by norm_num : (16 : ℝ) > 0)]
    have h : (1.408 : ℝ) < Real.sqrt 2 := by
      calc (1.408 : ℝ) = Real.sqrt ((1.408 : ℝ) ^ 2) :=
            (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.408)).symm
        _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  · rw [div_lt_iff (by norm_num : (16 : ℝ) > 0)]
    have h : Real.sqrt 2 < (1.424 : ℝ) := by
      calc Real.sqrt 2 < Real.sqrt ((1.424 : ℝ) ^ 2) :=
            Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (2 : ℝ) < (1.424 : ℝ) ^ 2)
        _ = 1.424 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.424)
    linarith

/-- c < 2/9, proving Erdős's original conjecture is false. -/
lemma c_lt_two_ninths : c < 2/9 := by
  unfold c
  rw [div_lt_div_iff (by norm_num : (16 : ℝ) > 0) (by norm_num : (9 : ℝ) > 0)]
  have h : Real.sqrt 2 < 14 / 9 := by
    calc Real.sqrt 2 < Real.sqrt ((14 / 9 : ℝ) ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (2 : ℝ) < (14 / 9) ^ 2)
      _ = 14 / 9 := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 14 / 9)
  linarith

/-- c > 0. -/
lemma c_pos : c > 0 := by
  unfold c
  apply div_pos
  · linarith [Real.sqrt_nonneg 2]
  · norm_num

end Erdos608
