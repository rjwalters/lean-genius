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
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnn := Real.sqrt_nonneg (2 : ℝ)
  constructor
  · -- 0.213 < (2 + √2)/16 ↔ 3.408 < 2 + √2 ↔ 1.408 < √2
    -- From √2² = 2 and 1.408² = 1.982464 < 2
    rw [gt_iff_lt, lt_div_iff (by norm_num : (0 : ℝ) < 16)]
    nlinarith [show (1.408 : ℝ) ^ 2 = 1.982464 from by ring]
  · -- (2 + √2)/16 < 0.214 ↔ 2 + √2 < 3.424 ↔ √2 < 1.424
    -- From √2² = 2 and 1.424² = 2.027776 > 2
    rw [div_lt_iff (by norm_num : (0 : ℝ) < 16)]
    nlinarith [show (1.424 : ℝ) ^ 2 = 2.027776 from by ring]

/-- c < 2/9, proving Erdős's original conjecture is false. -/
lemma c_lt_two_ninths : c < 2/9 := by
  unfold c
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hnn := Real.sqrt_nonneg (2 : ℝ)
  -- (2 + √2)/16 < 2/9 ↔ 9(2 + √2) < 32 ↔ 9√2 < 14 ↔ √2 < 14/9
  -- From √2² = 2 and (14/9)² = 196/81 > 2
  rw [div_lt_div_iff (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 9)]
  nlinarith [show ((14 : ℝ) / 9) ^ 2 = 196 / 81 from by ring]

/-- c > 0. -/
lemma c_pos : c > 0 := by
  unfold c; positivity

end Erdos608
