/-
  Aristotle targets for Erdős Problem #608
  Routine supporting lemmas for automated proof search.
  See Erdos608Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main extremal results (Füredi-Maleki, Grzesik-Hu-Volec)
  - Known numerical facts provable from definitions and Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos608Aristotle

open Real

/-- The correct constant c = (2 + √2) / 16. -/
noncomputable def c : ℝ := (2 + Real.sqrt 2) / 16

/-- The Turán threshold for triangles. -/
noncomputable def turanEdges (n : ℕ) : ℕ := (n / 2) * ((n + 1) / 2)

-- Routine: √2 > 1
theorem sqrt_two_gt_one : Real.sqrt 2 > 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

-- Routine: √2 < 1.5
theorem sqrt_two_lt : Real.sqrt 2 < 1.5 := by
  rw [show (1.5 : ℝ) = Real.sqrt (1.5 ^ 2) from (Real.sqrt_sq (by norm_num : (1.5:ℝ) ≥ 0)).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

-- Routine: √2 * √2 = 2
theorem sqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)

-- Routine: c > 0
theorem c_pos : c > 0 := by
  unfold c; linarith [sqrt_two_gt_one]

-- Routine: c > 0.213
-- (2 + √2)/16 > 0.213 ⟺ 2 + √2 > 3.408 ⟺ √2 > 1.408 ⟺ 2 > 1.982464
theorem c_gt : c > 0.213 := by
  unfold c
  have h : (1.408 : ℝ) < Real.sqrt 2 := by
    rw [show (1.408 : ℝ) = Real.sqrt (1.408^2) from (Real.sqrt_sq (by norm_num : (1.408:ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

-- Routine: c < 0.214
-- (2 + √2)/16 < 0.214 ⟺ 2 + √2 < 3.424 ⟺ √2 < 1.424 ⟺ 2 < 2.027776
theorem c_lt : c < 0.214 := by
  unfold c
  have h : Real.sqrt 2 < 1.424 := by
    rw [show (1.424 : ℝ) = Real.sqrt (1.424^2) from (Real.sqrt_sq (by norm_num : (1.424:ℝ) ≥ 0)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

-- Routine: c < 2/9 (this is why the original conjecture fails)
-- (2+√2)/16 < 2/9 ⟺ 9(2+√2) < 32 ⟺ 18+9√2 < 32 ⟺ √2 < 14/9 ≈ 1.556
theorem c_lt_two_ninths : c < 2 / 9 := by
  unfold c; linarith [sqrt_two_lt]

-- Routine: 2/9 > 0.222
theorem two_ninths_gt : (2 : ℝ) / 9 > 0.222 := by norm_num

-- Routine: The gap between 2/9 and c is positive
theorem gap_positive : (2 : ℝ) / 9 - c > 0 := by
  linarith [c_lt_two_ninths]

-- Routine: Turán edges for n=4 is 4
theorem turan_four : turanEdges 4 = 4 := by unfold turanEdges; norm_num

-- Routine: Turán edges for n=5 is 6
theorem turan_five : turanEdges 5 = 6 := by unfold turanEdges; norm_num

-- Routine: Turán edges for n=6 is 9
theorem turan_six : turanEdges 6 = 9 := by unfold turanEdges; norm_num

end Erdos608Aristotle
