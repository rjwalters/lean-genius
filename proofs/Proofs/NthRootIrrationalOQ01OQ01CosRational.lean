/-
  Nth Root Irrationality OQ-01-OQ-01 (Niven, rational cases):
  the *rational* half of Niven's cosine classification.

  The sibling file `NthRootIrrationalOQ01OQ01Cos.lean` proves the irrational
  direction with the sharp bound:

      `φ(n) ≥ 3  ⟹  Irrational (cos(2π/n))`,   sharp at `φ(n) ≤ 2 ⇔ n ∈ {1,2,3,4,6}`.

  This file supplies the complementary direction — that for each of those five
  exceptional `n`, `cos(2π/n)` really *is* rational — so that together the two
  files give the full classification (Niven's theorem):

      `cos(2π/n)` is rational  ⟺  `n ∈ {1, 2, 3, 4, 6}`,

  with the explicit values

      n: 1     2     3      4    6
      cos: 1   −1   −1/2    0   1/2.

  Each case is an elementary special-angle evaluation:
  * `cos(2π/1) = cos(2π) = 1`                          (`Real.cos_two_pi`)
  * `cos(2π/2) = cos π   = −1`                         (`Real.cos_pi`)
  * `cos(2π/3) = cos(π − π/3) = −cos(π/3) = −1/2`      (`Real.cos_pi_sub`, `Real.cos_pi_div_three`)
  * `cos(2π/4) = cos(π/2) = 0`                         (`Real.cos_pi_div_two`)
  * `cos(2π/6) = cos(π/3) = 1/2`                       (`Real.cos_pi_div_three`)

  Results (0 axioms, 0 sorries; Docker-verified green 2026-06-15):
  - `cos_two_pi_div_{one,two,three,four,six}_rational` — the five exceptional cases.
  - `cos_two_pi_div_rational_of_mem` — the bundled statement over `n ∈ {1,2,3,4,6}`.

  ## References
  - Niven, I. (1956). "Irrational Numbers." Carus Math. Monographs, Thm 3.9.
-/

import Mathlib

set_option linter.unusedVariables false

namespace NthRootIrrationalOQ01OQ01CosRational

open Real

/-- A real number equal to the cast of a rational is not irrational. -/
private lemma not_irrational_of_eq_rat {x : ℝ} (q : ℚ) (h : x = (q : ℝ)) :
    ¬ Irrational x := by
  rw [h]; exact q.not_irrational

/-- `cos(2π/1) = 1`, rational. -/
theorem cos_two_pi_div_one_rational :
    ¬ Irrational (Real.cos (2 * Real.pi / (1 : ℕ))) := by
  refine not_irrational_of_eq_rat 1 ?_
  rw [Nat.cast_one, div_one, Real.cos_two_pi]
  norm_num

/-- `cos(2π/2) = cos π = −1`, rational. -/
theorem cos_two_pi_div_two_rational :
    ¬ Irrational (Real.cos (2 * Real.pi / (2 : ℕ))) := by
  refine not_irrational_of_eq_rat (-1) ?_
  have ha : (2 * Real.pi / ((2 : ℕ) : ℝ)) = Real.pi := by push_cast; ring
  rw [ha, Real.cos_pi]
  norm_num

/-- `cos(2π/3) = cos(π − π/3) = −cos(π/3) = −1/2`, rational. -/
theorem cos_two_pi_div_three_rational :
    ¬ Irrational (Real.cos (2 * Real.pi / (3 : ℕ))) := by
  refine not_irrational_of_eq_rat (-1/2) ?_
  have ha : (2 * Real.pi / ((3 : ℕ) : ℝ)) = Real.pi - Real.pi / 3 := by push_cast; ring
  rw [ha, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- `cos(2π/4) = cos(π/2) = 0`, rational. -/
theorem cos_two_pi_div_four_rational :
    ¬ Irrational (Real.cos (2 * Real.pi / (4 : ℕ))) := by
  refine not_irrational_of_eq_rat 0 ?_
  have ha : (2 * Real.pi / ((4 : ℕ) : ℝ)) = Real.pi / 2 := by push_cast; ring
  rw [ha, Real.cos_pi_div_two]
  norm_num

/-- `cos(2π/6) = cos(π/3) = 1/2`, rational. -/
theorem cos_two_pi_div_six_rational :
    ¬ Irrational (Real.cos (2 * Real.pi / (6 : ℕ))) := by
  refine not_irrational_of_eq_rat (1/2) ?_
  have ha : (2 * Real.pi / ((6 : ℕ) : ℝ)) = Real.pi / 3 := by push_cast; ring
  rw [ha, Real.cos_pi_div_three]
  norm_num

/-- **Rational half of Niven's classification.** For every `n` in the
exceptional set `{1, 2, 3, 4, 6}`, `cos(2π/n)` is rational. Combined with the
sibling `cos_two_pi_div_n_irrational` (irrational for `φ(n) ≥ 3`, i.e. for all
other `n`), this yields the full classification: `cos(2π/n)` is rational iff
`n ∈ {1, 2, 3, 4, 6}`. -/
theorem cos_two_pi_div_rational_of_mem {n : ℕ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6) :
    ¬ Irrational (Real.cos (2 * Real.pi / (n : ℕ))) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact cos_two_pi_div_one_rational
  · exact cos_two_pi_div_two_rational
  · exact cos_two_pi_div_three_rational
  · exact cos_two_pi_div_four_rational
  · exact cos_two_pi_div_six_rational

end NthRootIrrationalOQ01OQ01CosRational
