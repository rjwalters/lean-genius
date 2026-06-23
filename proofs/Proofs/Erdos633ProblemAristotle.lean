/-
  Aristotle targets for Erdos633Problem

  Routine supporting lemmas for automated proof search.
  See Erdos633Problem.lean for the main formalization (classifying triangles
  that admit only square-number congruent dissections; Erdős–Soifer, OPEN).

  These lemmas provide elementary building blocks Aristotle can attack:
  - IsSquare arithmetic on small naturals
  - Square / non-square decisions for 0..10
  - n² is always a square (universal direction)
  - Soifer triangle: numeric witness facts (sqrt 2, sqrt 3, sqrt 4 = 2)
  - DissectionCounts membership trivia
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Erdos633.Aristotle

/-
  ## Section 1: IsSquare definition (mirrors Erdos633Problem)
-/

/-- A natural number is a perfect square. -/
def IsSquare (n : ℕ) : Prop := ∃ k : ℕ, n = k^2

/-
  ## Section 2: Small explicit squares (TRIVIAL witnesses)

  Aristotle can dispatch each of these by providing the witness `k`.
-/

theorem isSquare_zero : IsSquare 0 := ⟨0, by norm_num⟩
theorem isSquare_one : IsSquare 1 := ⟨1, by norm_num⟩
theorem isSquare_four : IsSquare 4 := ⟨2, by norm_num⟩
theorem isSquare_nine : IsSquare 9 := ⟨3, by norm_num⟩
theorem isSquare_sixteen : IsSquare 16 := ⟨4, by norm_num⟩
theorem isSquare_twentyfive : IsSquare 25 := ⟨5, by norm_num⟩
theorem isSquare_thirtysix : IsSquare 36 := ⟨6, by norm_num⟩
theorem isSquare_fortynine : IsSquare 49 := ⟨7, by norm_num⟩
theorem isSquare_sixtyfour : IsSquare 64 := ⟨8, by norm_num⟩
theorem isSquare_eightyone : IsSquare 81 := ⟨9, by norm_num⟩
theorem isSquare_hundred : IsSquare 100 := ⟨10, by norm_num⟩

/-
  ## Section 3: Universal square witness

  Every square number k² is an IsSquare. This is by definition.
-/

theorem isSquare_sq (k : ℕ) : IsSquare (k^2) := ⟨k, rfl⟩

theorem isSquare_one_sq : IsSquare (1^2) := isSquare_sq 1
theorem isSquare_two_sq : IsSquare (2^2) := isSquare_sq 2
theorem isSquare_three_sq : IsSquare (3^2) := isSquare_sq 3

/-
  ## Section 4: Non-squares (HARDER — Aristotle may search bounded ranges)

  These require ruling out all possible k with k² = n, which Aristotle can
  attempt via decide / norm_num / omega combinations.
-/

theorem not_isSquare_two : ¬ IsSquare 2 := by sorry
theorem not_isSquare_three : ¬ IsSquare 3 := by sorry
theorem not_isSquare_five : ¬ IsSquare 5 := by sorry
theorem not_isSquare_six : ¬ IsSquare 6 := by sorry
theorem not_isSquare_seven : ¬ IsSquare 7 := by sorry
theorem not_isSquare_eight : ¬ IsSquare 8 := by sorry
theorem not_isSquare_ten : ¬ IsSquare 10 := by sorry

/-
  ## Section 5: Soifer triangle numeric facts

  The Soifer triangle has sides √2, √3, √4. We expose elementary positivity
  and ordering facts. (The square-only property itself is the open question.)
-/

theorem sqrt_two_pos : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt_three_pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
theorem sqrt_four_eq_two : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem sqrt_two_lt_sqrt_three : Real.sqrt 2 < Real.sqrt 3 := by
  apply Real.sqrt_lt_sqrt <;> norm_num

theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 from sqrt_four_eq_two.symm]
  apply Real.sqrt_lt_sqrt <;> norm_num

theorem sqrt_two_lt_two : Real.sqrt 2 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 from sqrt_four_eq_two.symm]
  apply Real.sqrt_lt_sqrt <;> norm_num

theorem one_lt_sqrt_two : (1 : ℝ) < Real.sqrt 2 := by sorry

theorem one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by sorry

/-
  ## Section 6: Triangle inequality on Soifer sides

  The Soifer triangle (√2, √3, 2) is a genuine triangle. Each pair-sum exceeds
  the third side.
-/

theorem soifer_tri_ab : Real.sqrt 2 + Real.sqrt 3 > Real.sqrt 4 := by sorry

theorem soifer_tri_bc : Real.sqrt 3 + Real.sqrt 4 > Real.sqrt 2 := by sorry

theorem soifer_tri_ca : Real.sqrt 4 + Real.sqrt 2 > Real.sqrt 3 := by sorry

/-
  ## Section 7: Square arithmetic identities

  Routine identities Aristotle can leverage when reasoning about n² dissections.
-/

theorem sq_succ (n : ℕ) : (n + 1)^2 = n^2 + 2*n + 1 := by ring

theorem sq_add (a b : ℕ) : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring

theorem sq_pos_of_pos {n : ℕ} (h : 0 < n) : 0 < n^2 := by positivity

theorem isSquare_mul_sq (n k : ℕ) : IsSquare n → IsSquare (n * k^2) := by sorry

end Erdos633.Aristotle
