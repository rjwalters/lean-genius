/-
  Aristotle targets for Erdős Problem #634
  Routine supporting lemmas for automated proof search.
  See Erdos634Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT congruent_implies_similar (false as stated — multiset equality allows reordering)
  - NOT 7_not_dissectable, 11_not_dissectable (axioms)
  - Dissectability theorems (squares_dissectable, etc.) provable by trivial construction:
    the Dissection type uses a placeholder area_sum condition without geometric tiling
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos634Aristotle

/-- A triangle represented by its three side lengths (a, b, c). -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  triangle_ineq_ab : a + b > c
  triangle_ineq_bc : b + c > a
  triangle_ineq_ca : c + a > b

/-- Two triangles are congruent if they have the same side lengths (as multisets). -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  Multiset.ofList [T₁.a, T₁.b, T₁.c] = Multiset.ofList [T₂.a, T₂.b, T₂.c]

/-- A dissection of triangle T into n pieces (placeholder tiling condition). -/
structure Dissection (T : Triangle) (n : ℕ) where
  pieces : Fin n → Triangle
  area_sum : (∑ i, (pieces i).a * (pieces i).b) > 0

/-- A valid congruent dissection: all pieces are congruent to each other. -/
def IsCongruentDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Congruent (D.pieces i) (D.pieces j)

/-- n is dissectable if some triangle can be cut into n congruent triangles. -/
def IsDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsCongruentDissection T n D

/-- The unit equilateral triangle with all sides equal to 1. -/
def unitEquilateral : Triangle where
  a := 1
  b := 1
  c := 1
  ha := by norm_num
  hb := by norm_num
  hc := by norm_num
  triangle_ineq_ab := by norm_num
  triangle_ineq_bc := by norm_num
  triangle_ineq_ca := by norm_num

-- Routine: Congruence is reflexive.
-- The multiset [a, b, c] equals itself.
theorem congruent_refl (T : Triangle) : Congruent T T := rfl

-- Routine: For k ≥ 1, k^2 ≥ 1.
-- k ≥ 1 implies k^2 ≥ 1^2 = 1.
theorem sq_pos_of_pos (k : ℕ) (hk : k ≥ 1) : k ^ 2 ≥ 1 := by
  sorry

-- Routine: The sum of k^2 copies of 1 equals k^2.
-- ∑ i : Fin (k^2), (1 : ℝ) = k^2.
theorem sum_fin_sq_one (k : ℕ) : ∑ _i : Fin (k ^ 2), (1 : ℝ) = k ^ 2 := by
  sorry

-- Routine: For k ≥ 1, k^2 > 0 as a real number.
-- k ≥ 1 implies k^2 ≥ 1 > 0.
theorem sq_pos_real (k : ℕ) (hk : k ≥ 1) : (k : ℝ) ^ 2 > 0 := by
  sorry

-- Routine: The sum of 2*k^2 copies of 1 equals 2*k^2.
theorem sum_fin_two_sq_one (k : ℕ) : ∑ _i : Fin (2 * k ^ 2), (1 : ℝ) = 2 * k ^ 2 := by
  sorry

-- Routine: For k ≥ 1, 2 * k^2 > 0 as a real number.
theorem two_sq_pos_real (k : ℕ) (hk : k ≥ 1) : 2 * (k : ℝ) ^ 2 > 0 := by
  sorry

-- Routine: The sum of 3*k^2 copies of 1 equals 3*k^2.
theorem sum_fin_three_sq_one (k : ℕ) : ∑ _i : Fin (3 * k ^ 2), (1 : ℝ) = 3 * k ^ 2 := by
  sorry

-- Routine: For k ≥ 1, 3 * k^2 > 0 as a real number.
theorem three_sq_pos_real (k : ℕ) (hk : k ≥ 1) : 3 * (k : ℝ) ^ 2 > 0 := by
  sorry

-- Routine: The sum of 6*k^2 copies of 1 equals 6*k^2.
theorem sum_fin_six_sq_one (k : ℕ) : ∑ _i : Fin (6 * k ^ 2), (1 : ℝ) = 6 * k ^ 2 := by
  sorry

-- Routine: For k ≥ 1, 6 * k^2 > 0 as a real number.
theorem six_sq_pos_real (k : ℕ) (hk : k ≥ 1) : 6 * (k : ℝ) ^ 2 > 0 := by
  sorry

-- Routine: For n, m ≥ 1, n^2 + m^2 > 0 as a real number.
theorem sum_sq_pos_real (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    (n : ℝ) ^ 2 + m ^ 2 > 0 := by
  sorry

-- Routine: Perfect squares are dissectable.
-- Use k^2 copies of the unit equilateral triangle.
-- All pieces are the same triangle, so all are congruent.
-- area_sum = k^2 * (1 * 1) = k^2 > 0 for k ≥ 1.
theorem squares_dissectable (k : ℕ) (hk : k ≥ 1) : IsDissectable (k ^ 2) := by
  sorry

-- Routine: 2n² is dissectable.
-- Use 2*n^2 copies of the unit equilateral triangle.
theorem two_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (2 * n ^ 2) := by
  sorry

-- Routine: 3n² is dissectable.
-- Use 3*n^2 copies of the unit equilateral triangle.
theorem three_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (3 * n ^ 2) := by
  sorry

-- Routine: 6n² is dissectable.
-- Use 6*n^2 copies of the unit equilateral triangle.
theorem six_squares_dissectable (n : ℕ) (hn : n ≥ 1) : IsDissectable (6 * n ^ 2) := by
  sorry

-- Routine: n² + m² is dissectable for n, m ≥ 1.
-- Use n^2 + m^2 copies of the unit equilateral triangle.
theorem sum_squares_dissectable (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ 1) :
    IsDissectable (n ^ 2 + m ^ 2) := by
  sorry

-- Routine: 27 is dissectable.
-- 27 = 3 * 3^2 = 3 * 9, so follows from three_squares_dissectable 3.
theorem twenty_seven_dissectable : IsDissectable 27 := by
  sorry

end Erdos634Aristotle
