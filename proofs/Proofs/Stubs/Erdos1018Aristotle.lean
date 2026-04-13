/-
  Aristotle targets for Erdos1018Problem
  Routine supporting lemmas for automated proof search.
  See Proofs/Stubs/Erdos1018Problem.lean for the main formalization.

  These lemmas provide building blocks for non-planar subgraphs in dense graphs:
  - Arithmetic about the planar bound 3n - 6
  - Natural number power inequalities (n^k vs linear)
  - Logical deductions about existsBoundingConstant
  - explicitBound (= ⌈1/ε²⌉) basic properties
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace Erdos1018.Aristotle

/-
  ## Section 1: Arithmetic About the Planar Edge Bound 3n - 6

  Euler's formula gives: every planar graph on n ≥ 3 vertices has ≤ 3n - 6 edges.
  These lemmas establish basic facts about this bound.
-/

-- Concrete values of 3n - 6
theorem planar_bound_at_3 : 3 * 3 - 6 = 3 := by norm_num

theorem planar_bound_at_4 : 3 * 4 - 6 = 6 := by norm_num

theorem planar_bound_at_5 : 3 * 5 - 6 = 9 := by norm_num

theorem planar_bound_at_6 : 3 * 6 - 6 = 12 := by norm_num

theorem planar_bound_at_10 : 3 * 10 - 6 = 24 := by norm_num

theorem planar_bound_at_100 : 3 * 100 - 6 = 294 := by norm_num

-- 3n - 6 is bounded by 3n
theorem planar_bound_le_3n (n : ℕ) : 3 * n - 6 ≤ 3 * n := by omega

-- 3n - 6 < n² for n ≥ 5
theorem planar_bound_lt_square_5 (n : ℕ) (hn : n ≥ 5) : 3 * n - 6 < n ^ 2 := by
  sorry

-- 3n - 6 < n² for n ≥ 7 (a common threshold in planarity arguments)
theorem planar_bound_lt_square_7 (n : ℕ) (hn : n ≥ 7) : 3 * n - 6 < n ^ 2 := by
  sorry

-- Monotonicity: planar bound grows with n
theorem planar_bound_mono (n m : ℕ) (h : n ≤ m) : 3 * n - 6 ≤ 3 * m - 6 := by
  omega

-- If edgecount > planar bound, then edgecount ≥ planar bound + 1
theorem edgecount_exceeds_by_one (e n : ℕ) (h : e > 3 * n - 6) : e ≥ 3 * n - 6 + 1 := by
  omega

-- If edgecount ≤ planar bound, then edgecount < planar bound + 1
theorem edgecount_at_most_bound (e n : ℕ) (h : e ≤ 3 * n - 6) : e < 3 * n - 6 + 1 := by
  omega

-- 3n - 6 > n when n > 6
theorem planar_bound_gt_n (n : ℕ) (hn : n > 6) : 3 * n - 6 > n := by
  omega

/-
  ## Section 2: Integer Power Growth vs Linear Bound

  For k ≥ 2, the power n^k grows faster than 3n - 6.
  Key: n^2 ≥ 3n for n ≥ 3, and n^2 > 3n - 6 for n ≥ 4.
-/

-- n^2 ≥ 3n for n ≥ 3
theorem sq_ge_3n (n : ℕ) (hn : n ≥ 3) : n ^ 2 ≥ 3 * n := by
  sorry

-- n^2 > 3n - 6 for n ≥ 4 (key bound for the planarity argument)
theorem sq_gt_planar_bound (n : ℕ) (hn : n ≥ 4) : n ^ 2 > 3 * n - 6 := by
  sorry

-- n^2 ≥ 4n for n ≥ 4
theorem sq_ge_4n (n : ℕ) (hn : n ≥ 4) : n ^ 2 ≥ 4 * n := by
  sorry

-- n^3 > 3n - 6 for n ≥ 3
theorem cube_gt_planar_bound (n : ℕ) (hn : n ≥ 3) : n ^ 3 > 3 * n - 6 := by
  sorry

-- Power monotonicity: n^k ≤ n^(k+1) for n ≥ 1
theorem pow_le_pow_succ (n k : ℕ) (hn : n ≥ 1) : n ^ k ≤ n ^ (k + 1) := by
  sorry

-- If n^2 > 3n - 6 and edgeCount ≥ n^2, then edgeCount > 3n - 6
theorem edgecount_dense_exceeds_planar (e n : ℕ) (hn : n ≥ 4)
    (h : e ≥ n ^ 2) : e > 3 * n - 6 := by
  have hq : n ^ 2 > 3 * n - 6 := by sorry
  omega

/-
  ## Section 3: The explicitBound Function

  explicitBound ε = ⌈1/ε²⌉ is a polynomial bound on C_ε.
-/

-- ε² > 0 when ε > 0
theorem sq_pos (ε : ℝ) (hε : ε > 0) : ε ^ 2 > 0 := by
  positivity

-- 1/ε² > 0 when ε > 0
theorem inv_sq_pos (ε : ℝ) (hε : ε > 0) : 1 / ε ^ 2 > 0 := by
  positivity

-- 1/ε² ≥ 1 when 0 < ε ≤ 1
theorem inv_sq_ge_one (ε : ℝ) (hε : ε > 0) (hε1 : ε ≤ 1) : 1 / ε ^ 2 ≥ 1 := by
  sorry

-- ε² ≤ 1 when 0 < ε ≤ 1
theorem sq_le_one_of_le_one (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) : ε ^ 2 ≤ 1 := by
  sorry

-- 1/ε² is antitone: ε₁ ≤ ε₂ → 1/ε₁² ≥ 1/ε₂²
theorem inv_sq_antitone (ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0)
    (h : ε₁ ≤ ε₂) : 1 / ε₁ ^ 2 ≥ 1 / ε₂ ^ 2 := by
  sorry

-- 1/ε is less than 1/ε² when 0 < ε < 1
theorem inv_lt_inv_sq (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : 1 / ε < 1 / ε ^ 2 := by
  sorry

/-
  ## Section 4: Nat Ceiling Properties

  Facts about ⌈x⌉ used for bounding the constant C_ε.
-/

-- ⌈x⌉ ≥ 1 when x > 0
theorem ceil_pos_of_pos (x : ℝ) (hx : x > 0) : ⌈x⌉ ≥ 1 := by
  sorry

-- ⌈x⌉ ≤ ⌈y⌉ when x ≤ y
theorem ceil_mono_of_le (x y : ℝ) (h : x ≤ y) : ⌈x⌉ ≤ ⌈y⌉ := by
  sorry

-- ⌈x⌉ ≥ x (Nat.ceil lower bound)
theorem ceil_ge (x : ℝ) (hx : 0 ≤ x) : (⌈x⌉ : ℝ) ≥ x := by
  sorry

end Erdos1018.Aristotle
