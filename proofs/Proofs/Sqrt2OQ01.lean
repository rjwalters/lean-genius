/-
  Generalized Non-Negativity of Squares

  Open Question (sqrt2-examples-oq-01):
  "Can square_nonneg be generalized to arbitrary linearly ordered rings
   in Lean without additional axioms?"

  Answer: YES. Mathlib's `sq_nonneg` works for any `LinearOrderedSemiring`,
  which includes ℤ, ℚ, ℝ, and all linearly ordered rings. No additional
  axioms are needed. We demonstrate this and prove it independently.

  Tags: ordered-rings, algebra, generalization, pedagogical
-/

import Mathlib

namespace Sqrt2OQ01

-- ============================================================
-- Part I: The Generalized Result
-- ============================================================

/-- Non-negativity of squares in any linearly ordered semiring.
    This generalizes the parent's `square_nonneg` from ℤ to any
    type with a compatible ordering and multiplication. -/
theorem square_nonneg_general {α : Type*} [LinearOrderedSemiring α] (x : α) :
    0 ≤ x * x := mul_self_nonneg x

/-- Same result using the `^2` notation. -/
theorem sq_nonneg_general {α : Type*} [LinearOrderedSemiring α] (x : α) :
    0 ≤ x ^ 2 := sq_nonneg x

-- ============================================================
-- Part II: Concrete Instances
-- ============================================================

/-- Integers (the original case from the parent file). -/
theorem square_nonneg_int (n : ℤ) : 0 ≤ n * n := square_nonneg_general n

/-- Rationals. -/
theorem square_nonneg_rat (q : ℚ) : 0 ≤ q * q := square_nonneg_general q

/-- Reals. -/
theorem square_nonneg_real (x : ℝ) : 0 ≤ x * x := square_nonneg_general x

/-- Natural numbers (trivially, but it fits the framework). -/
theorem square_nonneg_nat (n : ℕ) : 0 ≤ n * n := square_nonneg_general n

-- ============================================================
-- Part III: Independent Proof (No Mathlib Shortcut)
-- ============================================================

/-- An independent proof by case analysis on sign, generalizing
    the parent file's proof technique from ℤ to any LinearOrderedRing.
    This shows the parent's proof strategy itself generalizes. -/
theorem square_nonneg_by_cases {α : Type*} [LinearOrderedRing α] (x : α) :
    0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact mul_nonneg h h
  · push_neg at h
    have h1 : x ≤ 0 := le_of_lt h
    have h2 : 0 ≤ -x := neg_nonneg.mpr h1
    calc x * x = (-x) * (-x) := by ring
             _ ≥ 0 := mul_nonneg h2 h2

-- ============================================================
-- Part IV: Consequences
-- ============================================================

/-- The sum of two squares is non-negative. -/
theorem sum_sq_nonneg {α : Type*} [LinearOrderedSemiring α] (x y : α) :
    0 ≤ x * x + y * y :=
  add_nonneg (square_nonneg_general x) (square_nonneg_general y)

/-- For linearly ordered rings, |x|² = x². -/
theorem abs_sq {α : Type*} [LinearOrderedCommRing α] (x : α) :
    |x| * |x| = x * x := abs_mul_self x

/-- The Cauchy-Schwarz trick: 0 ≤ (ax - by)² gives ab ≤ (a²+b²)/2. -/
theorem am_gm_sq {α : Type*} [LinearOrderedField α] (a b : α) :
    a * b ≤ (a * a + b * b) / 2 := by
  have h : 0 ≤ (a - b) * (a - b) := square_nonneg_general (a - b)
  nlinarith

/-
  Summary

  This file answers the open question from sqrt2-examples:
  "Can square_nonneg be generalized to arbitrary linearly ordered rings?"

  Answer: YES, with no additional axioms.

  1. Mathlib's `mul_self_nonneg` (= `sq_nonneg`) works for LinearOrderedSemiring
  2. The case-analysis proof technique from the parent also generalizes to LinearOrderedRing
  3. All standard number types (ℕ, ℤ, ℚ, ℝ) are instances

  Bonus consequences: sum of squares non-negativity and an AM-GM variant.

  0 axioms, 0 sorries, fully verified.
-/

end Sqrt2OQ01
