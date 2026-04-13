/-
  Aristotle targets for AMGM Inequality
  Routine supporting lemmas for automated proof search.
  See AMGMInequality.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main AM-GM theorems (already fully proved)
  - Routine real number inequalities that support AM-GM proofs
  - No definition sorries
  - No axioms

  Included targets (5):
  - sq_nonneg': x^2 ≥ 0 for any real x
  - two_mul_le_sq_add_sq: 2*a*b ≤ a^2 + b^2
  - sqrt_sq: Real.sqrt (a^2) = a for nonneg a
  - mul_nonneg': 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  - add_div_two_ge_sqrt: (a + b) / 2 ≥ Real.sqrt (a * b) for nonneg a, b
-/
import Mathlib

open Real

namespace AMGMInequalityAristotle

-- Routine: squares are nonneg.
-- x^2 ≥ 0 for any real x.
theorem sq_nonneg' (x : ℝ) : 0 ≤ x ^ 2 := by
  sorry

-- Routine: 2ab ≤ a² + b².
-- Equivalent to 0 ≤ (a-b)², which unfolds to a² - 2ab + b² ≥ 0.
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  sorry

-- Routine: sqrt(a²) = a for nonneg a.
-- Standard real square root identity.
theorem sqrt_sq_of_nonneg (a : ℝ) (ha : 0 ≤ a) : Real.sqrt (a ^ 2) = a := by
  sorry

-- Routine: product of nonneg reals is nonneg.
-- 0 ≤ a → 0 ≤ b → 0 ≤ a * b.
theorem mul_nonneg' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  sorry

-- Routine: (a + b) / 2 ≥ 0 when a, b ≥ 0.
-- Arithmetic mean of nonneg numbers is nonneg.
theorem half_sum_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ (a + b) / 2 := by
  sorry

end AMGMInequalityAristotle
