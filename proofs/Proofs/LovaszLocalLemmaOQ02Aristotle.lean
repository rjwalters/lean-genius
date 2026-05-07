/-
  Aristotle targets for Lovász Local Lemma — OQ-02 (Algebraic Tightness of T(d))
  Routine supporting lemmas for automated proof search.
  See LovaszLocalLemmaOQ02.lean for the main formalization.

  The symmetric LLL threshold is T(d) = d^d/(d+1)^{d+1}.
  Explicit values: T(1) = 1/4, T(2) = 4/27, T(3) = 27/256, T(4) = 256/3125.

  Criteria for inclusion:
  - NOT the main AM-GM maximum theorem (proved via Real.geom_mean_le_arith_mean2_weighted)
  - NOT the general equality case of AM-GM (hard, general machinery)
  - Strict inequalities for d = 1, 2, 3: x*(1-x)^d < T(d) when x ≠ 1/(d+1)
  - Equality characterizations for d = 1, 2, 3
  - d = 4 maximum bound (extending the d=1,2,3 pattern from parent)
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace LovaszLocalLemmaOQ02Aristotle

/-
  ## Section 1: Strict Maximum at d = 1

  T(1) = 1/4. For x ∈ [0,1] with x ≠ 1/2: x*(1-x) < 1/4.
  Algebraic identity: 1/4 - x*(1-x) = (x - 1/2)^2 > 0 when x ≠ 1/2.
-/

-- Aristotle target: strict d=1 bound at non-optimal point
-- Proof: 1/4 - x*(1-x) = (x - 1/2)^2 > 0 since x ≠ 1/2
theorem d1_strict (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / 2) :
    x * (1 - x) < 1 / 4 := by
  sorry

-- Aristotle target: equality at d=1 implies x = 1/2
-- Proof: from x*(1-x) = 1/4, we get (x - 1/2)^2 = 0, so x = 1/2
theorem d1_equality (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (h : x * (1 - x) = 1 / 4) : x = 1 / 2 := by
  sorry

-- Corollary: x*(1-x) ≤ 1/4 for x ∈ [0,1] (non-strict, supports parent proof)
theorem d1_maximum (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

/-
  ## Section 2: Strict Maximum at d = 2

  T(2) = 4/27. For x ∈ [0,1] with x ≠ 1/3: x*(1-x)^2 < 4/27.
  Factor: 4/27 - x*(1-x)^2 = (3x-1)^2 * (4 - 3x) / 27.
  Since x ≤ 1, (4 - 3x) ≥ 1 > 0. When x ≠ 1/3, (3x-1)^2 > 0.
-/

-- Aristotle target: strict d=2 bound at non-optimal point
-- Proof: (3x-1)^2 > 0 and (4-3x) > 0, combined via factored form
theorem d2_strict (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / 3) :
    x * (1 - x) ^ 2 < 4 / 27 := by
  sorry

-- Aristotle target: equality at d=2 implies x = 1/3
-- Proof: 4/27 = x*(1-x)^2 → (3x-1)^2*(4-3x) = 0 → 3x-1 = 0 (since 4-3x > 0)
theorem d2_equality (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (h : x * (1 - x) ^ 2 = 4 / 27) : x = 1 / 3 := by
  sorry

/-
  ## Section 3: Strict Maximum at d = 3

  T(3) = 27/256. For x ∈ [0,1] with x ≠ 1/4: x*(1-x)^3 < 27/256.
  Factor: 27 - 256*x*(1-x)^3 = (4x-1)^2 * (16x^2 - 40x + 27).
  Note: 16x^2 - 40x + 27 = (4x-5)^2/... + ... > 0 (discriminant -1/4·(256·27-40^2) < 0).
  Concretely: 16x^2 - 40x + 27 ≥ 2 for all x ∈ [0,1] (via completing the square).
-/

-- Aristotle target: 16x^2 - 40x + 27 > 0 for all rational x
-- Proof: discriminant 40^2 - 4*16*27 = 1600 - 1728 < 0, minimum at x=5/4 is 2
theorem d3_quadratic_pos (x : ℚ) : 0 < 16 * x ^ 2 - 40 * x + 27 := by
  nlinarith [sq_nonneg (4 * x - 5)]

-- Aristotle target: strict d=3 bound at non-optimal point
-- Proof: (4x-1)^2 > 0 (since x ≠ 1/4) and d3_quadratic_pos gives the other factor > 0
theorem d3_strict (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / 4) :
    x * (1 - x) ^ 3 < 27 / 256 := by
  sorry

-- Aristotle target: equality at d=3 implies x = 1/4
-- Proof: 27/256 = x*(1-x)^3 → (4x-1)^2*(16x^2-40x+27) = 0 → 4x-1 = 0
theorem d3_equality (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (h : x * (1 - x) ^ 3 = 27 / 256) : x = 1 / 4 := by
  sorry

/-
  ## Section 4: Maximum at d = 4

  T(4) = 4^4/5^5 = 256/3125, achieved at x = 1/5.
  Extends the explicit small-case pattern from the parent file (d=1,2,3).
  For the bound: 256/3125 - x*(1-x)^4 ≥ 0 follows from AM-GM on 5 terms:
    x, (1-x)/4, (1-x)/4, (1-x)/4, (1-x)/4
    with arithmetic mean 1/5 and T(4) = (1/5)^5 * 4^4.
-/

-- Aristotle target: d=4 maximum bound x*(1-x)^4 ≤ 256/3125 for x ∈ [0,1]
-- Proof strategy: 3125 * (256/3125 - x*(1-x)^4) = (5x-1)^2 * q(x) ≥ 0
theorem d4_maximum (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) ^ 4 ≤ 256 / 3125 := by
  sorry

-- d=4 achievement at x = 1/5 (norm_num provable, no sorry)
theorem d4_achieved : (1 : ℚ) / 5 * (1 - 1 / 5) ^ 4 = 256 / 3125 := by
  norm_num

-- Aristotle target: strict d=4 bound when x ≠ 1/5
theorem d4_strict (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hne : x ≠ 1 / 5) :
    x * (1 - x) ^ 4 < 256 / 3125 := by
  sorry

/-
  ## Section 5: Algebraic Helpers for AM-GM Equality Case

  Supporting the equality case of lllThreshold_strict_maximum in the parent.
  These characterize when x*(1-x)^d = T(d): iff x = 1/(d+1).
-/

-- Aristotle target: if x*(1-x) ≤ 1/4 is tight (equality), then x = 1/2
-- Combined characterization: x*(1-x) = 1/4 and x ∈ [0,1] → x = 1/2
theorem d1_tight_iff (x : ℚ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x * (1 - x) = 1 / 4 ↔ x = 1 / 2 := by
  constructor
  · exact d1_equality x hx hx1
  · intro h; rw [h]; norm_num

-- Arithmetic helper: (1/2 : ℚ) satisfies the d=1 equation (norm_num)
theorem d1_optimal_value : (1 : ℚ) / 2 * (1 - 1 / 2) = 1 / 4 := by norm_num

-- Arithmetic helper: (1/3 : ℚ) satisfies the d=2 equation (norm_num)
theorem d2_optimal_value : (1 : ℚ) / 3 * (1 - 1 / 3) ^ 2 = 4 / 27 := by norm_num

-- Arithmetic helper: (1/4 : ℚ) satisfies the d=3 equation (norm_num)
theorem d3_optimal_value : (1 : ℚ) / 4 * (1 - 1 / 4) ^ 3 = 27 / 256 := by norm_num

end LovaszLocalLemmaOQ02Aristotle
