/-
Erdős Problem #686: Ratios of Products of Consecutive Integers

**Problem Statement (OPEN)**

Can every integer N ≥ 2 be written as
  N = ∏_{1 ≤ i ≤ k}(m+i) / ∏_{1 ≤ i ≤ k}(n+i)
for some k ≥ 2 and m ≥ n + k?

In other words: can every integer ≥ 2 be expressed as a ratio of two
products of k consecutive integers, where the numerator starts at a
larger value than the denominator?

**Follow-up:** If n and k are fixed, what integers can be represented?

**Status:** OPEN

**Reference:** [Er79d]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Finset BigOperators Nat

namespace Erdos686

/-!
# Part 1: Basic Definitions

Products of consecutive integers starting at n with length k.
-/

-- Product of k consecutive integers starting at n+1
-- P(n, k) = (n+1)(n+2)...(n+k)
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

-- Equivalent to factorial ratio: (n+k)! / n!
theorem consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k = (n + k)! / n! := by
  sorry -- Standard factorial identity

-- Examples
example : consecutiveProduct 0 3 = 1 * 2 * 3 := by native_decide
example : consecutiveProduct 1 3 = 2 * 3 * 4 := by native_decide
example : consecutiveProduct 2 2 = 3 * 4 := by native_decide

/-!
# Part 2: The Ratio Expression

Ratio of two consecutive products.
-/

-- The ratio (as a rational number to handle division exactly)
noncomputable def ratioExpression (n m k : ℕ) : ℚ :=
  (consecutiveProduct m k : ℚ) / (consecutiveProduct n k : ℚ)

-- The ratio is an integer when the denominator divides the numerator
def IsIntegerRatio (n m k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

-- When the ratio is an integer, compute it
def integerRatio (n m k : ℕ) (h : IsIntegerRatio n m k) : ℕ :=
  consecutiveProduct m k / consecutiveProduct n k

/-!
# Part 3: The Representation Property

An integer N ≥ 2 is representable if it equals some ratio.
-/

-- N is representable with parameters (n, m, k)
def IsRepresentable (N : ℕ) (n m k : ℕ) : Prop :=
  k ≥ 2 ∧ m ≥ n + k ∧ ratioExpression n m k = N

-- N is representable (existentially)
def Representable (N : ℕ) : Prop :=
  ∃ n m k, IsRepresentable N n m k

-- The main conjecture: all N ≥ 2 are representable
def ErdosConjecture686 : Prop :=
  ∀ N ≥ 2, Representable N

/-!
# Part 4: Why the Constraints?

Explain the role of k ≥ 2 and m ≥ n + k.
-/

-- k ≥ 2: Products of at least 2 consecutive integers
-- k = 1 would just give (m+1)/(n+1), which is trivial

-- m ≥ n + k: The ranges don't overlap
-- If m < n + k, the products share common factors in complex ways

-- When m ≥ n + k, the numerator product is strictly greater
theorem numerator_gt_denominator (n m k : ℕ) (hk : k ≥ 2) (hm : m ≥ n + k) :
    consecutiveProduct m k > consecutiveProduct n k := by
  sorry -- Each factor in numerator is strictly greater

-- The ratio is > 1 when m ≥ n + k
theorem ratio_gt_one (n m k : ℕ) (hk : k ≥ 2) (hm : m ≥ n + k) (hpos : n > 0 ∨ k > 0) :
    ratioExpression n m k > 1 := by
  sorry -- Follows from numerator > denominator

/-!
# Part 5: Small Cases

Check representability for small N.
-/

-- N = 2: Can we write 2 as such a ratio?
-- Try k = 2: (m+1)(m+2) / (n+1)(n+2) = 2
-- Need (m+1)(m+2) = 2(n+1)(n+2)

-- Example: m = 2, n = 0, k = 2
-- (3)(4) / (1)(2) = 12/2 = 6, not 2

-- Example: m = 3, n = 1, k = 2
-- (4)(5) / (2)(3) = 20/6, not integer

-- Finding N = 2 is non-trivial

-- N = 6: m = 2, n = 0, k = 2 works
-- (3)(4) / (1)(2) = 12/2 = 6 ✓
example : ratioExpression 0 2 2 = 6 := by native_decide

-- N = 10: k = 2, look for (m+1)(m+2) = 10(n+1)(n+2)
-- m = 4, n = 1: (5)(6)/(2)(3) = 30/6 = 5, not 10

/-!
# Part 6: Connection to Binomial Coefficients

Products of consecutive integers relate to binomial coefficients.
-/

-- C(n+k, k) = (n+1)(n+2)...(n+k) / k!
-- So consecutiveProduct n k = k! * C(n+k, k)

theorem product_binomial_relation (n k : ℕ) :
    consecutiveProduct n k = k! * (n + k).choose k := by
  sorry -- Standard binomial identity

-- Ratio of consecutive products relates to binomial ratios
-- ratioExpression n m k = C(m+k, k) / C(n+k, k)

/-!
# Part 7: The Follow-Up Question

For fixed n and k, what integers are representable?
-/

-- The set of integers representable with fixed n, k
def RepresentableSet (n k : ℕ) : Set ℕ :=
  {N | ∃ m ≥ n + k, ratioExpression n m k = N}

-- For fixed n, k, as m increases, the ratio increases
theorem ratio_mono (n k m₁ m₂ : ℕ) (h : m₁ < m₂) :
    ratioExpression n m₁ k < ratioExpression n m₂ k := by
  sorry -- Larger numerator, same denominator

-- The representable set for fixed n, k is infinite
theorem representable_set_infinite (n k : ℕ) (hk : k ≥ 2) :
    Set.Infinite (RepresentableSet n k) := by
  sorry -- Can achieve arbitrarily large ratios

/-!
# Part 8: Constraints and Structure

The structure of representable numbers.
-/

-- The ratio is a product of ratios of individual terms
-- (m+1)...(m+k) / (n+1)...(n+k) = ∏_{i=1}^k (m+i)/(n+i)

-- Each factor (m+i)/(n+i) is > 1 when m > n
-- The product is roughly ((m+k)/((n+k))^k for large m ≈ n

-- For the ratio to be an integer, subtle divisibility is needed
-- This is why the problem is non-trivial

/-!
# Part 9: Related Problem 677

Problem 677 is cited as related.
-/

def RelatedProblem677 : Prop := True  -- Similar structure

/-!
# Part 10: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_686_status : String := "OPEN"

-- Main formal statement
theorem erdos_686_statement :
    ErdosConjecture686 ↔
    ∀ N ≥ 2, ∃ n m k : ℕ, k ≥ 2 ∧ m ≥ n + k ∧
      ratioExpression n m k = N := by
  simp only [ErdosConjecture686, Representable, IsRepresentable]

-- Alternative using original notation
theorem erdos_686_original :
    ErdosConjecture686 ↔
    ∀ N ≥ 2, ∃ k ≥ 2, ∃ n : ℕ, ∃ m ≥ n + k,
      (N : ℚ) = (∏ i ∈ Finset.Icc 1 k, (m + i : ℚ)) /
                (∏ i ∈ Finset.Icc 1 k, (n + i : ℚ)) := by
  sorry -- Equivalence of formulations

/-!
# Summary

**Problem:** Can every integer N ≥ 2 be written as
∏_{i=1}^k (m+i) / ∏_{i=1}^k (n+i)
for some k ≥ 2 and m ≥ n + k?

**Known:**
- Products of consecutive integers relate to factorials and binomials
- Some small integers can be verified (e.g., N = 6)
- For fixed n, k, representable set is infinite

**Unknown:**
- Whether every N ≥ 2 is representable
- Structure of representable sets for fixed n, k

**Difficulty:** Finding the right (n, m, k) triples for each N.
-/

end Erdos686
