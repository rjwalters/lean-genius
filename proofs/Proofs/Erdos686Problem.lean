/-
Erdos Problem #686: Ratios of Products of Consecutive Integers

Source: https://erdosproblems.com/686
Status: OPEN

Statement:
Can every integer N >= 2 be written as
  N = prod_{1 <= i <= k}(m+i) / prod_{1 <= i <= k}(n+i)
for some k >= 2 and m >= n + k?

Background:
- Products of k consecutive integers equal k! * C(n+k, k)
- k >= 2 excludes the trivial single-factor case
- m >= n + k ensures the ranges don't overlap

Reference: [Er79d]
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Finset BigOperators Nat

namespace Erdos686

-- ## Part I: Consecutive Products

/-- Product of k consecutive integers starting at n+1: P(n,k) = (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- P(n,k) = (n+k)! / n!. This is a standard identity proved by induction on k. -/
theorem consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k * n ! = (n + k) ! := by sorry

/-- P(n,k) = k! * C(n+k, k). Follows from the definition of binomial coefficients. -/
theorem product_binomial_relation (n k : ℕ) :
    consecutiveProduct n k = k ! * (n + k).choose k := by sorry

-- ## Part II: The Ratio Expression

/-- The ratio P(m,k)/P(n,k) as a rational number. -/
noncomputable def ratioExpression (n m k : ℕ) : ℚ :=
  (consecutiveProduct m k : ℚ) / (consecutiveProduct n k : ℚ)

/-- The ratio equals C(m+k,k) / C(n+k,k) when expressed via binomials. -/
theorem ratio_as_binomials (n m k : ℕ) (hk : k ≥ 1) :
    ratioExpression n m k = ((m + k).choose k : ℚ) / ((n + k).choose k : ℚ) := by sorry

/-- The ratio is an integer when the denominator divides the numerator. -/
def IsIntegerRatio (n m k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

-- ## Part III: The Representation Property

/-- N is representable with parameters (n, m, k). -/
def IsRepresentable (N : ℕ) (n m k : ℕ) : Prop :=
  k ≥ 2 ∧ m ≥ n + k ∧ ratioExpression n m k = N

/-- N is representable (existentially). -/
def Representable (N : ℕ) : Prop :=
  ∃ n m k, IsRepresentable N n m k

/-- Erdos Problem #686 (OPEN):
    Every integer N >= 2 can be expressed as a ratio of two products
    of k consecutive integers with non-overlapping ranges. -/
axiom erdos_686_conjecture : ∀ N ≥ 2, Representable N

-- ## Part IV: Structural Properties

/-- When m >= n + k, the numerator product exceeds the denominator.
    Each factor (m+i) > (n+i) since m > n. -/
axiom numerator_gt_denominator (n m k : ℕ) (hk : k ≥ 2) (hm : m ≥ n + k) :
    consecutiveProduct m k > consecutiveProduct n k

/-- The ratio increases monotonically with m (for fixed n, k). -/
axiom ratio_mono (n k m1 m2 : ℕ) (h : m1 < m2) :
    ratioExpression n m1 k < ratioExpression n m2 k

-- ## Part V: Verified Examples

/-- N = 2: C(4,2)/C(3,2) = 6/3 = 2 using k=2, n=1, m=2.
    P(2,2)/P(1,2) = (3*4)/(2*3) = 12/6 = 2. -/
theorem example_N2 : IsIntegerRatio 1 2 2 := by
  unfold IsIntegerRatio consecutiveProduct
  decide

/-- N = 6: P(2,2)/P(0,2) = (3*4)/(1*2) = 12/2 = 6. -/
theorem example_N6 : IsIntegerRatio 0 2 2 ∧ consecutiveProduct 2 2 / consecutiveProduct 0 2 = 6 := by
  constructor
  · unfold IsIntegerRatio consecutiveProduct; decide
  · native_decide

-- ## Part VI: Follow-Up Question

/-- The set of integers representable with fixed n, k. -/
def RepresentableSet (n k : ℕ) : Set ℕ :=
  {N | ∃ m ≥ n + k, ratioExpression n m k = N}

/-- For fixed n, k >= 2, the representable set is infinite. -/
axiom representable_set_infinite (n k : ℕ) (hk : k ≥ 2) :
    Set.Infinite (RepresentableSet n k)

-- ## Part VII: Connections

/-- Connection to Problem #677: integers as products of consecutive integers.
    This is the special case where the denominator product is 1. -/
def problem_677_special_case (N : ℕ) : Prop :=
  ∃ n k : ℕ, k ≥ 2 ∧ consecutiveProduct n k = N

-- ## Part VIII: Summary

/-- The conjecture is equivalent to the explicit form. -/
theorem erdos_686_equiv :
    (∀ N ≥ 2, Representable N) ↔
    ∀ N ≥ 2, ∃ n m k : ℕ, k ≥ 2 ∧ m ≥ n + k ∧
      ratioExpression n m k = N := by
  simp only [Representable, IsRepresentable]

end Erdos686
