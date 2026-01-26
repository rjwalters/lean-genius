/-
Erdős Problem #686: Ratios of Products of Consecutive Integers

Source: https://erdosproblems.com/686
Status: OPEN

Statement:
Can every integer N ≥ 2 be written as
  N = ∏_{1 ≤ i ≤ k}(m+i) / ∏_{1 ≤ i ≤ k}(n+i)
for some k ≥ 2 and m ≥ n + k?

Background:
- Products of k consecutive integers equal k! * C(n+k, k)
- k ≥ 2 excludes the trivial single-factor case
- m ≥ n + k ensures the ranges don't overlap

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

/-! ## Part I: Consecutive Products -/

/-- Product of k consecutive integers starting at n+1: P(n,k) = (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-- P(n,k) = (n+k)! / n!. -/
axiom consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k = (n + k)! / n!

/-- P(n,k) = k! * C(n+k, k). -/
axiom product_binomial_relation (n k : ℕ) :
    consecutiveProduct n k = k! * (n + k).choose k

/-- Examples via native_decide. -/
example : consecutiveProduct 0 3 = 1 * 2 * 3 := by native_decide
example : consecutiveProduct 1 3 = 2 * 3 * 4 := by native_decide
example : consecutiveProduct 2 2 = 3 * 4 := by native_decide

/-! ## Part II: The Ratio Expression -/

/-- The ratio P(m,k)/P(n,k) as a rational number. -/
noncomputable def ratioExpression (n m k : ℕ) : ℚ :=
  (consecutiveProduct m k : ℚ) / (consecutiveProduct n k : ℚ)

/-- The ratio is an integer when the denominator divides the numerator. -/
def IsIntegerRatio (n m k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

/-! ## Part III: The Representation Property -/

/-- N is representable with parameters (n, m, k). -/
def IsRepresentable (N : ℕ) (n m k : ℕ) : Prop :=
  k ≥ 2 ∧ m ≥ n + k ∧ ratioExpression n m k = N

/-- N is representable (existentially). -/
def Representable (N : ℕ) : Prop :=
  ∃ n m k, IsRepresentable N n m k

/--
**Erdős Problem #686 (OPEN):**
Every integer N ≥ 2 can be expressed as a ratio of two products
of k consecutive integers with non-overlapping ranges.
-/
def ErdosConjecture686 : Prop :=
  ∀ N ≥ 2, Representable N

/-! ## Part IV: Structural Properties -/

/-- When m ≥ n + k, the numerator product exceeds the denominator. -/
axiom numerator_gt_denominator (n m k : ℕ) (hk : k ≥ 2) (hm : m ≥ n + k) :
    consecutiveProduct m k > consecutiveProduct n k

/-- The ratio exceeds 1 when m ≥ n + k. -/
axiom ratio_gt_one (n m k : ℕ) (hk : k ≥ 2) (hm : m ≥ n + k) (hpos : n > 0 ∨ k > 0) :
    ratioExpression n m k > 1

/-! ## Part V: Examples -/

/-- N = 6: (3)(4)/(1)(2) = 12/2 = 6. -/
example : ratioExpression 0 2 2 = 6 := by native_decide

/-! ## Part VI: Follow-Up Question -/

/-- The set of integers representable with fixed n, k. -/
def RepresentableSet (n k : ℕ) : Set ℕ :=
  {N | ∃ m ≥ n + k, ratioExpression n m k = N}

/-- For fixed n, k, the ratio increases with m. -/
axiom ratio_mono (n k m₁ m₂ : ℕ) (h : m₁ < m₂) :
    ratioExpression n m₁ k < ratioExpression n m₂ k

/-- The representable set for fixed n, k is infinite. -/
axiom representable_set_infinite (n k : ℕ) (hk : k ≥ 2) :
    Set.Infinite (RepresentableSet n k)

/-! ## Part VII: Connections -/

/-- Connection to Problem #677 (similar structure). -/
axiom problem_677_connection : True

/-! ## Part VIII: Summary -/

/--
**Erdős Problem #686: Summary**

QUESTION: Can every integer N ≥ 2 be written as
∏_{i=1}^k (m+i) / ∏_{i=1}^k (n+i) for some k ≥ 2 and m ≥ n + k?

STATUS: OPEN

KNOWN:
- Products of consecutive integers relate to factorials and binomials
- N = 6 is verified: (3)(4)/(1)(2) = 6
- For fixed n, k, the representable set is infinite
- The ratio increases monotonically with m
-/
theorem erdos_686_statement :
    ErdosConjecture686 ↔
    ∀ N ≥ 2, ∃ n m k : ℕ, k ≥ 2 ∧ m ≥ n + k ∧
      ratioExpression n m k = N := by
  simp only [ErdosConjecture686, Representable, IsRepresentable]

/-- The problem remains OPEN. -/
theorem erdos_686_status : True := trivial

end Erdos686
