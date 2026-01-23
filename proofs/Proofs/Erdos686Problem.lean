/-
Erdős Problem #686: Ratios of Consecutive Products

**Question**: Can every integer N ≥ 2 be written as
  N = ∏_{1 ≤ i ≤ k}(m+i) / ∏_{1 ≤ i ≤ k}(n+i)
for some k ≥ 2 and m ≥ n + k?

**Equivalent Form**: Can every N ≥ 2 be expressed as
  N = (m+k)!/(m)! / ((n+k)!/(n)!) = C(m+k, k) / C(n+k, k)
where C denotes binomial coefficients?

**Status**: OPEN - The answer is unknown.

**Context**: This asks whether ratios of products of k consecutive integers
(with appropriate gaps) can represent all integers ≥ 2.

**Secondary Question**: If n and k are fixed, what integers can be represented?

**Related Problem**: Erdős #677 asks about when M(n,k) = M(m,k) where
M(n,k) = lcm(n+1, ..., n+k). The Thue-Siegel theorem implies finiteness.

References:
- https://erdosproblems.com/686
- https://erdosproblems.com/677
- [Er79d] Erdős, "Some unconventional problems in number theory" (1979)
-/

import Mathlib

namespace Erdos686

open Nat BigOperators

/-
## Products of Consecutive Integers

The product (n+1)(n+2)⋯(n+k) = (n+k)!/n!
-/

/--
The product of k consecutive integers starting from n+1.
That is, (n+1)(n+2)⋯(n+k).
-/
def consecutiveProduct (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i + 1)

/--
Alternative: using factorials.
(n+1)(n+2)⋯(n+k) = (n+k)!/n!
-/
theorem consecutiveProduct_eq_factorial (n k : ℕ) :
    consecutiveProduct n k = (n + k)! / n! := by
  sorry

/--
Another form: this equals k! times a binomial coefficient.
(n+1)⋯(n+k) = k! · C(n+k, k)
-/
theorem consecutiveProduct_eq_choose (n k : ℕ) :
    consecutiveProduct n k = k! * Nat.choose (n + k) k := by
  -- By definition of binomial coefficient
  sorry

/-
## The Ratio

For m ≥ n + k, the ratio is an integer.
-/

/--
The ratio of two consecutive products.
-/
def productRatio (m n k : ℕ) : ℚ :=
  consecutiveProduct m k / consecutiveProduct n k

/--
When m ≥ n + k, the numerator product dominates and the ratio is ≥ 1.
-/
theorem productRatio_ge_one (m n k : ℕ) (hmn : m ≥ n + k) :
    productRatio m n k ≥ 1 := by
  sorry

/--
The condition for the ratio to be an integer.
-/
def isIntegerRatio (m n k : ℕ) : Prop :=
  (consecutiveProduct n k) ∣ (consecutiveProduct m k)

/-
## The Main Question

Can every N ≥ 2 be represented as such a ratio?
-/

/--
A representation of N as a ratio of consecutive products.
-/
structure Representation (N : ℕ) where
  /-- The length of the products -/
  k : ℕ
  /-- The lower start -/
  n : ℕ
  /-- The upper start -/
  m : ℕ
  /-- k ≥ 2 -/
  hk : k ≥ 2
  /-- m ≥ n + k (products are disjoint) -/
  hmn : m ≥ n + k
  /-- The ratio equals N -/
  eq_N : consecutiveProduct m k = N * consecutiveProduct n k

/--
**Erdős Problem #686 (OPEN)**: Every integer N ≥ 2 can be represented
as a ratio of products of k consecutive integers for some k ≥ 2.
-/
def erdos_686_conjecture : Prop :=
  ∀ N : ℕ, N ≥ 2 → Nonempty (Representation N)

/-
## Examples

Let's verify some small cases.
-/

/--
For k = 2: (m+1)(m+2) / (n+1)(n+2) = N
Need (n+1)(n+2) | (m+1)(m+2) and quotient = N.
-/

/-- consecutiveProduct n 2 = (n+1)(n+2) -/
theorem consecutiveProduct_two (n : ℕ) :
    consecutiveProduct n 2 = (n + 1) * (n + 2) := by
  simp [consecutiveProduct, Finset.prod_range_succ]
  ring

/--
Example: N = 6 can be represented.
(2+1)(2+2) / (0+1)(0+2) = 12/2 = 6.
So m = 2, n = 0, k = 2.
-/
theorem six_representable : Nonempty (Representation 6) := by
  refine ⟨⟨2, 0, 2, by norm_num, by norm_num, ?_⟩⟩
  simp only [consecutiveProduct_two]
  norm_num

/--
Example: N = 10 can be represented.
(4+1)(4+2) = 30, (1+1)(1+2) = 6, 30/6 = 5 ≠ 10.
Try k = 3: (m+1)(m+2)(m+3) / (n+1)(n+2)(n+3).
-/

/-- consecutiveProduct n 3 = (n+1)(n+2)(n+3) -/
theorem consecutiveProduct_three (n : ℕ) :
    consecutiveProduct n 3 = (n + 1) * (n + 2) * (n + 3) := by
  simp [consecutiveProduct, Finset.prod_range_succ]
  ring

/-
## Secondary Question: Fixed n and k

What integers can be represented with fixed n and k?
-/

/--
The set of integers representable with fixed n and k.
-/
def representableSet (n k : ℕ) : Set ℕ :=
  {N : ℕ | ∃ m ≥ n + k, consecutiveProduct m k = N * consecutiveProduct n k}

/--
For fixed n and k, the representable set is a subset of positive ratios
of binomial coefficients.
-/
theorem representableSet_binomial (n k : ℕ) (hk : k ≥ 1) :
    representableSet n k =
      {N : ℕ | ∃ m ≥ n + k, Nat.choose (m + k) k = N * Nat.choose (n + k) k} := by
  -- Use consecutiveProduct_eq_choose
  sorry

/-
## Connection to Problem 677

Problem 677 asks about M(n,k) = lcm(n+1, ..., n+k).
The products here are ∏(n+i) which divides M(n,k)^k.

The connection: if M(n,k) = M(m,k) (same lcm), what can we say about
the product ratio?
-/

/--
The lcm of k consecutive integers starting from n+1.
-/
def consecutiveLcm (n k : ℕ) : ℕ :=
  (Finset.range k).lcm (fun i => n + i + 1)

/--
The product divides the lcm raised to the power k.
-/
theorem consecutiveProduct_dvd_lcm_pow (n k : ℕ) :
    consecutiveProduct n k ∣ consecutiveLcm n k ^ k := by
  -- Each factor divides the lcm
  sorry

/-
## Observations

The problem has an interesting structure:
1. The ratio is always rational, but is it always an integer for some m, n, k?
2. The constraint m ≥ n + k ensures the products are "disjoint"
3. For fixed k, the possible N's grow with m

Key insight: The ratio equals
  C(m+k, k) / C(n+k, k)
which is the ratio of two binomial coefficients with the same lower parameter.
-/

/--
The ratio in terms of binomial coefficients.
-/
theorem productRatio_choose (m n k : ℕ) (hk : k ≥ 1) :
    productRatio m n k = (Nat.choose (m + k) k : ℚ) / (Nat.choose (n + k) k : ℚ) := by
  sorry

/-
## Summary

Erdős Problem #686 asks whether every integer N ≥ 2 can be expressed as
a ratio of products of k consecutive integers.

**Formalized**:
- `consecutiveProduct n k` = (n+1)(n+2)⋯(n+k)
- `Representation N` = proof that N is such a ratio
- `erdos_686_conjecture` = ∀ N ≥ 2, Nonempty (Representation N)

**Status**: OPEN
- Small cases can be verified computationally
- General existence is unknown
- Connection to binomial coefficient ratios

**Approach Ideas**:
1. Systematic search for representations of small N
2. Study which primes can appear in such ratios
3. Connect to properties of binomial coefficients
-/

-- Placeholder for main conjecture status
axiom erdos_686 : erdos_686_conjecture

theorem erdos_686_summary : True := trivial

end Erdos686
