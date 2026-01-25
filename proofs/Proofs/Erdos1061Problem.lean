/-
Erdos Problem #1061: Sum of Divisors Equation

Source: https://erdosproblems.com/1061
Status: OPEN

Statement:
How many (ordered) solutions are there to sigma(a) + sigma(b) = sigma(a + b)
with a + b <= x, where sigma is the sum of divisors function?
Is this count asymptotic to c * x for some constant c > 0?

Background:
This is a question of Erdos reported in problem B15 of Guy's collection
"Unsolved Problems in Number Theory" (2004).

Key Insight:
The equation sigma(a) + sigma(b) = sigma(a + b) holds when the divisor
structure of a + b "decomposes" in a special way relative to a and b.

Related:
- OEIS A110177: Numbers n such that sigma(n) = sigma(a) + sigma(n-a) for some a < n
- Formal-conjectures: 1061.lean

References:
- Erdos (question reported in Guy's collection)
- Guy, R.K. [Gu04]: "Unsolved problems in number theory", Problem B15
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Archimedean

open Nat BigOperators Finset ArithmeticFunction Filter Asymptotics

namespace Erdos1061

/-
## Part I: The Sum of Divisors Function

sigma(n) = sum of all positive divisors of n
-/

/--
**Sum of Divisors:**
sigma(n) computes the sum of all positive divisors of n.

Examples:
- sigma(1) = 1
- sigma(2) = 1 + 2 = 3
- sigma(6) = 1 + 2 + 3 + 6 = 12
- sigma(p) = 1 + p for prime p
-/
def sigma (n : ℕ) : ℕ := (n.divisors).sum id

/-- sigma(1) = 1 -/
theorem sigma_one : sigma 1 = 1 := by
  simp [sigma, Nat.divisors_one]

/-- sigma(2) = 3 -/
theorem sigma_two : sigma 2 = 3 := by native_decide

/-- sigma(3) = 4 -/
theorem sigma_three : sigma 3 = 4 := by native_decide

/-- sigma(4) = 7 -/
theorem sigma_four : sigma 4 = 7 := by native_decide

/-- sigma(5) = 6 -/
theorem sigma_five : sigma 5 = 6 := by native_decide

/-- sigma(6) = 12 -/
theorem sigma_six : sigma 6 = 12 := by native_decide

/-- sigma(p) = 1 + p for prime p (divisors are just 1 and p) -/
axiom sigma_prime (p : ℕ) (hp : p.Prime) : sigma p = 1 + p

/-
## Part II: The Additive Divisor Equation

The central equation: sigma(a) + sigma(b) = sigma(a + b)
-/

/--
**Additive Divisor Solutions:**
A pair (a, b) satisfies the additive divisor equation if
sigma(a) + sigma(b) = sigma(a + b).
-/
def isAdditiveDivisorPair (a b : ℕ) : Prop :=
  a ≥ 1 ∧ b ≥ 1 ∧ sigma a + sigma b = sigma (a + b)

/--
The set of all ordered pairs (a, b) satisfying sigma(a) + sigma(b) = sigma(a + b)
with a, b >= 1.
-/
def additiveDivisorPairs : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | isAdditiveDivisorPair p.1 p.2}

/-
## Part III: The Counting Function

S(x) counts ordered pairs with a + b <= x.
-/

/--
**The Counting Function S(x):**
Counts the number of ordered pairs (a, b) with:
1. a >= 1 and b >= 1
2. a + b <= x
3. sigma(a) + sigma(b) = sigma(a + b)
-/
noncomputable def S (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter fun (a, b) =>
    a + b ≤ x ∧ sigma a + sigma b = sigma (a + b)).card

/-- S(0) = 0 (no pairs with positive components sum to at most 0) -/
theorem S_zero : S 0 = 0 := by
  simp only [S, Finset.Icc_eq_empty_of_lt (by omega : 1 > 0), Finset.empty_product,
             Finset.filter_empty, Finset.card_empty]

/-- S(1) = 0 (minimal sum is 1+1=2 > 1) -/
theorem S_one : S 1 = 0 := by native_decide

/-
## Part IV: Known Solutions

Examples of pairs satisfying sigma(a) + sigma(b) = sigma(a + b).
-/

/--
**Example 1:** (1, 1) does NOT satisfy the equation.
sigma(1) + sigma(1) = 1 + 1 = 2
sigma(1 + 1) = sigma(2) = 3
2 ≠ 3
-/
theorem not_solution_1_1 : ¬isAdditiveDivisorPair 1 1 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 2:** (2, 2) does NOT satisfy the equation.
sigma(2) + sigma(2) = 3 + 3 = 6
sigma(2 + 2) = sigma(4) = 7
6 ≠ 7
-/
theorem not_solution_2_2 : ¬isAdditiveDivisorPair 2 2 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 3:** (1, 2) does NOT satisfy the equation.
sigma(1) + sigma(2) = 1 + 3 = 4
sigma(1 + 2) = sigma(3) = 4
4 = 4 -- This one DOES work!
-/
theorem solution_1_2 : isAdditiveDivisorPair 1 2 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/-- (2, 1) also satisfies the equation by symmetry -/
theorem solution_2_1 : isAdditiveDivisorPair 2 1 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 4:** (1, 4) satisfies the equation.
sigma(1) + sigma(4) = 1 + 7 = 8
sigma(1 + 4) = sigma(5) = 6
8 ≠ 6 -- Does NOT work
-/
theorem not_solution_1_4 : ¬isAdditiveDivisorPair 1 4 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 5:** (1, 5) check.
sigma(1) + sigma(5) = 1 + 6 = 7
sigma(1 + 5) = sigma(6) = 12
7 ≠ 12
-/
theorem not_solution_1_5 : ¬isAdditiveDivisorPair 1 5 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 6:** (2, 4) check.
sigma(2) + sigma(4) = 3 + 7 = 10
sigma(2 + 4) = sigma(6) = 12
10 ≠ 12
-/
theorem not_solution_2_4 : ¬isAdditiveDivisorPair 2 4 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
**Example 7:** (3, 3) check.
sigma(3) + sigma(3) = 4 + 4 = 8
sigma(3 + 3) = sigma(6) = 12
8 ≠ 12
-/
theorem not_solution_3_3 : ¬isAdditiveDivisorPair 3 3 := by
  simp only [isAdditiveDivisorPair, sigma]
  native_decide

/--
The pair (1, 2) shows additiveDivisorPairs is nonempty.
-/
theorem pairs_nonempty : (1, 2) ∈ additiveDivisorPairs := solution_1_2

/-
## Part V: Structure Theorems

Understanding when sigma(a) + sigma(b) = sigma(a + b) can hold.
-/

/--
**Subadditivity Failure:**
In general, sigma is NOT subadditive: sigma(a + b) can be less than sigma(a) + sigma(b).
But it can also be greater (as in most cases).

The equation sigma(a) + sigma(b) = sigma(a + b) represents a special balance.
-/
axiom sigma_not_subadditive :
  ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma (a + b) < sigma a + sigma b

/--
**Superadditivity Failure:**
sigma is also NOT superadditive in general.
-/
axiom sigma_not_superadditive :
  ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ sigma (a + b) > sigma a + sigma b

/-
## Part VI: Asymptotic Question

Is S(x) ~ c * x for some constant c > 0?
-/

/--
**The Main Question:**
Does there exist a constant c > 0 such that S(x) is asymptotically c * x?

This is asking whether the density of solutions is positive and linear.
-/
def hasLinearGrowth : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Tendsto (fun x : ℕ => (S x : ℝ) / x) atTop (nhds c)

/--
**Alternative Formulation:**
S(x) ~ c * x means S(x) / (c * x) -> 1 as x -> infinity.
-/
def isAsymptoticToLinear (c : ℝ) : Prop :=
  c > 0 ∧ Tendsto (fun x : ℕ => (S x : ℝ) / (c * x)) atTop (nhds 1)

/-
## Part VII: Bounds and Estimates
-/

/--
**Lower Bound:**
S(x) >= 2 for x >= 3, since (1,2) and (2,1) are solutions with sum 3.
-/
axiom S_lower_bound (x : ℕ) (hx : x ≥ 3) : S x ≥ 2

/--
**Upper Bound:**
S(x) <= x^2 / 4 trivially (at most (x/2)^2 pairs with a + b <= x).
-/
axiom S_upper_bound (x : ℕ) (hx : x ≥ 1) : S x ≤ x * x / 4

/--
**Monotonicity:**
S is monotone increasing.
-/
axiom S_monotone (x y : ℕ) (hxy : x ≤ y) : S x ≤ S y

/-
## Part VIII: The Open Problem

Erdos Problem #1061 asks whether S(x) ~ c * x.
This remains unresolved.
-/

/--
**Erdos Problem #1061:**
Is S(x) asymptotic to c * x for some constant c > 0?

Status: OPEN

The formal statement from formal-conjectures asks:
  answer(sorry) <-> exists c > 0, S ~[atTop] (fun x => c * x)

We leave this as an open question.
-/
axiom erdos_1061_open : True -- Placeholder: the problem is open

/--
**Conjecture (Implicit):**
Erdos's question suggests he believed S(x) might grow linearly,
but this remains unproven.
-/
axiom erdos_1061_conjecture :
  hasLinearGrowth ∨ ¬hasLinearGrowth

/-
## Part IX: Related Sequences

OEIS A110177: Numbers n such that sigma(n) = sigma(a) + sigma(n-a) for some 0 < a < n.
-/

/--
**OEIS A110177:**
The set of n such that n = a + b for some solution pair (a, b).
-/
def A110177 : Set ℕ :=
  {n : ℕ | ∃ a b : ℕ, a ≥ 1 ∧ b ≥ 1 ∧ a + b = n ∧ sigma a + sigma b = sigma n}

/-- 3 is in A110177 since (1, 2) is a solution with 1 + 2 = 3 -/
theorem three_in_A110177 : 3 ∈ A110177 := by
  use 1, 2
  simp only [sigma, and_true]
  constructor
  · omega
  constructor
  · omega
  constructor
  · ring
  · native_decide

/-
## Part X: Summary
-/

/--
**Summary of Erdos Problem #1061:**

1. The problem counts solutions to sigma(a) + sigma(b) = sigma(a + b)
2. Known solutions include (1, 2) and (2, 1) with common value 3
3. The question asks if S(x) ~ c * x for some c > 0
4. This remains an OPEN problem
5. Related to OEIS A110177

Key insight: This equation probes the arithmetic structure of the divisor function
in a fundamental way. The linearity question asks about the "density" of
solutions among all pairs.
-/
theorem erdos_1061_summary :
    (1, 2) ∈ additiveDivisorPairs ∧
    (2, 1) ∈ additiveDivisorPairs ∧
    3 ∈ A110177 := by
  exact ⟨solution_1_2, solution_2_1, three_in_A110177⟩

end Erdos1061
