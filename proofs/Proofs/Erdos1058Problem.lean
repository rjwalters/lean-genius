/-
Erdős Problem #1058: Prime Divisors of n!+1 Between Consecutive Primes

Source: https://erdosproblems.com/1058
Status: SOLVED (Luca 2001)

Statement:
Let 2 = p₁ < p₂ < ... be the sequence of primes. Are there only
finitely many n such that n ∈ [p_{k-1}, p_k) and the only primes
dividing n!+1 are p_k and p_{k+1}?

Resolution:
Luca [Lu01] proved that n = 1, 2, 3, 4, 5 are the only solutions.

Historical Note:
A conjecture of Erdős and Stewart, as reported in problem A2 of
Guy's collection [Gu04]. The problem connects factorials, consecutive
primes, and divisibility in a subtle way.

References:
- Erdős-Stewart: Original conjecture
- Guy [Gu04]: Problem A2, Unsolved Problems in Number Theory
- Luca [Lu01]: Complete solution (Math. Comp.)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace Erdos1058

/-
## Part I: Prime Sequence Definitions
-/

/--
**The prime sequence:**
p₁ = 2, p₂ = 3, p₃ = 5, p₄ = 7, ...
The n-th prime number.
-/
axiom prime_seq : ℕ → ℕ

/--
**Basic properties of the prime sequence:**
p₁ = 2, and pₙ₊₁ > pₙ for all n.
-/
/--
**First few primes:**
p₁ = 2, p₂ = 3, p₃ = 5, p₄ = 7, p₅ = 11.
-/
/-
## Part II: The Problem Statement
-/

/--
**The interval condition:**
n ∈ [p_{k-1}, p_k) means p_{k-1} ≤ n < p_k.
-/
def inPrimeInterval (n k : ℕ) : Prop :=
  prime_seq (k - 1) ≤ n ∧ n < prime_seq k

/--
**The divisibility condition:**
The only primes dividing n!+1 are p_k and p_{k+1}.
-/
def onlyTwoPrimesDivide (n k : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ (n.factorial + 1) →
    (p = prime_seq k ∨ p = prime_seq (k + 1))

/--
**The Erdős-Stewart condition:**
n satisfies the condition if it's in [p_{k-1}, p_k) and
n!+1 is only divisible by p_k and p_{k+1}.
-/
def satisfiesCondition (n : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 2 ∧ inPrimeInterval n k ∧ onlyTwoPrimesDivide n k

/-
## Part III: The Conjecture and its Resolution
-/

/--
**Erdős-Stewart Conjecture:**
There are only finitely many n satisfying the condition.
-/
def erdos_stewart_conjecture : Prop :=
  ∃ S : Finset ℕ, ∀ n : ℕ, satisfiesCondition n → n ∈ S

/-- The conjecture is TRUE: Luca proved this in 2001. -/
axiom erdos_stewart_conjecture_true : erdos_stewart_conjecture

/-
## Part IV: The Complete Classification
-/

/--
**Luca's Theorem (2001):**
The only n satisfying the Erdős-Stewart condition are n = 1, 2, 3, 4, 5.
-/
axiom luca_theorem :
    ∀ n : ℕ, satisfiesCondition n ↔ n ∈ ({1, 2, 3, 4, 5} : Finset ℕ)

/-
## Part V: Verification of Known Cases
-/

/-- n = 1: 1! + 1 = 2 = 2¹. The only prime factor is 2. -/
example : (1 : ℕ).factorial + 1 = 2 := by norm_num

/-- n = 2: 2! + 1 = 3 = 3¹. The only prime factor is 3. -/
example : (2 : ℕ).factorial + 1 = 3 := by norm_num

/-- n = 3: 3! + 1 = 7 = 7¹. The only prime factor is 7. -/
example : (3 : ℕ).factorial + 1 = 7 := by norm_num

/-- n = 4: 4! + 1 = 25 = 5². The only prime factor is 5. -/
example : (4 : ℕ).factorial + 1 = 25 := by norm_num

/-- n = 5: 5! + 1 = 121 = 11². The only prime factor is 11. -/
example : (5 : ℕ).factorial + 1 = 121 := by norm_num

/-- n = 6: 6! + 1 = 721 = 7 × 103. Has extra prime factor 103 > p₅ = 11. -/
example : (6 : ℕ).factorial + 1 = 721 := by norm_num

/-
## Part VI: Summary
-/

/--
**Summary of Erdős Problem #1058:**

PROBLEM: Let 2 = p₁ < p₂ < ... be the primes. Are there only
finitely many n with n ∈ [p_{k-1}, p_k) such that the only primes
dividing n!+1 are p_k and p_{k+1}?

STATUS: SOLVED (Luca 2001)

ANSWER: YES. The only solutions are n = 1, 2, 3, 4, 5.

VERIFICATION:
- 1! + 1 = 2 = 2¹
- 2! + 1 = 3 = 3¹
- 3! + 1 = 7 = 7¹
- 4! + 1 = 25 = 5²
- 5! + 1 = 121 = 11²

KEY INSIGHTS:
1. Factorial growth eventually forces many prime factors
2. Wilson's theorem ensures p_k divides (p_k - 1)! + 1
3. For n ≥ 6, n!+1 is too large to be a pure prime power
4. Diophantine methods eliminate all larger cases
-/
theorem erdos_1058_status :
    -- There are only finitely many solutions
    erdos_stewart_conjecture ∧
    -- The complete list is {1, 2, 3, 4, 5}
    (∀ n : ℕ, satisfiesCondition n ↔ n ∈ ({1, 2, 3, 4, 5} : Finset ℕ)) := by
  constructor
  · exact erdos_stewart_conjecture_true
  · exact luca_theorem

/-- Erdős Problem #1058 was completely solved by Luca in 2001. -/
theorem erdos_1058_solved : erdos_stewart_conjecture := erdos_stewart_conjecture_true

end Erdos1058
