/-!
# Erdős Problem 931: Same Prime Factors in Products of Consecutive Integers

*Reference:* [erdosproblems.com/931](https://www.erdosproblems.com/931)

Let `k₁ ≥ k₂ ≥ 3`. Are there only finitely many `n₂ ≥ n₁ + k₁` such that
the products `∏_{i=1}^{k₁} (n₁+i)` and `∏_{j=1}^{k₂} (n₂+j)` share the
same set of prime factors?

Erdős himself expressed doubt, conjecturing instead that such pairs must satisfy
`n₂ > 2(n₁ + k₁)`. Counterexamples exist to the stronger claim: AlphaProof
found that `10! = 2⁸·3⁴·5²·7` and `14·15·16 = 2⁵·3·5·7` share the same
prime factors {2,3,5,7}. Tijdeman also found: `19·20·21·22` and `54·55·56·57`
share the same prime factors.

This remains an open problem.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

/-!
## Section 1: Product prime factors

We define the prime factor set of a product of consecutive integers.
-/

namespace Erdos931

open Nat Finset

/-- The product of k consecutive integers starting from n+1: (n+1)(n+2)⋯(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.Icc 1 k).prod (fun i => n + i)

/-- The set of prime factors of a consecutive product. -/
def consecutivePrimeFactors (n k : ℕ) : Finset ℕ :=
  (consecutiveProduct n k).primeFactors

/-!
## Section 2: Same prime factors property

Two blocks of consecutive integers have the same prime factors if their
products share the same prime factor set.
-/

/-- Two pairs (n₁, k₁) and (n₂, k₂) produce products with the same prime factors. -/
def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  consecutivePrimeFactors n₁ k₁ = consecutivePrimeFactors n₂ k₂

/-!
## Section 3: The main conjecture

Erdős Problem 931: for fixed k₁ ≥ k₂ ≥ 3, are there only finitely many
pairs (n₁, n₂) with n₂ ≥ n₁ + k₁ and same prime factors?
-/

/-- Erdős Problem 931: For all k₁ ≥ k₂ ≥ 3, the set of pairs (n₁, n₂)
    with n₂ ≥ n₁ + k₁ and same prime factors is finite. -/
def ErdosProblem931 : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-!
## Section 4: The stronger conjecture (n₂ > 2(n₁ + k₁))

Erdős conjectured that when the products have the same factors, we must have
n₂ > 2(n₁ + k₁). This is stronger than finiteness.
-/

/-- Erdős's stronger conjecture: if the products share prime factors and
    n₂ ≥ n₁ + k₁, then n₂ > 2(n₁ + k₁), allowing finitely many exceptions. -/
def StrongerConjecture : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧ p.2 ≤ 2 * (p.1 + k₁) ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-!
## Section 5: AlphaProof counterexample

AlphaProof found: 10! and 14·15·16 share prime factors {2,3,5,7}.
Equivalently, n₁ = 0, k₁ = 10, n₂ = 13, k₂ = 3 gives a counterexample
to the claim that there are NO such pairs with n₂ ≤ 2(n₁ + k₁).
-/

/-- AlphaProof counterexample: products (1·2···10) and (14·15·16) share
    the same prime factors {2,3,5,7}, with n₂ = 13 ≤ 2·(0+10) = 20. -/
axiom alphaproof_counterexample :
  SamePrimeFactors 0 10 13 3 ∧ 0 + 10 ≤ 13 ∧ 13 ≤ 2 * (0 + 10)

/-!
## Section 6: Tijdeman's example

Tijdeman found: 19·20·21·22 and 54·55·56·57 share the same prime factors.
Here n₁ = 18, k₁ = 4, n₂ = 53, k₂ = 4.
-/

/-- Tijdeman's example: 19·20·21·22 and 54·55·56·57 share prime factors. -/
axiom tijdeman_example :
  SamePrimeFactors 18 4 53 4

/-!
## Section 7: Prime between n₁ and n₂

Erdős was unable to prove that if the two products have the same prime factors,
then there must exist a prime between n₁ and n₂.
-/

/-- Open question: if two consecutive products share prime factors with
    n₂ ≥ n₁ + k₁, must there exist a prime p with n₁ ≤ p ≤ n₂? -/
axiom exists_prime_between (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ ≤ p ∧ p ≤ n₂

end Erdos931
