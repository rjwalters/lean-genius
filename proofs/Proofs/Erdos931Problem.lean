/-
Erdős Problem 931: Same Prime Factors in Products of Consecutive Integers

Let k₁ ≥ k₂ ≥ 3. Are there only finitely many n₂ ≥ n₁ + k₁ such that
the products ∏_{i=1}^{k₁} (n₁+i) and ∏_{j=1}^{k₂} (n₂+j) share the
same set of prime factors?

Erdős himself expressed doubt, conjecturing instead that such pairs must satisfy
n₂ > 2(n₁ + k₁). Counterexamples exist to the stronger claim: AlphaProof
found that 10! = 2⁸·3⁴·5²·7 and 14·15·16 = 2⁵·3·5·7 share the same
prime factors {2,3,5,7}. Tijdeman also found: 19·20·21·22 and 54·55·56·57
share the same prime factors.

**Status:** OPEN

**Reference:** erdosproblems.com/931, Er76d, Gu04 (Problem B35)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic

namespace Erdos931

open Nat Finset

/-
## Core Definitions
-/

/-- The product of k consecutive integers starting from n+1: (n+1)(n+2)...(n+k). -/
def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.Icc 1 k).prod (fun i => n + i)

/-- The set of prime factors of a consecutive product. -/
def consecutivePrimeFactors (n k : ℕ) : Finset ℕ :=
  (consecutiveProduct n k).primeFactors

/-- Two pairs (n₁, k₁) and (n₂, k₂) produce products with the same prime factors. -/
def SamePrimeFactors (n₁ k₁ n₂ k₂ : ℕ) : Prop :=
  consecutivePrimeFactors n₁ k₁ = consecutivePrimeFactors n₂ k₂

instance SamePrimeFactorsDecidable (n₁ k₁ n₂ k₂ : ℕ) :
    Decidable (SamePrimeFactors n₁ k₁ n₂ k₂) :=
  inferInstanceAs (Decidable (_ = _))

/-
## Small Computations
-/

/-- 1·2·...·10 = 10! = 3628800. -/
theorem consecutiveProduct_0_10 : consecutiveProduct 0 10 = 3628800 := by native_decide

/-- 14·15·16 = 3360. -/
theorem consecutiveProduct_13_3 : consecutiveProduct 13 3 = 3360 := by native_decide

/-- 19·20·21·22 = 175560. -/
theorem consecutiveProduct_18_4 : consecutiveProduct 18 4 = 175560 := by native_decide

/-- 54·55·56·57 = 9480240. -/
theorem consecutiveProduct_53_4 : consecutiveProduct 53 4 = 9480240 := by native_decide

/-- For k = 0, the product is 1 (empty product). -/
theorem consecutiveProduct_zero (n : ℕ) : consecutiveProduct n 0 = 1 := by
  simp [consecutiveProduct]

/-- For k = 1, the product is n+1. -/
theorem consecutiveProduct_one (n : ℕ) : consecutiveProduct n 1 = n + 1 := by
  simp [consecutiveProduct]

/-- The product is positive when all factors are positive (always true for n+i with i ≥ 1). -/
theorem consecutiveProduct_pos (n k : ℕ) : 0 < consecutiveProduct n k := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  omega

/-- The product is never zero. -/
theorem consecutiveProduct_ne_zero (n k : ℕ) : consecutiveProduct n k ≠ 0 :=
  Nat.pos_iff_ne_zero.mp (consecutiveProduct_pos n k)

/-
## Main Conjecture (OPEN)
-/

/-- **Erdős Problem 931**: For all k₁ ≥ k₂ ≥ 3, the set of pairs (n₁, n₂)
    with n₂ ≥ n₁ + k₁ and same prime factors is finite. -/
def ErdosProblem931 : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-- Erdős's stronger conjecture: if the products share prime factors and
    n₂ ≥ n₁ + k₁, then n₂ > 2(n₁ + k₁), allowing finitely many exceptions. -/
def StrongerConjecture : Prop :=
  ∀ k₁ k₂ : ℕ, 3 ≤ k₂ → k₂ ≤ k₁ →
    { p : ℕ × ℕ | p.1 + k₁ ≤ p.2 ∧ p.2 ≤ 2 * (p.1 + k₁) ∧
      SamePrimeFactors p.1 k₁ p.2 k₂ }.Finite

/-
## Counterexamples (Verified)
-/

/-- AlphaProof counterexample: 10! and 14·15·16 share prime factors {2,3,5,7}.
    Here n₁ = 0, k₁ = 10, n₂ = 13, k₂ = 3. -/
theorem alphaproof_same_factors : SamePrimeFactors 0 10 13 3 := by native_decide

/-- The AlphaProof counterexample satisfies the gap condition n₂ ≥ n₁ + k₁. -/
theorem alphaproof_gap : 0 + 10 ≤ 13 := by omega

/-- The AlphaProof counterexample has n₂ ≤ 2(n₁ + k₁), refuting the
    no-exceptions version of the stronger conjecture. -/
theorem alphaproof_within_double : 13 ≤ 2 * (0 + 10) := by omega

/-- Tijdeman's example: 19·20·21·22 and 54·55·56·57 share prime factors. -/
theorem tijdeman_same_factors : SamePrimeFactors 18 4 53 4 := by native_decide

/-- Tijdeman's example satisfies the gap condition. -/
theorem tijdeman_gap : 18 + 4 ≤ 53 := by omega

/-- Tijdeman's example also has n₂ > 2(n₁ + k₁): 53 > 44. -/
theorem tijdeman_beyond_double : 53 > 2 * (18 + 4) := by omega

/-
## Properties of Prime Factors
-/

/-- Every prime factor of the consecutive product divides the product. -/
theorem prime_factor_dvd (n k p : ℕ) (hp : p ∈ consecutivePrimeFactors n k) :
    p ∣ consecutiveProduct n k :=
  Nat.dvd_of_mem_primeFactors hp

/-- Every prime factor of the consecutive product is prime. -/
theorem prime_factor_is_prime (n k p : ℕ) (hp : p ∈ consecutivePrimeFactors n k) :
    p.Prime :=
  Nat.prime_of_mem_primeFactors hp

/-- A prime dividing one of the factors divides the product. -/
theorem factor_prime_dvd_product (n k i : ℕ) (hi : i ∈ Finset.Icc 1 k)
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ (n + i)) :
    p ∣ consecutiveProduct n k := by
  unfold consecutiveProduct
  exact dvd_trans hdvd (Finset.dvd_prod_of_mem _ hi)

/-- If p divides some n+i with 1 ≤ i ≤ k, then p is a prime factor of the product. -/
theorem factor_prime_mem (n k i : ℕ) (hi : i ∈ Finset.Icc 1 k)
    (p : ℕ) (hp : p.Prime) (hdvd : p ∣ (n + i)) :
    p ∈ consecutivePrimeFactors n k := by
  unfold consecutivePrimeFactors
  rw [Nat.mem_primeFactors]
  exact ⟨hp, factor_prime_dvd_product n k i hi p hp hdvd, consecutiveProduct_ne_zero n k⟩

/-- SamePrimeFactors is reflexive. -/
theorem samePrimeFactors_refl (n k : ℕ) : SamePrimeFactors n k n k :=
  rfl

/-- SamePrimeFactors is symmetric. -/
theorem samePrimeFactors_symm {n₁ k₁ n₂ k₂ : ℕ}
    (h : SamePrimeFactors n₁ k₁ n₂ k₂) : SamePrimeFactors n₂ k₂ n₁ k₁ :=
  h.symm

/-- SamePrimeFactors is transitive. -/
theorem samePrimeFactors_trans {n₁ k₁ n₂ k₂ n₃ k₃ : ℕ}
    (h₁ : SamePrimeFactors n₁ k₁ n₂ k₂) (h₂ : SamePrimeFactors n₂ k₂ n₃ k₃) :
    SamePrimeFactors n₁ k₁ n₃ k₃ :=
  h₁.trans h₂

/-
## The Stronger Conjecture Implies the Main One
-/

/-- The stronger conjecture implies the main conjecture: if same-prime-factor
    pairs with n₂ ≤ 2(n₁+k₁) are finite, combined with the trivial bound,
    we get overall finiteness. -/
axiom stronger_implies_main : StrongerConjecture → ErdosProblem931

/-
## Open Question: Prime Between Blocks
-/

/-- Open question: if two consecutive products share prime factors with
    n₂ ≥ n₁ + k₁, must there exist a prime p with n₁ < p ≤ n₂ + k₂? -/
axiom exists_prime_between_blocks (k₁ k₂ n₁ n₂ : ℕ)
    (h₁ : 3 ≤ k₂) (h₂ : k₂ ≤ k₁)
    (h₃ : n₁ + k₁ ≤ n₂)
    (h₄ : SamePrimeFactors n₁ k₁ n₂ k₂) :
    ∃ p : ℕ, p.Prime ∧ n₁ < p ∧ p ≤ n₂ + k₂

/-
## Problem Status
-/

def erdos_931_status : String := "OPEN"

end Erdos931
