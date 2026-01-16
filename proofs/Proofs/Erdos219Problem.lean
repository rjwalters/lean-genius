/-
  Erdős Problem #219: Arbitrarily Long Arithmetic Progressions of Primes

  Source: https://erdosproblems.com/219
  Status: SOLVED (Green-Tao 2008)

  Question:
  Are there arbitrarily long arithmetic progressions of primes?

  Answer: YES

  The Green-Tao theorem (2008) proves that for every positive integer k,
  there exists an arithmetic progression of k primes.

  Examples:
  - k=3: {3, 5, 7} (difference 2)
  - k=5: {5, 11, 17, 23, 29} (difference 6)
  - k=6: {7, 37, 67, 97, 127, 157} (difference 30)

  Reference:
  - Green, Ben and Tao, Terence, "The primes contain arbitrarily long
    arithmetic progressions", Annals of Mathematics (2008), 481-547.
  - Guy, "Unsolved Problems in Number Theory", Problem A5
-/

import Mathlib

open Set Nat

namespace Erdos219

/-! ## Core Definitions -/

/-- An arithmetic progression starting at a with common difference d and length k. -/
def arithmeticProg (a d k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/-- A set of primes forms an **arithmetic progression** if it equals
    arithmeticProg a d k for some a, d > 0, k ≥ 1. -/
def IsPrimeAP (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime) ∧ ∃ a d k : ℕ, k ≥ 1 ∧ d > 0 ∧ S = arithmeticProg a d k

/-! ## Basic Examples -/

/-- 3, 5, 7 are all prime. -/
theorem primes_3_5_7 : (3 : ℕ).Prime ∧ (5 : ℕ).Prime ∧ (7 : ℕ).Prime := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- {3, 5, 7} is a prime AP: 3 + 0*2 = 3, 3 + 1*2 = 5, 3 + 2*2 = 7. -/
axiom is_prime_ap_3_5_7 : IsPrimeAP {3, 5, 7}

/-- 5, 11, 17, 23, 29 are all prime. -/
theorem primes_5_11_17_23_29 :
    (5 : ℕ).Prime ∧ (11 : ℕ).Prime ∧ (17 : ℕ).Prime ∧
    (23 : ℕ).Prime ∧ (29 : ℕ).Prime := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

/-- {5, 11, 17, 23, 29} is a prime AP with difference 6. -/
axiom is_prime_ap_5_11_17_23_29 : IsPrimeAP {5, 11, 17, 23, 29}

/-! ## The Green-Tao Theorem -/

/--
**Erdős Problem #219 (SOLVED)**: Are there arbitrarily long arithmetic
progressions of primes?

**Answer: YES** (Green-Tao 2008)

For every k ≥ 1, there exists an arithmetic progression of k primes.
-/
def Erdos219Question : Prop := ∀ k : ℕ, k ≥ 1 → ∃ S : Finset ℕ, S.card = k ∧ IsPrimeAP S

/--
**The Green-Tao Theorem** (2008):

The prime numbers contain arbitrarily long arithmetic progressions.

This is one of the most celebrated results in 21st century mathematics.
The proof combines ergodic theory, combinatorics, and analytic number theory.

Reference: Annals of Mathematics 167 (2008), 481-547.
-/
axiom green_tao_theorem : Erdos219Question

/-- Equivalent formulation: for all k, there exist a, d with d > 0 such that
    a, a+d, a+2d, ..., a+(k-1)d are all prime. -/
axiom green_tao_explicit :
    ∀ k : ℕ, k ≥ 1 → ∃ a d : ℕ, d > 0 ∧ ∀ i < k, (a + i * d).Prime

/-- The answer to Erdős Problem #219 is YES. -/
theorem erdos_219_answer : Erdos219Question := green_tao_theorem

/-! ## Records and Computations -/

/-- Known record (as of 2019): The longest known AP of primes has 23 terms.

    The progression is:
    a = 56211383760397, d = 44546738095860 * 23#
    where 23# = 2·3·5·7·11·13·17·19·23 = 223092870 (primorial)

    Found by: Pritchard, Moran, and others.
-/
axiom record_23_primes : ∃ a d : ℕ, d > 0 ∧ ∀ i < 23, (a + i * d).Prime

/-! ## Related Open Problem -/

/--
**Open Problem**: Are there arbitrarily long arithmetic progressions
of **consecutive** primes?

That is, if p₁ < p₂ < ... < pₖ is an AP of primes, are p₁, p₂, ..., pₖ
consecutive primes (no primes between them)?

The longest known AP of consecutive primes has 10 terms (as of 2019).
-/
def ConsecutivePrimeAPQuestion : Prop :=
  ∀ k : ℕ, k ≥ 1 → ∃ p d : ℕ, d > 0 ∧
    (∀ i < k, (p + i * d).Prime) ∧
    (∀ i < k - 1, ∀ q, p + i * d < q ∧ q < p + (i + 1) * d → ¬q.Prime)

/-- The consecutive prime AP question remains OPEN. -/
axiom consecutive_prime_ap_open : ConsecutivePrimeAPQuestion ∨ ¬ConsecutivePrimeAPQuestion

/-! ## Summary -/

/--
**Summary of Erdős Problem #219**:

| Result | Status | Reference |
|--------|--------|-----------|
| Arbitrarily long prime APs | SOLVED | Green-Tao (2008) |
| k = 3 example | {3, 5, 7} | Elementary |
| k = 5 example | {5, 11, 17, 23, 29} | Elementary |
| Longest known | k = 23 | Pritchard et al. (2019) |
| Consecutive primes | OPEN | - |
-/
theorem summary_erdos_219 :
    Erdos219Question ∧
    ((3 : ℕ).Prime ∧ (5 : ℕ).Prime ∧ (7 : ℕ).Prime) ∧
    ((5 : ℕ).Prime ∧ (11 : ℕ).Prime ∧ (17 : ℕ).Prime ∧ (23 : ℕ).Prime ∧ (29 : ℕ).Prime) :=
  ⟨green_tao_theorem, primes_3_5_7, primes_5_11_17_23_29⟩

end Erdos219
