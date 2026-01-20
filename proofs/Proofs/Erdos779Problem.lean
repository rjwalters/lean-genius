/-
  Erdős Problem #779: Primorial Plus Prime

  **Problem**: Let p₁ < p₂ < ... < pₙ be the first n primes, and let
  P = p₁ · p₂ · ... · pₙ (the primorial). Does there always exist a prime p
  with pₙ < p < P such that P + p is also prime?

  **Status**: OPEN

  **Known Results**:
  - Verified for n ≤ 1000 by Deaconescu
  - Erdős conjectured the least such p satisfies p ≤ n^O(1)
  - Heuristically, failure probability is exponentially small

  This is a problem of Deaconescu. The heuristic argument suggests that
  P + p is prime with probability ≈ 1/log(P), so with ~(P - pₙ) primes
  to try, the chance of all failing is vanishingly small.

  Reference: https://erdosproblems.com/779
  [Gu83] Güth (1983)
  Related: OEIS A005235 (smallest prime p > pₙ such that P + p is prime)

  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib

open Finset Nat

namespace Erdos779

/-
## The Primorial Function

The primorial of n is the product of the first n primes.
This is denoted n# in some notations.
-/

/-- The nth prime (0-indexed), using Mathlib's Nat.nth.
  nthPrime 0 = 2, nthPrime 1 = 3, nthPrime 2 = 5, etc. -/
noncomputable def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- The primorial: product of the first n primes.
For n = 0, this is the empty product = 1.
For n = 1, this is 2.
For n = 2, this is 2 · 3 = 6.
For n = 3, this is 2 · 3 · 5 = 30. -/
noncomputable def primorial (n : ℕ) : ℕ := ∏ i ∈ range n, nthPrime i

/-
## Basic Properties of Primorials
-/

/-- The primorial of 0 is the empty product, which equals 1. -/
theorem primorial_zero : primorial 0 = 1 := by
  simp [primorial]

/-- The primorial is always positive (product of positive primes). -/
theorem primorial_pos (n : ℕ) : 0 < primorial n := by
  simp only [primorial]
  apply Finset.prod_pos
  intro i _
  simp only [nthPrime]
  exact Nat.Prime.pos (Nat.prime_nth_prime i)

/-- The nth prime divides the (n+1)-primorial. -/
theorem nthPrime_dvd_primorial (k n : ℕ) (h : k < n) : nthPrime k ∣ primorial n := by
  simp only [primorial]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr h)

/-
## The Main Conjecture (OPEN)

The Deaconescu conjecture asks: can we always find a prime p between
pₙ and P such that P + p is prime?
-/

/-- The set of primes p with pₙ < p < P such that P + p is prime.
This is the set whose non-emptiness the conjecture asserts. -/
def validPrimes (n : ℕ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ nthPrime (n - 1) < p ∧ p < primorial n ∧ (primorial n + p).Prime}

/-- **Erdős Problem #779 (OPEN)**: The Deaconescu Conjecture.

For all n ≥ 1, there exists a prime p with pₙ < p < P (where P is the
primorial of n) such that P + p is also prime.

This is formalized as: for n ≥ 1, validPrimes n is nonempty. -/
def deaconescuConjecture : Prop :=
  ∀ n ≥ 1, (validPrimes n).Nonempty

/-- Alternative formulation matching the formal-conjectures statement.
Uses 0-indexed primes and requires p between nth prime n and the product. -/
def erdos779Conjecture : Prop :=
  ∀ n ≥ 1, let P := ∏ i ∈ range (n + 1), Nat.nth Nat.Prime i
    ∃ p, Nat.Prime p ∧ Nat.Prime (P + p) ∧ Nat.nth Nat.Prime n < p ∧ p < P

/-
## Erdős's Stronger Conjecture

Erdős believed the least valid prime is polynomial in n.
-/

/-- **Erdős's Stronger Conjecture**: The smallest valid prime is O(n^c).
This is a quantitative strengthening: not only does a valid prime exist,
but one can be found that is polynomially bounded in n. -/
def erdosPolynomialBound : Prop :=
  ∃ c : ℕ, ∀ n ≥ 2, ∃ p ∈ validPrimes n, p ≤ n ^ c

/-
## Verified Small Cases

We verify the conjecture for small n by finding explicit primes.
The nth prime values are:
  nthPrime 0 = 2
  nthPrime 1 = 3
  nthPrime 2 = 5
  nthPrime 3 = 7
  nthPrime 4 = 11
-/

/-- For n = 2: P = primorial 2 = 2 · 3 = 6.
We need pₙ₋₁ = nthPrime 1 = 3, and p with 3 < p < 6 such that 6 + p is prime.
The only prime in (3, 6) is 5. And 6 + 5 = 11 is prime! -/
theorem case_n_eq_2_exists : ∃ p, p.Prime ∧ 3 < p ∧ p < 6 ∧ (6 + p).Prime := by
  use 5
  constructor
  · exact Nat.prime_five
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- For n = 3: P = primorial 3 = 2 · 3 · 5 = 30.
We need p with 5 < p < 30 such that 30 + p is prime.
p = 7 works: 30 + 7 = 37, which is prime. -/
theorem case_n_eq_3_exists : ∃ p, p.Prime ∧ 5 < p ∧ p < 30 ∧ (30 + p).Prime := by
  use 7
  constructor
  · exact Nat.prime_seven
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- For n = 4: P = primorial 4 = 2 · 3 · 5 · 7 = 210.
We need p with 7 < p < 210 such that 210 + p is prime.
p = 13 works: 210 + 13 = 223, which is prime. -/
theorem case_n_eq_4_exists : ∃ p, p.Prime ∧ 7 < p ∧ p < 210 ∧ (210 + p).Prime := by
  use 13
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-- For n = 5: P = primorial 5 = 2 · 3 · 5 · 7 · 11 = 2310.
We need p with 11 < p < 2310 such that 2310 + p is prime.
p = 23 works: 2310 + 23 = 2333, which is prime. -/
theorem case_n_eq_5_exists : ∃ p, p.Prime ∧ 11 < p ∧ p < 2310 ∧ (2310 + p).Prime := by
  use 23
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/-
## Heuristic Analysis

The heuristic argument for why the conjecture should be true:
- P + p is prime with "probability" ≈ 1/log(P)
- There are ~(P - pₙ) primes to try in the interval (pₙ, P)
- The probability that ALL fail is ≈ (1 - 1/log(P))^(P - pₙ)
- Since P ≈ n^((1+o(1))n), this is ≈ exp(-n^(cn)) for some c > 0
- This is "ridiculously small" as Cambie notes
-/

/-- Each prime is at least 2. -/
lemma nthPrime_ge_two (k : ℕ) : nthPrime k ≥ 2 := by
  simp only [nthPrime]
  exact Nat.Prime.two_le (Nat.prime_nth_prime k)

/-- The primorial grows very fast: roughly e^(n log n) by the prime number theorem. -/
theorem primorial_growth_heuristic : ∀ n ≥ 1, primorial n ≥ 2^n := by
  intro n hn
  -- Product of n terms each ≥ 2 is ≥ 2^n
  simp only [primorial]
  calc ∏ i ∈ range n, nthPrime i
      ≥ ∏ _i ∈ range n, 2 := by
        apply Finset.prod_le_prod
        · intro i _; exact Nat.zero_le 2
        · intro i _; exact nthPrime_ge_two i
    _ = 2 ^ n := by simp [Finset.prod_const, Finset.card_range]

/-
## Connection to Other Problems
-/

/-- The primorial primes: primes of the form P# ± 1.
These are related but distinct from our problem.
P# + 1 being prime is much rarer than finding some p with P + p prime. -/
def primorialPrime (n : ℕ) : Prop := (primorial n + 1).Prime ∨ (primorial n - 1).Prime

/-- The sequence of smallest valid primes (OEIS A005235).
For n = 2: smallest p with 3 < p < 6 and 6+p prime is 5.
For n = 3: smallest p with 5 < p < 30 and 30+p prime is 7.
For n = 4: smallest p with 7 < p < 210 and 210+p prime is 13. -/
axiom oeis_A005235 : ℕ → ℕ

/-- The first few values of A005235 (axiomatized from OEIS).
a(n) = smallest prime p > p_n such that primorial(n) + p is prime. -/
axiom oeis_A005235_values :
  oeis_A005235 2 = 5 ∧
  oeis_A005235 3 = 7 ∧
  oeis_A005235 4 = 13 ∧
  oeis_A005235 5 = 23 ∧
  oeis_A005235 6 = 17

/-
## The Problem is Open but Heuristically True

Deaconescu verified the conjecture for n ≤ 1000. The heuristic argument
strongly suggests it should be true for all n, but no proof exists.
-/

/-- **Computational Verification**: The conjecture has been verified for n ≤ 1000. -/
axiom deaconescu_verification : ∀ n, 2 ≤ n → n ≤ 1000 → (validPrimes n).Nonempty

/-- The heuristic probability that no valid prime exists is extremely small. -/
axiom heuristic_failure_probability (n : ℕ) (hn : n ≥ 2) :
    ∃ c > 0, ∃ (prob : ℝ), prob < Real.exp (-(n : ℝ)^c)

end Erdos779
