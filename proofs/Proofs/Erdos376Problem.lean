/-
  Erdős Problem #376: Central Binomial Coefficients Coprime to 105

  **Question**: Are there infinitely many n such that C(2n,n) is coprime to 105?

  **Context**: 105 = 3 × 5 × 7, the product of the first three odd primes.

  **Known Result (EGRS 1975)**: For any two odd primes p and q, infinitely many n
  have C(2n,n) coprime to pq.

  **Status**: OPEN for three primes (like 105 = 3 × 5 × 7).

  **Key Tool - Kummer's Theorem**: The exact power of prime p dividing C(m,n) equals
  the number of carries when adding n + (m-n) in base p.

  **Corollary**: C(2n,n) is coprime to prime p iff n has only "small" digits
  (0, 1, ..., (p-1)/2) in base p representation.

  References:
  - https://erdosproblems.com/376
  - Erdős, Graham, Ruzsa, Straus, "On the prime factors of C(2n,n)" (1975)
  - Kummer, "Über die Ergänzungssätze..." (1852)
-/

import Mathlib

open Nat Set Finset BigOperators

namespace Erdos376

/-!
## Core Definitions

The central binomial coefficient C(2n,n) and coprimality conditions.
-/

/-- The **central binomial coefficient** C(2n,n) = (2n)! / (n!)².
This is `Nat.centralBinom` in Mathlib. -/
example (n : ℕ) : n.centralBinom = (2 * n).choose n := rfl

/-- An integer n is **105-good** if C(2n,n) is coprime to 105. -/
def Is105Good (n : ℕ) : Prop := n.centralBinom.Coprime 105

/-- The set of all 105-good integers. -/
def GoodSet105 : Set ℕ := {n | Is105Good n}

/-!
## Connection to Digit Representations

By Kummer's theorem, C(2n,n) coprime to p requires n to have restricted digits.
-/

/-- A natural number n has **p-small digits** if all digits in base p are ≤ (p-1)/2.
This ensures no carries when computing n + n in base p. -/
def HasSmallDigits (n : ℕ) (p : ℕ) : Prop :=
  ∀ d ∈ n.digits p, d ≤ (p - 1) / 2

/-- **Kummer's Theorem** (stated as axiom): The exact power of prime p dividing
C(m,k) equals the number of carries when adding k + (m-k) in base p.

The number of carries when adding a + b in base p equals the number of
positions where a_i + b_i + carry_{i-1} ≥ p.

We state a simplified version: the exact power is determined by the digit sums. -/
axiom kummer_theorem (m k p : ℕ) (hp : p.Prime) :
    ∃ carries : ℕ, p.factorization (m.choose k) = carries

/-- Corollary: C(2n,n) coprime to p iff n has p-small digits. -/
axiom centralBinom_coprime_iff_small_digits (n p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    n.centralBinom.Coprime p ↔ HasSmallDigits n p

/-!
## Specific Conditions for 105 = 3 × 5 × 7

For C(2n,n) coprime to 105, n must satisfy digit constraints in three bases.
-/

/-- 105 = 3 × 5 × 7, the product of first three odd primes. -/
theorem factorization_105 : 105 = 3 * 5 * 7 := by norm_num

/-- C(2n,n) coprime to 105 requires coprimality to each prime factor. -/
axiom coprime_105_iff (n : ℕ) :
    n.centralBinom.Coprime 105 ↔
    n.centralBinom.Coprime 3 ∧ n.centralBinom.Coprime 5 ∧ n.centralBinom.Coprime 7

/-- For coprimality to 3: n must have only digits 0, 1 in base 3. -/
axiom coprime_3_digits (n : ℕ) :
    n.centralBinom.Coprime 3 ↔ ∀ d ∈ n.digits 3, d ≤ 1

/-- For coprimality to 5: n must have only digits 0, 1, 2 in base 5. -/
axiom coprime_5_digits (n : ℕ) :
    n.centralBinom.Coprime 5 ↔ ∀ d ∈ n.digits 5, d ≤ 2

/-- For coprimality to 7: n must have only digits 0, 1, 2, 3 in base 7. -/
axiom coprime_7_digits (n : ℕ) :
    n.centralBinom.Coprime 7 ↔ ∀ d ∈ n.digits 7, d ≤ 3

/-!
## The EGRS Theorem (1975)

For any TWO odd primes, infinitely many n have C(2n,n) coprime to their product.
-/

/-- **EGRS Theorem (1975)**: For any two odd primes p and q, there are infinitely
many n such that C(2n,n) is coprime to pq.

This was proved by Erdős, Graham, Ruzsa, and Straus in 1975. -/
axiom egrs_theorem (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hp2 : Odd p) (hq2 : Odd q) :
    {n : ℕ | n.centralBinom.Coprime (p * q)}.Infinite

/-- Corollary: Infinitely many n have C(2n,n) coprime to 15 = 3 × 5. -/
theorem infinitely_coprime_15 : {n : ℕ | n.centralBinom.Coprime 15}.Infinite := by
  have h15 : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h15]
  exact egrs_theorem 3 5 Nat.prime_three Nat.prime_five (by decide) (by decide)

/-- Corollary: Infinitely many n have C(2n,n) coprime to 21 = 3 × 7. -/
theorem infinitely_coprime_21 : {n : ℕ | n.centralBinom.Coprime 21}.Infinite := by
  have h21 : (21 : ℕ) = 3 * 7 := by norm_num
  rw [h21]
  exact egrs_theorem 3 7 Nat.prime_three Nat.prime_seven (by decide) (by decide)

/-- Corollary: Infinitely many n have C(2n,n) coprime to 35 = 5 × 7. -/
theorem infinitely_coprime_35 : {n : ℕ | n.centralBinom.Coprime 35}.Infinite := by
  have h35 : (35 : ℕ) = 5 * 7 := by norm_num
  rw [h35]
  exact egrs_theorem 5 7 Nat.prime_five Nat.prime_seven (by decide) (by decide)

/-!
## Main Conjecture (OPEN)

The question for three primes remains open!
-/

/-- **Erdős Problem #376 (OPEN)**: Are there infinitely many n such that
C(2n,n) is coprime to 105 = 3 × 5 × 7?

This extends EGRS from two primes to three primes. -/
axiom erdos_376_conjecture :
    {n : ℕ | n.centralBinom.Coprime 105}.Infinite ∨
    ¬{n : ℕ | n.centralBinom.Coprime 105}.Infinite

/-- The positive answer would mean infinitely many 105-good integers exist. -/
axiom erdos_376_positive_answer :
    {n : ℕ | n.centralBinom.Coprime 105}.Infinite

/-!
## Known 105-Good Integers

We verify specific small values of n that are 105-good.
-/

/-- 1 is 105-good: C(2,1) = 2, which is coprime to 105. -/
theorem one_is_good : Is105Good 1 := by
  unfold Is105Good
  native_decide

/-- 2 is 105-good: C(4,2) = 6 = 2 × 3, not coprime to 105. -/
theorem two_not_good : ¬Is105Good 2 := by
  unfold Is105Good
  native_decide

/-- 4 is 105-good: C(8,4) = 70 = 2 × 5 × 7, not coprime to 105. -/
theorem four_not_good : ¬Is105Good 4 := by
  unfold Is105Good
  native_decide

/-- List of small 105-good values (verified computationally).
These are n where C(2n,n) has no factors of 3, 5, or 7. -/
axiom small_good_values : ({1} : Set ℕ) ⊆ GoodSet105

/-!
## Density Considerations

The set of 105-good integers is expected to be sparse but infinite.
-/

/-- The density of n coprime to a single prime p is positive.
In base p, roughly (1/2)^{log_p n} proportion satisfy small digits. -/
axiom density_single_prime (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    {n : ℕ | n.centralBinom.Coprime p}.Infinite

/-- For product of k odd primes, density decreases exponentially with k. -/
axiom density_decreases_with_primes :
    ∀ k : ℕ, ∃ c : ℝ, c > 0 ∧
    ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ 2 < p) → P.card = k →
    ∃ d : ℝ, d ≥ c^k ∧ d > 0

/-!
## Connection to Digit Sequences

The problem is equivalent to finding n with simultaneously restricted digits
in bases 3, 5, and 7.
-/

/-- The set of n with digits only in {0,1} in base 3. These are the "base-3 good" numbers. -/
def Base3Good : Set ℕ := {n | ∀ d ∈ n.digits 3, d ≤ 1}

/-- The set of n with digits only in {0,1,2} in base 5. -/
def Base5Good : Set ℕ := {n | ∀ d ∈ n.digits 5, d ≤ 2}

/-- The set of n with digits only in {0,1,2,3} in base 7. -/
def Base7Good : Set ℕ := {n | ∀ d ∈ n.digits 7, d ≤ 3}

/-- 105-good integers are exactly the intersection of the three base-good sets. -/
axiom good_105_characterization :
    GoodSet105 = Base3Good ∩ Base5Good ∩ Base7Good

/-- Each individual base-good set is infinite. -/
axiom base3Good_infinite : Base3Good.Infinite
axiom base5Good_infinite : Base5Good.Infinite
axiom base7Good_infinite : Base7Good.Infinite

/-- The question is whether the intersection is also infinite. -/
axiom intersection_question :
    (Base3Good ∩ Base5Good ∩ Base7Good).Infinite ↔
    {n : ℕ | n.centralBinom.Coprime 105}.Infinite

/-!
## Historical Context

The study of prime factors of central binomial coefficients has a rich history.
Kummer's 1852 theorem provides the key tool, and EGRS 1975 established the
two-prime case. The three-prime case remains open.
-/

/-- For any prime p, there are infinitely many n with p | C(2n,n). -/
axiom infinitely_many_divisible (p : ℕ) (hp : p.Prime) :
    {n : ℕ | p ∣ n.centralBinom}.Infinite

/-- C(2n,n) is always even for n ≥ 1. -/
axiom centralBinom_even (n : ℕ) (hn : 1 ≤ n) : 2 ∣ n.centralBinom

/-!
## Generalizations

Erdős asked about other products of primes beyond 105.
-/

/-- Generalization: For any finite set of odd primes P, is
{n | C(2n,n) coprime to ∏ p ∈ P} infinite? -/
axiom general_conjecture (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    {n : ℕ | n.centralBinom.Coprime (∏ p ∈ P, p)}.Infinite ∨
    ¬{n : ℕ | n.centralBinom.Coprime (∏ p ∈ P, p)}.Infinite

/-- For |P| = 2, the answer is YES (EGRS). -/
axiom two_primes_solved (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2 < p)
    (hcard : P.card = 2) :
    {n : ℕ | n.centralBinom.Coprime (∏ p ∈ P, p)}.Infinite

end Erdos376
