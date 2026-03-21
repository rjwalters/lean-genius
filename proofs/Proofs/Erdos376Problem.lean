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

/-
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

/-
## Connection to Digit Representations

By Kummer's theorem, C(2n,n) coprime to p requires n to have restricted digits.
-/

/-- A natural number n has **p-small digits** if all digits in base p are ≤ (p-1)/2.
This ensures no carries when computing n + n in base p. -/
def HasSmallDigits (n : ℕ) (p : ℕ) : Prop :=
  ∀ d ∈ n.digits p, d ≤ (p - 1) / 2

/-
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

/-
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

/-
## Digit Sequence Definitions

The problem is equivalent to finding n with simultaneously restricted digits
in bases 3, 5, and 7.
-/

/-- The set of n with digits only in {0,1} in base 3. These are the "base-3 good" numbers. -/
def Base3Good : Set ℕ := {n | ∀ d ∈ n.digits 3, d ≤ 1}

/-- The set of n with digits only in {0,1,2} in base 5. -/
def Base5Good : Set ℕ := {n | ∀ d ∈ n.digits 5, d ≤ 2}

/-- The set of n with digits only in {0,1,2,3} in base 7. -/
def Base7Good : Set ℕ := {n | ∀ d ∈ n.digits 7, d ≤ 3}

end Erdos376
