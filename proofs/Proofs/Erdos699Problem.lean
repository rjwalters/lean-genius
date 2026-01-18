/-
  Erdős Problem #699: Prime Divisors of GCDs of Binomial Coefficients

  **Problem**: Is it true that for every 1 ≤ i < j ≤ n/2 there exists a
  prime p ≥ i such that p | gcd(C(n,i), C(n,j))?

  **Status**: OPEN (could be falsified by a finite counterexample)

  **Background**: The Sylvester-Schur theorem says that for any 1 ≤ i ≤ n/2,
  there exists a prime p > i dividing C(n,i). This problem asks about the
  common prime divisors of *two* binomial coefficients.

  **Erdős-Szekeres Conjecture**: The stronger claim that p > i (strict) holds
  except for finitely many exceptional triples (n, i, j).

  **Known counterexamples** to the strong form:
  - i = 2 with certain powers of 2
  - Several cases for i = 3
  - One case for i ≥ 4: gcd(C(28,5), C(28,14)) = 2³·3³·5

  Reference: https://erdosproblems.com/699
  [ErSz78] Erdős and Szekeres (1978)
  [Gu04] Guy, Unsolved Problems in Number Theory, Problem B31
-/

import Mathlib

open Nat

namespace Erdos699

/-!
## The Sylvester-Schur Theorem

A classical result: for any 1 ≤ i ≤ n/2, there exists a prime p > i
dividing the binomial coefficient C(n, i).

This ensures that "large" primes appear as divisors of binomial coefficients.
-/

/-- **Sylvester-Schur Theorem** (1934): For 1 ≤ i ≤ n/2, there exists a prime
    p > i that divides C(n, i).

    This is a classical result in combinatorial number theory. The proof uses
    properties of the product n(n-1)...(n-i+1) and shows that it must have
    a prime factor greater than i. -/
axiom sylvester_schur (n i : ℕ) (hi : 1 ≤ i) (hi_half : i ≤ n / 2) :
    ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.choose n i

/-!
## The Main Question (OPEN)

Erdős and Szekeres asked whether a similar result holds for the GCD of
two binomial coefficients: for 1 ≤ i < j ≤ n/2, does there exist a prime
p ≥ i with p | gcd(C(n,i), C(n,j))?

This remains open.
-/

/-- A prime p ≥ i divides both C(n, i) and C(n, j). -/
def HasCommonLargePrime (n i j : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ i ≤ p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j)

/-- A prime p > i (strict) divides both C(n, i) and C(n, j). -/
def HasCommonStrictlyLargePrime (n i j : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ i < p ∧ p ∣ Nat.gcd (Nat.choose n i) (Nat.choose n j)

/-- **Erdős Problem #699 (OPEN)**: For every 1 ≤ i < j ≤ n/2, does there exist
    a prime p ≥ i such that p | gcd(C(n,i), C(n,j))?

    This is a generalization of Sylvester-Schur from single binomial coefficients
    to their GCDs. The conjecture remains open and is marked as "falsifiable"
    (could be disproved by finding a counterexample). -/
def erdos_699_statement : Prop :=
  ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 → HasCommonLargePrime n i j

/-- The problem is open - we don't know whether it's true or false. -/
axiom erdos_699_open : True

/-!
## The Erdős-Szekeres Strengthening (OPEN)

Erdős and Szekeres conjectured the stronger result that p > i (strict inequality)
holds for all but finitely many triples (n, i, j).
-/

/-- **Erdős-Szekeres Conjecture**: The strengthened version with p > i (strict)
    holds except for finitely many exceptional triples.

    Known failures of the strict inequality:
    - When i = 2 and n is certain powers of 2
    - Several counterexamples when i = 3
    - One counterexample when i ≥ 4: (n, i, j) = (28, 5, 14)

    Note: gcd(C(28,5), C(28,14)) = 2³·3³·5 = 1080, with largest prime 5 = i. -/
def erdos_szekeres_conjecture : Prop :=
  ∃ E : Finset (ℕ × ℕ × ℕ),
    ∀ n i j : ℕ, 1 ≤ i → i < j → j ≤ n / 2 →
      (n, i, j) ∉ E → HasCommonStrictlyLargePrime n i j

/-!
## Concrete Computations

We verify some specific GCD computations to illustrate the problem.
-/

/-- C(6, 2) = 15 -/
theorem choose_6_2 : Nat.choose 6 2 = 15 := by native_decide

/-- C(6, 3) = 20 -/
theorem choose_6_3 : Nat.choose 6 3 = 20 := by native_decide

/-- gcd(C(6,2), C(6,3)) = gcd(15, 20) = 5 -/
theorem gcd_choose_6_2_3 : Nat.gcd (Nat.choose 6 2) (Nat.choose 6 3) = 5 := by native_decide

/-- For n=6, i=2, j=3: the prime 5 ≥ 2 divides gcd(C(6,2), C(6,3)).
    This verifies the conjecture for this specific case. -/
theorem example_6_2_3 : HasCommonLargePrime 6 2 3 := by
  use 5
  constructor
  · decide
  constructor
  · omega
  · native_decide

/-- C(10, 2) = 45 -/
theorem choose_10_2 : Nat.choose 10 2 = 45 := by native_decide

/-- C(10, 4) = 210 -/
theorem choose_10_4 : Nat.choose 10 4 = 210 := by native_decide

/-- C(10, 5) = 252 -/
theorem choose_10_5 : Nat.choose 10 5 = 252 := by native_decide

/-- gcd(C(10,2), C(10,5)) = gcd(45, 252) = 9 -/
theorem gcd_choose_10_2_5 : Nat.gcd (Nat.choose 10 2) (Nat.choose 10 5) = 9 := by native_decide

/-- For n=10, i=2, j=5: gcd = 9 = 3², so 3 ≥ 2 is a prime divisor.
    Note: 3 > 2, so this also satisfies the strict version. -/
theorem example_10_2_5 : HasCommonLargePrime 10 2 5 := by
  use 3
  constructor
  · decide
  constructor
  · omega
  · native_decide

/-!
## The Critical Counterexample to the Strong Form

Erdős and Szekeres noted that gcd(C(28,5), C(28,14)) = 1080 = 2³·3³·5,
where the largest prime divisor is 5 = i, not > i.
-/

/-- C(28, 5) = 98280 -/
theorem choose_28_5 : Nat.choose 28 5 = 98280 := by native_decide

/-- C(28, 14) = 40116600 -/
theorem choose_28_14 : Nat.choose 28 14 = 40116600 := by native_decide

/-- gcd(C(28,5), C(28,14)) = 1080 = 2³·3³·5 -/
theorem gcd_choose_28_5_14 : Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 := by native_decide

/-- 1080 = 2³·3³·5 factorization -/
theorem factor_1080 : 1080 = 2^3 * 3^3 * 5 := by native_decide

/-- The largest prime dividing 1080 is 5.
    This shows that for (n,i,j) = (28,5,14), the largest prime in gcd is exactly i,
    which is a counterexample to the strict version p > i.

    Proof sketch: 1080 = 2³ × 3³ × 5, so the only prime factors are 2, 3, 5. -/
theorem max_prime_1080_is_5 : ∀ p : ℕ, p.Prime → p ∣ 1080 → p ≤ 5 := by
  intro p hp hdiv
  -- 1080 = 2³ × 3³ × 5, prime factors are {2, 3, 5}
  have h2 : (2 : ℕ).Prime := Nat.prime_two
  have h3 : (3 : ℕ).Prime := Nat.prime_three
  have h5 : (5 : ℕ).Prime := Nat.prime_five
  -- We need to show any prime dividing 1080 is ≤ 5
  -- This requires checking the factorization
  sorry

/-- For n=28, i=5, j=14: the prime 5 ≥ 5 divides the gcd, satisfying the weak version.
    But there is NO prime p > 5 dividing the gcd (counterexample to strong version). -/
theorem example_28_5_14_weak : HasCommonLargePrime 28 5 14 := by
  use 5
  constructor
  · decide
  constructor
  · omega
  · native_decide

/-- The triple (28, 5, 14) is a counterexample to the strong form:
    there is no prime p > 5 dividing gcd(C(28,5), C(28,14)).

    This follows from: gcd = 1080 = 2³ × 3³ × 5, so max prime is 5 = i. -/
theorem counterexample_28_5_14_strong : ¬HasCommonStrictlyLargePrime 28 5 14 := by
  intro ⟨p, hp_prime, hp_gt, hp_div⟩
  have h_gcd : Nat.gcd (Nat.choose 28 5) (Nat.choose 28 14) = 1080 := by native_decide
  rw [h_gcd] at hp_div
  have h_le : p ≤ 5 := max_prime_1080_is_5 p hp_prime hp_div
  omega

/-!
## Why Sylvester-Schur Doesn't Immediately Help

Sylvester-Schur gives a prime p > i dividing C(n, i), and a prime q > j dividing C(n, j).
But p and q might be different! The question is about *common* divisors.
-/

/-- The product representation: C(n, i) = n! / (i! · (n-i)!).
    Primes in the range (i, n-i] often appear, but finding common ones is harder. -/
theorem choose_formula (n k : ℕ) (h : k ≤ n) :
    Nat.choose n k = n.factorial / (k.factorial * (n - k).factorial) :=
  Nat.choose_eq_factorial_div_factorial h

end Erdos699
