/-
  Aristotle targets for Erdős Problem #891
  Routine supporting lemmas for automated proof search.
  See Erdos891Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

open Nat BigOperators Finset

namespace Erdos891Aristotle

/-
## Section 1: Prime Factor Counting (Ω function)

bigOmega counts prime factors with multiplicity.
Redefined locally for self-containment.
-/

def bigOmega (n : ℕ) : ℕ := n.factorization.sum fun _ k => k

/-- Ω(p^k) = k for any prime p. Key identity for the problem. -/
theorem bigOmega_prime_pow (p : ℕ) (hp : p.Prime) (k : ℕ) :
    bigOmega (p ^ k) = k := by sorry

/-- Ω(m·n) = Ω(m) + Ω(n) when gcd(m,n) = 1. Additivity on coprimes. -/
theorem bigOmega_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) :
    bigOmega (m * n) = bigOmega m + bigOmega n := by sorry

/-- Ω(n) ≥ 1 for any n ≥ 2. Every composite or prime has at least one factor. -/
theorem bigOmega_pos_of_one_lt {n : ℕ} (hn : 1 < n) :
    0 < bigOmega n := by sorry

/-- Ω(n) ≤ n for all n. Crude upper bound. -/
theorem bigOmega_le (n : ℕ) : bigOmega n ≤ n := by sorry

/-
## Section 2: Nat.nth Prime Values

Values of the first few primes via Nat.nth Nat.Prime.
These link the noncomputable enumeration to concrete values.
-/

/-- The 0th prime is 2. -/
theorem nth_prime_zero : Nat.nth Nat.Prime 0 = 2 := by sorry

/-- The 1st prime is 3. -/
theorem nth_prime_one : Nat.nth Nat.Prime 1 = 3 := by sorry

/-- The 2nd prime is 5. -/
theorem nth_prime_two : Nat.nth Nat.Prime 2 = 5 := by sorry

/-- The 3rd prime is 7. -/
theorem nth_prime_three : Nat.nth Nat.Prime 3 = 7 := by sorry

/-- The 4th prime is 11. -/
theorem nth_prime_four : Nat.nth Nat.Prime 4 = 11 := by sorry

/-
## Section 3: Primorial Function Properties
-/

noncomputable def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- primorial 0 = 1 (empty product). -/
theorem primorial_zero : primorial 0 = 1 := by sorry

/-- Primorial recurrence: primorial(k+1) = primorial(k) · p_k. -/
theorem primorial_succ (k : ℕ) :
    primorial (k + 1) = primorial k * Nat.nth Nat.Prime k := by sorry

/-- Primorial is always positive. -/
theorem primorial_pos (k : ℕ) : 0 < primorial k := by sorry

/-- Each prime divides the primorial it appears in. -/
theorem nthPrime_dvd_primorial {i k : ℕ} (h : i < k) :
    Nat.nth Nat.Prime i ∣ primorial k := by sorry

/-
## Section 4: Divisibility in Short Intervals

These support the structural argument that short intervals
must contain numbers with many prime factors.
-/

/-- Every interval [n, n+d) contains a multiple of d (for d > 0). -/
theorem exists_multiple_in_interval (d : ℕ) (hd : 0 < d) (n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + d ∧ d ∣ m := by sorry

/-- Among any 3 consecutive integers starting from n ≥ 1, one is even. -/
theorem three_consec_has_even (n : ℕ) :
    ∃ m, n ≤ m ∧ m < n + 3 ∧ 2 ∣ m := by sorry

/-
## Section 5: Smooth Number Facts

k-smooth numbers have all prime factors ≤ p_k.
-/

/-- All prime factors of 2 are at most 2 (2 is 2-smooth). -/
theorem two_smooth : ∀ p : ℕ, p.Prime → p ∣ 2 → p ≤ 2 := by sorry

/-- All prime factors of 12 are at most 3 (12 is 3-smooth). -/
theorem twelve_3smooth : ∀ p : ℕ, p.Prime → p ∣ 12 → p ≤ 3 := by sorry

/-- All prime factors of 30 are at most 5 (30 is 5-smooth). -/
theorem thirty_5smooth : ∀ p : ℕ, p.Prime → p ∣ 30 → p ≤ 5 := by sorry

/-- All prime factors of 210 are at most 7 (210 is 7-smooth). -/
theorem twoten_7smooth : ∀ p : ℕ, p.Prime → p ∣ 210 → p ≤ 7 := by sorry

/-
## Section 6: Arithmetic Identities

Specific computations used in the formalization.
-/

/-- 2 · 3 = 6 (primorial of 2 primes). -/
theorem two_mul_three : 2 * 3 = 6 := by norm_num

/-- 2 · 3 · 5 = 30 (primorial of 3 primes). -/
theorem primorial_three_val : 2 * 3 * 5 = 30 := by norm_num

/-- 2 · 3 · 5 · 7 = 210 (primorial of 4 primes). -/
theorem primorial_four_val : 2 * 3 * 5 * 7 = 210 := by norm_num

/-- 2 · 3 · 5 · 7 · 11 = 2310 (primorial of 5 primes). -/
theorem primorial_five_val : 2 * 3 * 5 * 7 * 11 = 2310 := by norm_num

end Erdos891Aristotle
