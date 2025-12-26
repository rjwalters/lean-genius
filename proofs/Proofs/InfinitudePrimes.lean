import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Infinitude of Prime Numbers

## What This Proves
We prove Euclid's theorem: for any n, there exists a prime p > n. This
establishes that there are infinitely many prime numbers.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's definitions of `Nat.Prime`
  and `Nat.factorial`, plus the lemma `Nat.dvd_factorial`. The existence of
  prime divisors (`Nat.exists_prime_and_dvd`) is also from Mathlib.
- **Original Contributions:** The proof structure follows Euclid's classical
  argument with our own lemmas. We prove `dvd_factorial`, `factorial_succ_ge_two`,
  and `dvd_of_dvd_add_one` to build up to the main theorem.
- **Proof Techniques Demonstrated:** Constructive existence proofs, proof by
  contradiction for the bound, `omega` for arithmetic, divisibility reasoning.

## Status
- [x] Complete proof
- [ ] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.Prime` : Definition of prime numbers
- `Nat.factorial` : Factorial function and properties
- `Nat.dvd_factorial` : k ∣ n! when 0 < k ≤ n
- `Nat.exists_prime_and_dvd` : Every n ≥ 2 has a prime divisor
- `Nat.Prime.one_lt` : Every prime is > 1

Original author: Yannis Konstantoulas
Source: https://github.com/ykonstant1/InfinitePrimes
-/

namespace InfinitudePrimes

/-! ## Key Lemmas for the Proof -/

/-- Any positive k ≤ n divides n!
    This is the crucial property of factorials used in Euclid's proof. -/
theorem dvd_factorial {k n : ℕ} (hk : 0 < k) (hkn : k ≤ n) : k ∣ n.factorial := by
  -- Use Mathlib's existing theorem
  exact Nat.dvd_factorial hk hkn

/-- n! + 1 is always ≥ 2 for any n.
    This ensures n! + 1 has at least one prime divisor. -/
theorem factorial_succ_ge_two (n : ℕ) : n.factorial + 1 ≥ 2 := by
  have h : n.factorial ≥ 1 := Nat.factorial_pos n
  omega

/-- If p divides both a and a + 1, then p divides 1.
    This is the key observation in Euclid's proof. -/
theorem dvd_of_dvd_add_one {p a : ℕ} (h1 : p ∣ a) (h2 : p ∣ a + 1) : p ∣ 1 := by
  have hsub : p ∣ (a + 1) - a := Nat.dvd_sub' h2 h1
  simp only [add_tsub_cancel_left] at hsub
  exact hsub

/-! ## The Main Theorem -/

/-- **Euclid's Theorem: There are infinitely many primes**

    For any natural number n, there exists a prime p greater than n.

    Proof sketch:
    1. Consider Q = n! + 1
    2. Q ≥ 2, so Q has a prime divisor p
    3. Claim: p > n
    4. Proof by contradiction: If p ≤ n, then:
       - p ∣ n! (since p is in the product 1 × 2 × ... × n)
       - p ∣ n! + 1 = Q (by assumption)
       - Therefore p ∣ 1
       - But p ≥ 2, contradiction!
    5. So p > n, and we found our prime. -/
theorem unbounded_primes : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := by
  intro n
  -- Let Q = n! + 1
  let Q := n.factorial + 1
  -- Q ≥ 2, so it has a minimum prime factor
  have hQ : Q ≥ 2 := factorial_succ_ge_two n
  have hQ_ne_one : Q ≠ 1 := by omega
  -- Get the minimum prime factor of Q
  have ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hQ_ne_one
  -- We claim p > n
  use p
  constructor
  · exact hp_prime
  · -- Prove p > n by contradiction
    by_contra h_not_gt
    push_neg at h_not_gt  -- h_not_gt : p ≤ n
    -- Since p ≤ n and p is prime (so p ≥ 2 > 0), p divides n!
    have hp_pos : 0 < p := hp_prime.pos
    have hp_dvd_fact : p ∣ n.factorial := dvd_factorial hp_pos h_not_gt
    -- But p also divides Q = n! + 1
    -- So p divides (n! + 1) - n! = 1
    have hp_dvd_one : p ∣ 1 := dvd_of_dvd_add_one hp_dvd_fact hp_dvd
    -- Since p divides 1, p must equal 1
    have hp_eq_one : p = 1 := Nat.dvd_one.mp hp_dvd_one
    -- But p is prime, so p ≠ 1 - contradiction!
    exact hp_prime.ne_one hp_eq_one

/-- Alternative statement: The set of primes is infinite.
    This follows immediately from unbounded_primes. -/
theorem primes_infinite : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n := unbounded_primes

/-! ## Corollaries -/

/-- There exists a prime greater than any given prime. -/
theorem exists_prime_gt_prime (p : ℕ) (_hp : Nat.Prime p) : ∃ q : ℕ, Nat.Prime q ∧ q > p := by
  exact unbounded_primes p

/-- There is no largest prime. -/
theorem no_largest_prime : ¬∃ p : ℕ, Nat.Prime p ∧ ∀ q : ℕ, Nat.Prime q → q ≤ p := by
  intro ⟨p, _, hp_largest⟩
  obtain ⟨q, hq_prime, hq_gt⟩ := unbounded_primes p
  have hq_le := hp_largest q hq_prime
  omega

#check unbounded_primes
#check primes_infinite
#check no_largest_prime

end InfinitudePrimes
