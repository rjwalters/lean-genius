import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Bertrand's Postulate

## What This Proves
Bertrand's Postulate: For every integer n > 1, there exists a prime p such that n < p ≤ 2n.

Equivalently: between any number greater than 1 and its double, there is always at least
one prime number.

## Historical Context
Joseph Bertrand conjectured this result in 1845 after verifying it for all n up to 3 million.
Pafnuty Chebyshev gave the first proof in 1852 using analytic techniques. In 1932, the
19-year-old Paul Erdős published an elegant elementary proof that has become the standard
approach. The theorem is sometimes called the "Bertrand-Chebyshev theorem."

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.NumberTheory.Bertrand` which provides
  the complete proof following Erdős's approach via analysis of the central binomial
  coefficient.
- **Original Contributions:** Pedagogical wrapper theorems with documentation explaining
  the theorem's significance, equivalent formulations, and interesting corollaries.
- **Proof Techniques Demonstrated:** The underlying Mathlib proof analyzes the prime
  factorization of C(2n, n) = (2n)!/(n!)² to derive bounds on prime distribution.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.NumberTheory.Bertrand` : Complete proof of Bertrand's Postulate
- `Nat.exists_prime_lt_and_le_two_mul` : Main theorem statement
- `Nat.bertrand` : Alias for the main theorem

## Why This Theorem is Important
Bertrand's Postulate has numerous applications:
- Provides explicit bounds on prime gaps (gap < n for primes near n)
- Used in proofs about the distribution of primes
- Foundation for stronger results like the Prime Number Theorem
- Applications in combinatorics and algorithms requiring "nearby" primes

## Wiedijk's 100 Theorems: #98
-/

namespace BertrandsPostulate

/-! ## The Main Theorem -/

/-- **Bertrand's Postulate (Main Statement)**

    For any positive natural number n, there exists a prime p with n < p ≤ 2n.

    This is the core result: between n and 2n (inclusive), there's always a prime.
    Note: Mathlib states this as n < p ≤ 2n, which is equivalent to n < p < 2n + 1. -/
theorem bertrand_postulate (n : ℕ) (hn : 0 < n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n (Nat.pos_iff_ne_zero.mp hn)

/-- **Bertrand's Postulate (Alternative Name)**

    An alias for the main theorem using Mathlib's naming convention. -/
theorem bertrand (n : ℕ) (hn : 0 < n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand n (Nat.pos_iff_ne_zero.mp hn)

/-! ## Corollaries -/

/-- **Existence of primes in intervals**

    For n ≥ 1, there's a prime between n and 2n (exclusive on left, inclusive on right). -/
theorem exists_prime_between (n : ℕ) (hn : 1 ≤ n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  exact bertrand_postulate n hn

/-- **Prime gaps are bounded**

    For any prime p > 2, the next prime is at most 2p - 1.
    (Since there's a prime q with p < q ≤ 2p.) -/
theorem prime_gap_bounded (p : ℕ) (hp : Nat.Prime p) :
    ∃ q, Nat.Prime q ∧ p < q ∧ q ≤ 2 * p :=
  bertrand_postulate p hp.pos

/-- **Infinitude of primes (via Bertrand)**

    Bertrand's Postulate implies there are infinitely many primes.
    For any n, apply Bertrand to get a prime > n. -/
theorem primes_infinite_via_bertrand : ∀ n : ℕ, ∃ p, Nat.Prime p ∧ p > n := by
  intro n
  cases' n with n
  · -- n = 0: any prime works
    use 2
    exact ⟨Nat.prime_two, by omega⟩
  · -- n = Nat.succ n ≥ 1
    obtain ⟨p, hp_prime, hp_gt, _⟩ := bertrand_postulate (n + 1) (by omega)
    exact ⟨p, hp_prime, hp_gt⟩

/-- **No largest prime (via Bertrand)**

    Another consequence: there is no largest prime number. -/
theorem no_largest_prime_via_bertrand : ¬∃ p, Nat.Prime p ∧ ∀ q, Nat.Prime q → q ≤ p := by
  intro ⟨p, _, h_largest⟩
  obtain ⟨q, hq_prime, hq_gt⟩ := primes_infinite_via_bertrand p
  have hq_le := h_largest q hq_prime
  omega

/-! ## Stronger Bounds for Large n

The proof works by first establishing the result for n ≥ 512 via analysis of
the central binomial coefficient, then using a descending chain of known primes
to cover smaller values. -/

/-- **Bertrand's Postulate for large n**

    For n ≥ 512, the postulate holds. This is the "main engine" of the proof,
    where the Erdős-style analysis of C(2n,n) applies directly. -/
theorem bertrand_large (n : ℕ) (hn : 512 ≤ n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul_eventually n hn

/-! ## Examples

### Concrete instances of Bertrand's Postulate:

**n = 1:** Primes between 1 and 2: {2}. ✓

**n = 2:** Primes between 2 and 4: {3}. ✓

**n = 3:** Primes between 3 and 6: {5}. ✓

**n = 10:** Primes between 10 and 20: {11, 13, 17, 19}. ✓

**n = 100:** Primes between 100 and 200: {101, 103, 107, 109, 113, ...}. ✓

### The "descending chain" for small n:

The proof uses this chain of primes, each more than half the next:
983, 491, 241, 127, 61, 31, 17, 11, 7, 5, 3, 2

For any n ≤ 512, we find a prime in this chain that lies in (n, 2n].
-/

/-! ## Connection to Prime Number Theorem

Bertrand's Postulate is a stepping stone to the Prime Number Theorem (PNT).

While Bertrand guarantees at least one prime in (n, 2n], the PNT tells us
approximately how many: about n/ln(n) primes exist between 1 and n.

For the interval (n, 2n], the PNT predicts roughly n/ln(n) primes,
far more than Bertrand's guaranteed minimum of 1.

The Riemann Hypothesis, if true, would give even tighter bounds on the
distribution of primes in such intervals. -/

/-! ## Key Theorems Summary -/

#check bertrand_postulate
#check bertrand
#check exists_prime_between
#check prime_gap_bounded
#check primes_infinite_via_bertrand
#check no_largest_prime_via_bertrand

end BertrandsPostulate
