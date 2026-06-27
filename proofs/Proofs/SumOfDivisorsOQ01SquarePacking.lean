/-
# Euler's Odd-Perfect Form — the square-packaging half (`m²`)

This file extends the *local prime-power engine* of `SumOfDivisorsOQ01.lean`
toward the **global** assembly of Euler's structural theorem.

## The two halves of Euler's form

Euler (1747): an odd perfect `N` has the form `N = p^a·m²` with `p` the special
prime, `p ≡ a ≡ 1 (mod 4)`, `gcd(p, m) = 1`.  The classical proof has two halves:

1. **Square-packaging (this file).**  Multiplicativity of `σ` spreads the
   prime-power parity law L1 (`σ(p^a)` odd ⟺ `a` even) across the whole
   factorization: for odd `N`, `σ(N)` is odd ⟺ *every* prime exponent is even
   ⟺ `N` is a perfect square.  This is the `m²` half — the non-special primes,
   each to an even power, assemble into a square.

2. **Special-prime counting (deferred).**  The harder mod-4 *counting* that
   `σ(N)=2N` forces *exactly one* odd-exponent prime, and that L2 pins it to
   `p ≡ a ≡ 1 (mod 4)`.  Left for follow-up.

## Contents

* `isSquare_iff_even_factorization` — `N` (positive) is a square ⟺ every prime
  exponent in `N.factorization` is even.  (Pure factorization fact.)
* `odd_sigma_iff_even_factorization` — for odd `N`, `σ(N)` is odd ⟺ every prime
  exponent is even.  (L1 spread by `isMultiplicative_sigma`.)
* `odd_sigma_odd_iff_isSquare` — **headline**: for odd `N`, `σ(N)` is odd ⟺ `N`
  is a perfect square.  (Odd case of "σ(n) odd ⟺ n is a square or twice a
  square".)
* `odd_perfect_not_isSquare` — corollary: an odd perfect number is never a
  perfect square (its `σ = 2N` is even, so it cannot be a square).

All results are conditional structure theorems and assume nothing about the
existence of odd perfect numbers (open).
-/
import Mathlib
import Proofs.SumOfDivisorsOQ01

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace SumOfDivisorsOQ01

/-- A positive natural number is a perfect square iff every exponent in its prime
factorization is even.  Pure factorization fact, independent of the
perfect-number context. -/
theorem isSquare_iff_even_factorization {N : ℕ} (hN : N ≠ 0) :
    IsSquare N ↔ ∀ p, Even (N.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p
    have hr : r ≠ 0 := by rintro rfl; simp at hN
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, rfl⟩
  · intro h
    refine ⟨N.factorization.prod fun p e => p ^ (e / 2), ?_⟩
    have key : (N.factorization.prod fun p e => p ^ (e / 2)) ^ 2 = N := by
      conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hN]
      simp only [Finsupp.prod]
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← pow_mul]
      congr 1
      obtain ⟨k, hk⟩ := h p
      omega
    rw [← key]; ring

/-- For an odd `N`, `σ(N)` is odd iff every prime in its factorization appears to
an even power.  Multiplicativity of `σ` (`isMultiplicative_sigma`) turns the
prime-power parity law L1 (`sigma_prime_pow_odd_iff`) into a statement about the
whole factorization. -/
theorem odd_sigma_iff_even_factorization {N : ℕ} (hodd : Odd N) (hN : N ≠ 0) :
    Odd (σ 1 N) ↔ ∀ p ∈ N.primeFactors, Even (N.factorization p) := by
  rw [(σ 1).multiplicative_factorization isMultiplicative_sigma hN]
  simp only [Finsupp.prod, Nat.support_factorization]
  rw [← not_even_iff_odd, even_iff_two_dvd,
    Nat.prime_two.prime.dvd_finset_prod_iff]
  push_neg
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hp_odd : Odd p := by
    rcases Nat.even_or_odd p with he | ho
    · exact absurd (even_iff_two_dvd.mpr (he.two_dvd.trans hpd))
        (not_even_iff_odd.mpr hodd)
    · exact ho
  rw [← even_iff_two_dvd, not_even_iff_odd]
  exact sigma_prime_pow_odd_iff hp_prime hp_odd _

/-- **σ-parity detects squares (odd case).**  For an odd `N`, `σ(N)` is odd ⟺ `N`
is a perfect square.  This is the odd case of the classical "σ(n) is odd iff n is
a square or twice a square", and the square-packaging half of Euler's odd-perfect
form: the part of `N` on which `σ` stays odd (the even-exponent primes) is a
square `m²`. -/
theorem odd_sigma_odd_iff_isSquare {N : ℕ} (hodd : Odd N) (hN : N ≠ 0) :
    Odd (σ 1 N) ↔ IsSquare N := by
  rw [odd_sigma_iff_even_factorization hodd hN, isSquare_iff_even_factorization hN]
  constructor
  · intro h p
    by_cases hp : p ∈ N.primeFactors
    · exact h p hp
    · have hz : N.factorization p = 0 := by
        rw [← Nat.support_factorization] at hp
        exact Finsupp.not_mem_support_iff.mp hp
      rw [hz]; exact even_zero
  · intro h p _; exact h p

/-- **An odd perfect number is never a perfect square.**  From `σ(N) = 2N` the
value `σ(N)` is even, so by the parity law `N` cannot be a square.  Equivalently:
in `N = p^a·m²` the special prime's exponent `a` is odd, so `p^a` is a non-square
factor and `N` itself is not a square. -/
theorem odd_perfect_not_isSquare {N : ℕ} (hodd : Odd N) (hperf : Nat.Perfect N) :
    ¬ IsSquare N := by
  have hN : N ≠ 0 := hperf.2.ne'
  rw [← odd_sigma_odd_iff_isSquare hodd hN, odd_perfect_sigma_eq_two_mul hperf]
  exact not_odd_iff_even.mpr ⟨N, by ring⟩

end SumOfDivisorsOQ01
