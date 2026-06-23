/-
# Explicit Prime Gap Bounds

This file derives explicit bounds on prime gaps and the n-th prime
from Bertrand's postulate.

**Status**: DEEP DIVE
- Proves pi(2n) >= pi(n) + 1 from Bertrand
- Computes small values of pi
- Proves the exponential bound p_n <= 2^(n+1) from Bertrand

**Key Results**:
- For n >= 1: pi(2n) > pi(n) (there's always a new prime when doubling)
- Computational: pi(10) = 4, pi(20) = 8, pi(30) = 10, pi(50) = 15
- The n-th prime satisfies p_n <= 2^(n+1) (proved from Bertrand)
-/

import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

namespace PrimeGapBounds

open Nat

/-
## Bertrand's Postulate Consequences

From Bertrand: for all n >= 1, there exists a prime p with n < p <= 2n.
-/

/-- Bertrand's postulate: there's a prime strictly between n and 2n (inclusive) -/
theorem bertrand_postulate (n : ℕ) (hn : n ≥ 1) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n (Nat.one_le_iff_ne_zero.mp hn)

/-
## Prime Counting Bounds

From Bertrand we derive bounds on the prime counting function.
-/

/-- The first prime is 2 -/
theorem first_prime : nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two

/-- The nth prime is prime. -/
lemma nth_prime_is_prime (n : ℕ) : Nat.Prime (nth Nat.Prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- pi(2n) > pi(n) for n >= 1: there's always a new prime when doubling -/
theorem primeCounting_double_gt (n : ℕ) (hn : n ≥ 1) :
    Nat.primeCounting (2 * n) > Nat.primeCounting n := by
  obtain ⟨p, hp_prime, hlt, hle⟩ := bertrand_postulate n hn
  unfold primeCounting primeCounting'
  have h1 : count Nat.Prime (n + 1) < count Nat.Prime (p + 1) := by
    have hmono : count Nat.Prime (n + 1) ≤ count Nat.Prime p := Nat.count_monotone _ (by omega)
    have hstrict : count Nat.Prime p < count Nat.Prime (p + 1) :=
      Nat.count_strict_mono hp_prime (Nat.lt_succ_self p)
    omega
  have h2 : count Nat.Prime (p + 1) ≤ count Nat.Prime (2 * n + 1) :=
    Nat.count_monotone _ (by omega)
  omega

/-- pi(2n) >= pi(n) + 1 -/
theorem primeCounting_double_ge_succ (n : ℕ) (hn : n ≥ 1) :
    Nat.primeCounting (2 * n) ≥ Nat.primeCounting n + 1 := by
  have := primeCounting_double_gt n hn
  omega

/-- Iterating: pi(2^k * n) >= pi(n) + k for n >= 1 -/
theorem primeCounting_pow_two_mul (n k : ℕ) (hn : n ≥ 1) :
    Nat.primeCounting (2^k * n) ≥ Nat.primeCounting n + k := by
  induction k with
  | zero => simp
  | succ j ih =>
    have h1 : 2^j * n ≥ 1 := by
      have hp : 2^j ≥ 1 := Nat.one_le_pow j 2 (by decide)
      calc 2^j * n ≥ 1 * n := Nat.mul_le_mul_right n hp
           _ = n := by ring
           _ ≥ 1 := hn
    have h2 : Nat.primeCounting (2^(j+1) * n) ≥ Nat.primeCounting (2^j * n) + 1 := by
      have : 2^(j+1) * n = 2 * (2^j * n) := by ring
      rw [this]
      exact primeCounting_double_ge_succ (2^j * n) h1
    calc Nat.primeCounting (2^(j+1) * n) ≥ Nat.primeCounting (2^j * n) + 1 := h2
         _ ≥ (Nat.primeCounting n + j) + 1 := by omega
         _ = Nat.primeCounting n + (j + 1) := by ring

/-
## Small Value Computations
-/

/-- pi(10) = 4 (primes: 2, 3, 5, 7) -/
theorem primeCounting_ten : Nat.primeCounting 10 = 4 := by decide

/-- pi(20) = 8 (primes: 2, 3, 5, 7, 11, 13, 17, 19) -/
theorem primeCounting_twenty : Nat.primeCounting 20 = 8 := by decide

/-- pi(30) = 10 -/
theorem primeCounting_thirty : Nat.primeCounting 30 = 10 := by decide

/-- pi(50) = 15 -/
theorem primeCounting_fifty : Nat.primeCounting 50 = 15 := by decide

/-- Verify Bertrand computationally: pi(20) > pi(10) -/
example : Nat.primeCounting 20 > Nat.primeCounting 10 := by
  rw [primeCounting_ten, primeCounting_twenty]
  decide

/-
## Exponential Bound on p_n (Proof from Bertrand)

From Bertrand, we prove p_n <= 2^(n+1) by induction.
The key insight: if p_n is the n-th prime, Bertrand gives a prime q with p_n < q <= 2*p_n.
Since p_{n+1} is the smallest prime > p_n, we get p_{n+1} <= q <= 2*p_n.
By induction, p_n <= 2^(n+1), so p_{n+1} <= 2*2^(n+1) = 2^(n+2).
-/

/-- Key lemma: if q is prime and greater than the n-th prime,
    then the (n+1)-th prime is at most q.
    This follows from nth being the order-preserving enumeration of primes. -/
lemma nth_prime_succ_le_of_prime_gt (n q : ℕ) (hq : Nat.Prime q)
    (hlt : nth Nat.Prime n < q) : nth Nat.Prime (n + 1) ≤ q := by
  by_contra h
  push_neg at h
  -- h : q < nth Nat.Prime (n + 1)
  -- count(q + 1) ≤ n + 1 (since q + 1 ≤ nth(n+1))
  have hcount_lt : Nat.count Nat.Prime (q + 1) ≤ n + 1 := by
    have hqle : q + 1 ≤ nth Nat.Prime (n + 1) := h
    have := Nat.count_monotone Nat.Prime hqle
    rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime] at this
    exact this
  -- count(q) ≥ n + 1 (since nth(n) + 1 ≤ q and nth(n) is prime)
  have hcount_ge : Nat.count Nat.Prime q ≥ n + 1 := by
    have h1 : Nat.count Nat.Prime (nth Nat.Prime n) = n :=
      Nat.count_nth_of_infinite Nat.infinite_setOf_prime n
    have h2 : Nat.count Nat.Prime (nth Nat.Prime n + 1) = n + 1 := by
      rw [Nat.count_succ, if_pos (nth_prime_is_prime n)]
      omega
    have h3 : nth Nat.Prime n + 1 ≤ q := by omega
    have h4 := Nat.count_monotone Nat.Prime h3
    omega
  -- count(q + 1) = count(q) + 1 since q is prime
  have hcount_succ : Nat.count Nat.Prime (q + 1) = Nat.count Nat.Prime q + 1 := by
    rw [Nat.count_succ, if_pos hq]
  omega

/-- **The n-th prime (0-indexed) is at most 2^(n+1).**

This is proved by induction using Bertrand's postulate:
- Base: p_0 = 2 ≤ 2^1 = 2
- Step: By Bertrand, ∃ q prime with p_k < q ≤ 2*p_k.
  Since p_{k+1} is the smallest prime > p_k, p_{k+1} ≤ q ≤ 2*p_k ≤ 2^{k+2}. -/
theorem nth_prime_le_two_pow_succ (n : ℕ) : nth Nat.Prime n ≤ 2^(n + 1) := by
  induction n with
  | zero =>
    rw [first_prime]
    norm_num
  | succ k ih =>
    have hpos : nth Nat.Prime k ≠ 0 := Nat.ne_of_gt (nth_prime_is_prime k).pos
    obtain ⟨q, hq_prime, hlt, hle⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (nth Nat.Prime k) hpos
    have h1 := nth_prime_succ_le_of_prime_gt k q hq_prime hlt
    calc nth Nat.Prime (k + 1) ≤ q := h1
      _ ≤ 2 * nth Nat.Prime k := hle
      _ ≤ 2 * 2^(k + 1) := by omega
      _ = 2^(k + 2) := by ring

/-- Corollary: p_n <= 2^n for 1-indexed primes -/
theorem nth_prime_le_two_pow (n : ℕ) (hn : n ≥ 1) : nth Nat.Prime (n - 1) ≤ 2^n := by
  have h := nth_prime_le_two_pow_succ (n - 1)
  simp only [Nat.sub_add_cancel hn] at h
  exact h

/-
## Consequences

The exponential bound gives explicit guarantees:
- p_0 = 2 ≤ 2
- p_1 = 3 ≤ 4
- p_2 = 5 ≤ 8
- p_9 = 29 ≤ 1024
- p_99 = 541 ≤ 2^100

Much tighter bounds (Dusart-type) like p_n <= n(ln n + ln ln n) require
analytic number theory not currently in Mathlib.

### Summary

This file proves:
1. Bertrand's postulate consequences for prime counting
2. pi(2n) > pi(n) for n >= 1
3. pi(2^k * n) >= pi(n) + k (iterated doubling)
4. Small values of pi verified computationally
5. **p_n <= 2^(n+1)** - proved from Bertrand (was previously an axiom)
6. Key lemma: nth_prime_succ_le_of_prime_gt (order-preserving enumeration property)

### Axioms: 0 (fully proved from Mathlib)
-/

end PrimeGapBounds
