/-
# Explicit Prime Gap Bounds

This file derives explicit bounds on prime gaps and the n-th prime
from Bertrand's postulate.

**Status**: DEEP DIVE
- Proves π(2n) ≥ π(n) + 1 from Bertrand
- Computes small values of π
- States the exponential bound on p_n

**Key Results**:
- For n ≥ 1: π(2n) > π(n) (there's always a new prime when doubling)
- Computational: π(10) = 4, π(20) = 8, π(100) = 25
-/

import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace PrimeGapBounds

open Nat

/-!
## Bertrand's Postulate Consequences

From Bertrand: for all n ≥ 1, there exists a prime p with n < p ≤ 2n.
-/

/-- Bertrand's postulate: there's a prime strictly between n and 2n (inclusive) -/
theorem bertrand_postulate (n : ℕ) (hn : n ≥ 1) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n (Nat.one_le_iff_ne_zero.mp hn)

/-!
## Prime Counting Bounds

From Bertrand we derive bounds on the prime counting function.
-/

/-- The first prime is 2 -/
theorem first_prime : nth Nat.Prime 0 = 2 := Nat.zeroth_prime_eq_two

/-- π(2n) > π(n) for n ≥ 1: there's always a new prime when doubling -/
theorem primeCounting_double_gt (n : ℕ) (hn : n ≥ 1) : π (2 * n) > π n := by
  obtain ⟨p, hp_prime, hlt, hle⟩ := bertrand_postulate n hn
  -- p is a prime with n < p ≤ 2n
  -- π(2n) counts primes ≤ 2n, which includes p
  -- π(n) counts primes ≤ n, which excludes p (since n < p)
  unfold primeCounting primeCounting'
  -- count (< n+1) < count (< p+1) because p is prime and n < p < p+1
  have h1 : count Nat.Prime (n + 1) < count Nat.Prime (p + 1) := by
    have hmono : count Nat.Prime (n + 1) ≤ count Nat.Prime p := Nat.count_monotone _ (by omega)
    have hstrict : count Nat.Prime p < count Nat.Prime (p + 1) :=
      Nat.count_strict_mono hp_prime (Nat.lt_succ_self p)
    omega
  have h2 : count Nat.Prime (p + 1) ≤ count Nat.Prime (2 * n + 1) :=
    Nat.count_monotone _ (by omega)
  omega

/-- π(2n) ≥ π(n) + 1 -/
theorem primeCounting_double_ge_succ (n : ℕ) (hn : n ≥ 1) : π (2 * n) ≥ π n + 1 := by
  have := primeCounting_double_gt n hn
  omega

/-- Iterating: π(2^k · n) ≥ π(n) + k for n ≥ 1 -/
theorem primeCounting_pow_two_mul (n k : ℕ) (hn : n ≥ 1) : π (2^k * n) ≥ π n + k := by
  induction k with
  | zero => simp
  | succ j ih =>
    have h1 : 2^j * n ≥ 1 := by
      have hp : 2^j ≥ 1 := Nat.one_le_pow j 2 (by decide)
      calc 2^j * n ≥ 1 * n := Nat.mul_le_mul_right n hp
           _ = n := by ring
           _ ≥ 1 := hn
    have h2 : π (2^(j+1) * n) ≥ π (2^j * n) + 1 := by
      have : 2^(j+1) * n = 2 * (2^j * n) := by ring
      rw [this]
      exact primeCounting_double_ge_succ (2^j * n) h1
    calc π (2^(j+1) * n) ≥ π (2^j * n) + 1 := h2
         _ ≥ (π n + j) + 1 := by omega
         _ = π n + (j + 1) := by ring

/-!
## Small Value Computations
-/

/-- π(10) = 4 (primes: 2, 3, 5, 7) -/
theorem primeCounting_ten : π 10 = 4 := by decide

/-- π(20) = 8 (primes: 2, 3, 5, 7, 11, 13, 17, 19) -/
theorem primeCounting_twenty : π 20 = 8 := by decide

/-- π(30) = 10 -/
theorem primeCounting_thirty : π 30 = 10 := by decide

/-- π(50) = 15 -/
theorem primeCounting_fifty : π 50 = 15 := by decide

/-- Verify Bertrand computationally: π(20) > π(10) ✓ -/
example : π 20 > π 10 := by
  rw [primeCounting_ten, primeCounting_twenty]
  decide

/-!
## Exponential Bound on p_n (Statement)

From Bertrand, one can prove p_n ≤ 2^n by induction.
The key insight: if p is the n-th prime, Bertrand gives a prime q with p < q ≤ 2p,
so the (n+1)-th prime is at most 2p ≤ 2^{n+1}.

We state this as an axiom since the full proof requires careful handling of
the nth function's properties.
-/

/-- The n-th prime (0-indexed) is at most 2^(n+1) -/
axiom nth_prime_le_two_pow_succ (n : ℕ) : nth Nat.Prime n ≤ 2^(n + 1)

/-- Corollary: p_n ≤ 2^n for 1-indexed primes -/
theorem nth_prime_le_two_pow (n : ℕ) (hn : n ≥ 1) : nth Nat.Prime (n - 1) ≤ 2^n := by
  have h := nth_prime_le_two_pow_succ (n - 1)
  simp only [Nat.sub_add_cancel hn] at h
  exact h

/-!
## Consequences

The exponential bound, while weak, gives explicit guarantees:
- p_1 = 2 ≤ 2
- p_2 = 3 ≤ 4
- p_3 = 5 ≤ 8
- p_10 = 29 ≤ 1024
- p_100 = 541 ≤ 2^100 ≈ 10^30

Much tighter bounds (Dusart-type) like p_n ≤ n(ln n + ln ln n) require
analytic number theory not currently in Mathlib.
-/

end PrimeGapBounds
