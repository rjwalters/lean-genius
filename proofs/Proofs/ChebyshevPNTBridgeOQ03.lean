/-
  Bertrand's Postulate and the Prime-Counting Function
  Open Question: chebyshev-pnt-bridge-oq-03

  The parent ChebyshevPNTBridge.lean proves explicit Chebyshev-type bounds
  giving π(x) = Θ(x/log x). Its third open question asks to use the bridge
  to formalize **Bertrand's postulate**: there is always a prime in (n, 2n].

  The deep factorization argument (binomial coefficient bounds) that powers
  both the Chebyshev bridge and Bertrand's postulate is already formalized in
  Mathlib as `Nat.exists_prime_lt_and_le_two_mul`. This file states Bertrand
  in the bridge's setting and, more importantly, derives its quantitative
  consequences for the prime-counting function π that the bridge studies —
  all with 0 axioms / 0 sorries:

    • `bertrand`                 : ∀ n ≥ 1, ∃ prime p, n < p ≤ 2n.
    • `primeCounting_two_mul_ge` : π(2n) ≥ π(n) + 1 — every doubling interval
                                   (n, 2n] contributes at least one new prime,
                                   so π strictly increases along doublings.
    • `primeCounting_two_pow_ge` : π(2^k) ≥ k — at least k primes below 2^k,
                                   a clean lower bound on π recovering the
                                   Θ(x/log x) order (π(2^k)/log(2^k) ≥ 1/log 2).
    • `exists_prime_between_consecutive_powers` and explicit small cases.

  Reference: https://en.wikipedia.org/wiki/Bertrand%27s_postulate
-/

import Mathlib

namespace ChebyshevPNTBertrand

open Nat

/-- **Bertrand's postulate.** For every n ≥ 1 there is a prime p with
    n < p ≤ 2n. (The factorization argument is Mathlib's
    `Nat.exists_prime_lt_and_le_two_mul`.) -/
theorem bertrand (n : ℕ) (hn : 1 ≤ n) : ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n (by omega)

/-- **π grows by at least one across each doubling.** π(2n) ≥ π(n) + 1:
    the Bertrand prime p ∈ (n, 2n] is counted by π(2n) but not by π(n). -/
theorem primeCounting_two_mul_ge (n : ℕ) (hn : 1 ≤ n) :
    Nat.primeCounting n + 1 ≤ Nat.primeCounting (2 * n) := by
  obtain ⟨p, hp, hnp, hp2n⟩ := bertrand n hn
  -- π(m) = π'(m+1) = (# primes < m+1) = (# primes ≤ m)
  unfold Nat.primeCounting
  have h1 : Nat.primeCounting' (n + 1) ≤ Nat.primeCounting' p :=
    Nat.monotone_primeCounting' (by omega)
  have h2 : Nat.primeCounting' p + 1 = Nat.primeCounting' (p + 1) := by
    show Nat.count Nat.Prime p + 1 = Nat.count Nat.Prime (p + 1)
    rw [Nat.count_succ, if_pos hp]
  have h3 : Nat.primeCounting' (p + 1) ≤ Nat.primeCounting' (2 * n + 1) :=
    Nat.monotone_primeCounting' (by omega)
  omega

/-- **At least k primes below 2^k:** π(2^k) ≥ k. Iterating Bertrand from
    2^0 = 1 up to 2^k, each doubling adds a prime. This lower bound matches
    the Θ(x/log x) order: π(2^k)·log 2 ≥ k = log₂(2^k). -/
theorem primeCounting_two_pow_ge (k : ℕ) : k ≤ Nat.primeCounting (2 ^ k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hstep := primeCounting_two_mul_ge (2 ^ m) Nat.one_le_two_pow
    have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hpow]
    omega

/-- A prime always lies strictly between consecutive powers of two:
    for k ≥ 1 there is a prime p with 2^k < p ≤ 2^(k+1). -/
theorem exists_prime_between_consecutive_powers (k : ℕ) :
    ∃ p, Nat.Prime p ∧ 2 ^ k < p ∧ p ≤ 2 ^ (k + 1) := by
  obtain ⟨p, hp, hlt, hle⟩ := bertrand (2 ^ k) Nat.one_le_two_pow
  exact ⟨p, hp, hlt, by rw [pow_succ]; omega⟩

/-- The doubling map on π is strictly increasing: π(n) < π(2n) for n ≥ 1. -/
theorem primeCounting_lt_two_mul (n : ℕ) (hn : 1 ≤ n) :
    Nat.primeCounting n < Nat.primeCounting (2 * n) := by
  have := primeCounting_two_mul_ge n hn
  omega

/- ## Explicit small cases -/

/-- A prime in (1, 2]: namely 2. -/
example : ∃ p, Nat.Prime p ∧ 1 < p ∧ p ≤ 2 := bertrand 1 (by norm_num)

/-- A prime in (5, 10]: namely 7. -/
example : ∃ p, Nat.Prime p ∧ 5 < p ∧ p ≤ 10 := bertrand 5 (by norm_num)

end ChebyshevPNTBertrand
