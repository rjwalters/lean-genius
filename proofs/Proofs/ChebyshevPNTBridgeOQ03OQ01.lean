/-
  A Pointwise Elementary Logarithmic Lower Bound on π
  Open Question: chebyshev-pnt-bridge-oq-03-oq-01

  The parent ChebyshevPNTBridgeOQ03.lean uses Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`) to show every doubling interval (n, 2n]
  contains a prime, and derives the lower bound

      π(2^k) ≥ k      (`ChebyshevPNTBertrand.primeCounting_two_pow_ge`)

  — at least k primes below 2^k. That statement only constrains π along the
  sparse sequence of powers of two.  This follow-up upgrades it to a bound that
  holds at **every** natural number:

      π(n) ≥ ⌊log₂ n⌋   for all n.

  The proof is one line of mathematics: monotonicity of π together with
  `2 ^ ⌊log₂ n⌋ ≤ n` transports the powers-of-two bound to arbitrary n.

  **Honest scope.**  This bound is deliberately *weaker* than the Chebyshev
  bound already in the gallery — `ChebyshevPNTBridge` proves π(n) = Θ(n / log n),
  so π(n) ≥ c·n/log n, which dwarfs ⌊log₂ n⌋.  The value of this file is not the
  strength of the estimate but its **provenance**: it is a clean, pointwise,
  fully *elementary* lower bound obtained from Bertrand alone — no primorial
  factorization, no real-analytic o(1) term — and it is the exact counting-side
  dual of the already-formalized ceiling on the k-th prime
  `PrimeGapBounds.nth_prime_le_two_pow_succ` (pₖ ≤ 2^(k+1)).  We re-export that
  dual here so the two elementary directions of the "bridge" sit side by side.

  The sharp asymptotic π(x)·log x / x → 1 (the full Prime Number Theorem)
  remains out of reach of the pinned Mathlib and is not attempted here.

  All results below are verified with **0 axioms / 0 sorries**.

  Reference: https://en.wikipedia.org/wiki/Bertrand%27s_postulate
-/

import Mathlib
import Proofs.ChebyshevPNTBridgeOQ03
import Proofs.PrimeGapBounds

namespace ChebyshevPNTBridgeOQ03OQ01

open Nat

/-- **π(n) ≥ ⌊log₂ n⌋ for every n.**  The parent file proves π(2^k) ≥ k only at
    powers of two; monotonicity of π together with `2 ^ (Nat.log 2 n) ≤ n`
    upgrades this to a bound valid at every natural number. -/
theorem primeCounting_ge_log2 (n : ℕ) :
    Nat.log 2 n ≤ Nat.primeCounting n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  -- Let k := ⌊log₂ n⌋.  Then 2^k ≤ n, so π(2^k) ≤ π(n); and π(2^k) ≥ k.
  have hle : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 hn.ne'
  calc Nat.log 2 n
      ≤ Nat.primeCounting (2 ^ Nat.log 2 n) :=
        ChebyshevPNTBertrand.primeCounting_two_pow_ge (Nat.log 2 n)
    _ ≤ Nat.primeCounting n := Nat.monotone_primeCounting hle

/-- **Counting-side dual, restated.**  The ceiling on the k-th prime
    pₖ ≤ 2^(k+1) is already formalized in `PrimeGapBounds`; we re-export it here
    so both elementary directions of the Bertrand bridge — a lower bound on the
    *count* of primes and an upper bound on the *size* of the k-th prime — are
    available together. -/
theorem nth_prime_le_two_pow_succ (k : ℕ) : Nat.nth Nat.Prime k ≤ 2 ^ (k + 1) :=
  PrimeGapBounds.nth_prime_le_two_pow_succ k

/-- The two elementary bounds are mutually consistent at powers of two:
    π(2^k) ≥ k while every prime pⱼ with j < k lies below 2^k.  Here we record
    the immediate consequence that `⌊log₂ (pₖ)⌋ ≤ k + 1`, i.e. the k-th prime is
    not much larger than the (k+1)-th power of two in log scale. -/
theorem log2_nth_prime_le (k : ℕ) : Nat.log 2 (Nat.nth Nat.Prime k) ≤ k + 1 := by
  have hle : Nat.nth Nat.Prime k ≤ 2 ^ (k + 1) := nth_prime_le_two_pow_succ k
  calc Nat.log 2 (Nat.nth Nat.Prime k)
      ≤ Nat.log 2 (2 ^ (k + 1)) := Nat.log_mono_right hle
    _ = k + 1 := by rw [Nat.log_pow (by norm_num)]

/- ## Explicit small cases -/

/-- π(8) ≥ 3: primes 2, 3, 5, 7 are all ≤ 8, and ⌊log₂ 8⌋ = 3. -/
example : 3 ≤ Nat.primeCounting 8 := by
  have h := primeCounting_ge_log2 8
  have e : Nat.log 2 8 = 3 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rwa [e] at h

/-- π(1000) ≥ 9: a clean elementary certificate that there are at least nine
    primes below 1000, since ⌊log₂ 1000⌋ = 9. -/
example : 9 ≤ Nat.primeCounting 1000 := by
  have h := primeCounting_ge_log2 1000
  have e : Nat.log 2 1000 = 9 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  rwa [e] at h

end ChebyshevPNTBridgeOQ03OQ01
