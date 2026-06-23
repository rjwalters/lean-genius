/-
  Prime Reciprocal Divergence — OQ-01: the prime zeta convergence dichotomy

  The gallery entry `PrimeReciprocalDivergence` proves `∑_p 1/p` diverges and, on the
  convergence side, the isolated facts that `∑_p 1/p²` converges and (in `p^r` form)
  the `Nat.Primes.summable_rpow` dichotomy.  Its OQ-01 asks for the *precise error
  term* of `∑_{p≤n} 1/p = ln ln n + M + E(n)` — a Mertens-type result requiring
  analytic number theory well beyond Mathlib.  Short of that, this file records the
  clean convergence/divergence boundary of the **prime zeta function**
  `P(s) = ∑_p 1/p^s`, the standard `1/p^s` packaging that the surrounding convergence
  questions all reduce to:

  * `prime_zeta_summable_iff` — `∑_p 1/p^s` is summable **iff** `s > 1`.
  * `prime_zeta_summable` / `prime_zeta_not_summable` — the two directions.
  * `prime_reciprocal_not_summable_rpow` — the `s = 1` boundary case (the gallery's
    divergence headline, in `1/p^s` form).
  * `prime_squared_summable` — `∑_p 1/p²` recovered as the `s = 2` instance.

  All results are fully machine-checked (0 axioms, 0 sorries), reducing to Mathlib's
  `Nat.Primes.summable_rpow`.

  Reference: Mertens (1874); https://erdosproblems.com (prime reciprocal sum).
-/

import Mathlib

open scoped Real

namespace PrimeReciprocalDivergenceOQ01

/-- **Prime zeta convergence dichotomy.**  The prime zeta series
    `P(s) = ∑_p 1/p^s` is summable **iff** `s > 1`.  Reduces to
    `Nat.Primes.summable_rpow` via `1/p^s = p^(−s)`. -/
theorem prime_zeta_summable_iff (s : ℝ) :
    Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ s) ↔ 1 < s := by
  have hfun : (fun p : Nat.Primes => 1 / (p : ℝ) ^ s)
      = (fun p : Nat.Primes => (p : ℝ) ^ (-s)) := by
    funext p
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    rw [Real.rpow_neg hp.le, one_div]
  rw [hfun, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **Convergence for `s > 1`.** -/
theorem prime_zeta_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ s) :=
  (prime_zeta_summable_iff s).mpr hs

/-- **Divergence for `s ≤ 1`.** -/
theorem prime_zeta_not_summable {s : ℝ} (hs : s ≤ 1) :
    ¬ Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ s) := by
  intro h
  have := (prime_zeta_summable_iff s).mp h
  linarith

/-- **The `s = 1` boundary**: the prime reciprocal series diverges — the gallery's
    headline, here as the critical exponent of the prime zeta function. -/
theorem prime_reciprocal_not_summable_rpow :
    ¬ Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ (1 : ℝ)) :=
  prime_zeta_not_summable (le_refl 1)

/-- **The `s = 2` instance**: `∑_p 1/p²` converges (the prime analogue of the Basel
    sum), recovered from the dichotomy. -/
theorem prime_squared_summable :
    Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ (2 : ℝ)) :=
  prime_zeta_summable (by norm_num)

end PrimeReciprocalDivergenceOQ01
