import Proofs.GCDAlgorithmOQ01
import Mathlib.Tactic

/-
# Removing the 10^20 Restriction from Lamé's 5-Digit Bound

## Research Problem: gcd-algorithm-oq-01-oq-03
Can the 5-digit bound be extended beyond b < 10^20?

## What This Proves
The existing GCDAlgorithmOQ01.lean proves Lamé's 5-digit bound
(euclideanSteps a b ≤ 5 * decimalDigits b) only for b < 10^20,
using interval_cases + native_decide to verify fib(5k+2) ≥ 10^k for k ≤ 20.

This file removes the restriction entirely by proving fib(5k+2) ≥ 10^k
for ALL k, using only Fibonacci recurrence identities:

**Key identity**: fib(n+5) = 5·fib(n+1) + 3·fib(n)
**Growth bound**: fib(5k+7) ≥ 10·fib(5k+2)
**Main result**: fib(5k+2) ≥ 10^k for all k

No golden ratio, no real analysis — pure natural number arithmetic.

## Status
- [x] Five-step Fibonacci identity
- [x] Multiplicative growth: fib(5(k+1)+2) ≥ 10·fib(5k+2)
- [x] Main bound: fib(5k+2) ≥ 10^k for all k
- [x] Generalized Lamé 5-digit bound (no restriction on b)
- Axiom count: 0
- Sorry count: 0
-/

namespace GCDAlgorithmOQ01OQ03

open Nat GCDAlgorithmOQ01

/-! ## The Five-Step Fibonacci Identity -/

/-- The five-step Fibonacci identity: fib(n+5) = 5·fib(n+1) + 3·fib(n).
    Derived from four instances of fib(n+2) = fib(n) + fib(n+1). -/
theorem fib_add_five (n : ℕ) : fib (n + 5) = 5 * fib (n + 1) + 3 * fib n := by
  have h2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := by
    exact fib_add_two
  have h4 : fib (n + 4) = fib (n + 2) + fib (n + 3) := by
    exact fib_add_two
  have h5 : fib (n + 5) = fib (n + 3) + fib (n + 4) := by
    exact fib_add_two
  omega

/-! ## The Multiplicative Growth Step -/

/-- The multiplicative growth: fib(5k+7) ≥ 10·fib(5k+2).
    Uses: fib(5k+7) = 8·fib(5k+2) + 5·fib(5k+1), and
    5·fib(5k+1) ≥ 2·fib(5k+2) since 3·fib(5k+1) ≥ 2·fib(5k). -/
theorem fib_five_step_growth (k : ℕ) : 10 * fib (5 * k + 2) ≤ fib (5 * k + 7) := by
  -- Unfold fib(5k+7) down to fib(5k) and fib(5k+1)
  have h1 : fib (5 * k + 2) = fib (5 * k) + fib (5 * k + 1) := fib_add_two
  have h2 : fib (5 * k + 3) = fib (5 * k + 1) + fib (5 * k + 2) := by
    exact fib_add_two
  have h3 : fib (5 * k + 4) = fib (5 * k + 2) + fib (5 * k + 3) := by
    exact fib_add_two
  have h4 : fib (5 * k + 5) = fib (5 * k + 3) + fib (5 * k + 4) := by
    exact fib_add_two
  have h5 : fib (5 * k + 6) = fib (5 * k + 4) + fib (5 * k + 5) := by
    exact fib_add_two
  have h6 : fib (5 * k + 7) = fib (5 * k + 5) + fib (5 * k + 6) := by
    exact fib_add_two
  -- Monotonicity: fib(5k) ≤ fib(5k+1)
  have hmono : fib (5 * k) ≤ fib (5 * k + 1) := Nat.fib_mono (by omega)
  omega

/-! ## Main Bound: fib(5k+2) ≥ 10^k for All k -/

/-- **fib(5k+2) ≥ 10^k for all k** (no restriction).
    Proved by induction using the multiplicative growth step. -/
theorem fib_ge_pow10_general (k : ℕ) : 10 ^ k ≤ fib (5 * k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hgrowth := fib_five_step_growth k
    have hindex : 5 * k + 7 = 5 * (k + 1) + 2 := by omega
    calc 10 ^ (k + 1) = 10 * 10 ^ k := by ring
      _ ≤ 10 * fib (5 * k + 2) := Nat.mul_le_mul_left 10 ih
      _ ≤ fib (5 * k + 7) := hgrowth
      _ = fib (5 * (k + 1) + 2) := by rw [hindex]

/-! ## Generalized Lamé 5-Digit Bound -/

/-- **Lamé's 5-Digit Bound (unrestricted)**: For any b > 0,
    euclideanSteps a b ≤ 5 × decimalDigits(b).

    This generalizes the original bound from b < 10^20 to all b. -/
theorem lame_five_digit_bound_general (a b : ℕ) (hb : 0 < b) :
    euclideanSteps a b ≤ 5 * decimalDigits b := by
  unfold decimalDigits
  set d := Nat.log 10 b
  apply lame_step_bound a b hb
  have hb_lt : b < 10 ^ (d + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 10) b
  have hfib : 10 ^ (d + 1) ≤ fib (5 * (d + 1) + 2) := fib_ge_pow10_general (d + 1)
  omega

-- Verify
example : euclideanSteps 48 18 ≤ 5 * decimalDigits 18 := by native_decide
example : euclideanSteps 1000 373 ≤ 5 * decimalDigits 373 := by native_decide

end GCDAlgorithmOQ01OQ03
