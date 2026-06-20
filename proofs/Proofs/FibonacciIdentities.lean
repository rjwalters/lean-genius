import Mathlib

/-!
# Fibonacci summation identities

Mathlib's `Nat.fib` library is rich in *pointwise* identities — the recurrence
`Nat.fib_add_two`, the addition formula `Nat.fib_add`, the doubling formulas
`Nat.fib_two_mul` / `Nat.fib_two_mul_add_one`, Cassini's identity
(`Int.fib_succ_mul_fib_pred_sub_fib_sq`), the gcd law `Nat.fib_gcd`, and the
Pascal-diagonal sum `Nat.fib_succ_eq_sum_choose`. What it does **not** record are
the classical *summation* identities for the Fibonacci numbers. This entry supplies
three of them, each a fully self-contained induction (no axioms, no `native_decide`):

* `fib_sum_sq` — the **sum of squares** telescopes into a single product:
  `F₀² + F₁² + ⋯ + Fₙ² = Fₙ · Fₙ₊₁`. Geometrically this is the dissection of an
  `Fₙ × Fₙ₊₁` rectangle into squares of side `F₀, …, Fₙ`.

* `fib_sum_odd` — the **odd-indexed** Fibonacci numbers sum to an even-indexed one:
  `F₁ + F₃ + ⋯ + F₂ₙ₋₁ = F₂ₙ`.

* `fib_sum_even` — the **even-indexed** Fibonacci numbers sum (off by one) to an
  odd-indexed one: `(F₂ + F₄ + ⋯ + F₂ₙ) + 1 = F₂ₙ₊₁` (stated additively to stay
  inside `ℕ`).

The only Fibonacci fact used is the defining recurrence `Nat.fib_add_two`; everything
else is `Finset.sum_range_succ` plus `ring`.

No axioms, no sorries.
-/

namespace FibonacciIdentities

open Finset

/-- **Sum of squares of Fibonacci numbers.**
`F₀² + F₁² + ⋯ + Fₙ² = Fₙ · Fₙ₊₁`. The partial sums of `Fᵢ²` telescope, since
`Fₙ · Fₙ₊₁ − Fₙ₋₁ · Fₙ = Fₙ(Fₙ₊₁ − Fₙ₋₁) = Fₙ · Fₙ = Fₙ²`. -/
theorem fib_sum_sq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.fib i ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show k + 1 + 1 = k + 2 from rfl, Nat.fib_add_two]
    ring

/-- **Sum of the odd-indexed Fibonacci numbers.**
`F₁ + F₃ + ⋯ + F₂ₙ₋₁ = F₂ₙ`. -/
theorem fib_sum_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, Nat.fib (2 * i + 1) = Nat.fib (2 * n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (k + 1) = 2 * k + 2 from by ring,
      Nat.fib_add_two]

/-- **Sum of the even-indexed Fibonacci numbers** (additive form, to stay in `ℕ`).
`(F₂ + F₄ + ⋯ + F₂ₙ) + 1 = F₂ₙ₊₁`. -/
theorem fib_sum_even (n : ℕ) :
    (∑ i ∈ Finset.range n, Nat.fib (2 * i + 2)) + 1 = Nat.fib (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h : Nat.fib (2 * (k + 1) + 1) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by ring, Nat.fib_add_two,
        show (2 * k + 1) + 1 = 2 * k + 2 from by ring]
    rw [h]
    omega

end FibonacciIdentities
