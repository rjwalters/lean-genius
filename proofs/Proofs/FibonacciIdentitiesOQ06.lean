import Mathlib

/-!
# Fibonacci summation identities, continued — the linear (degree-one) sums

The parent entry `FibonacciIdentities` records the *quadratic* telescoping sum
(`fib_sum_sq`, `F₀²+⋯+Fₙ² = Fₙ·Fₙ₊₁`) and the *parity-filtered* sums of the
Fibonacci numbers themselves (`fib_sum_odd`, `fib_sum_even`). Curiously, the two
most elementary *linear* summation identities are absent from both that file and
its open-question descendants (which instead cover Cassini/Vajda/d'Ocagne,
divisibility/`gcd`, and the bilinear product sums `∑ Fᵢ·Fᵢ₊₁`, `∑ Fᵢ·Fᵢ₊₂`). This
entry supplies them, each a short `Finset.sum_range_succ` induction whose only
Fibonacci input is the defining recurrence `Nat.fib_add_two`.

* `fib_sum` — the **partial sum** telescopes to a single Fibonacci number:
  `F₀ + F₁ + ⋯ + Fₙ = Fₙ₊₂ − 1`. Stated additively (`(∑ Fᵢ) + 1 = Fₙ₊₂`) to stay
  inside `ℕ`. This is the discrete antiderivative of the recurrence: each `Fᵢ`
  equals `Fᵢ₊₂ − Fᵢ₊₁`, so the sum collapses.

* `fib_weighted_sum` — the **index-weighted sum** (a discrete "first moment"):
  `0·F₀ + 1·F₁ + 2·F₂ + ⋯ + n·Fₙ = n·Fₙ₊₂ − Fₙ₊₃ + 2`. Again stated additively,
  `(∑ i·Fᵢ) + Fₙ₊₃ = n·Fₙ₊₂ + 2`, to remain in `ℕ`. This is the Fibonacci analogue
  of `∑ i·rⁱ`; it is *not* a special case of any sibling identity, since the
  summand carries the running index `i` as a coefficient.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ06

open Finset

/-- **Partial sum of the Fibonacci numbers** (additive form, to stay in `ℕ`).
`(F₀ + F₁ + ⋯ + Fₙ) + 1 = Fₙ₊₂`, equivalently `∑_{i≤n} Fᵢ = Fₙ₊₂ − 1`.
The sum telescopes: `Fᵢ = Fᵢ₊₂ − Fᵢ₊₁`. -/
theorem fib_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), Nat.fib i) + 1 = Nat.fib (n + 2) := by
  induction n with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one]; decide
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hrec : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two
    omega

/-- **Index-weighted sum of the Fibonacci numbers** (additive form, to stay in `ℕ`).
`(0·F₀ + 1·F₁ + ⋯ + n·Fₙ) + Fₙ₊₃ = n·Fₙ₊₂ + 2`, equivalently
`∑_{i≤n} i·Fᵢ = n·Fₙ₊₂ − Fₙ₊₃ + 2`. The discrete first moment of the Fibonacci
sequence. -/
theorem fib_weighted_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), i * Nat.fib i) + Nat.fib (n + 3)
      = n * Nat.fib (n + 2) + 2 := by
  induction n with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one]; decide
  | succ k ih =>
    have e3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two
    have e2 : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) :=
      Nat.fib_add_two
    have e4 : Nat.fib (k + 1 + 3)
        = Nat.fib (k + 2) + (Nat.fib (k + 1) + Nat.fib (k + 2)) := by
      have h : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) :=
        Nat.fib_add_two
      rw [h, e3]
    rw [Finset.sum_range_succ, e4, e2]
    rw [e3] at ih
    zify at ih ⊢
    linear_combination ih

end FibonacciIdentitiesOQ06
