import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# Cassini's Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
**Cassini's identity** is the exact relation

    Fₙ₊₂ · Fₙ − Fₙ₊₁² = (−1)ⁿ⁺¹      (over ℤ).

Equivalently, shifting the index, `Fₙ₋₁·Fₙ₊₁ − Fₙ² = (−1)ⁿ`.  It says that the
"determinant" of three consecutive Fibonacci numbers is always `±1`: the
product of the outer two differs from the square of the middle one by exactly
one, with a sign that alternates with `n`.

For example:
- `n = 1`: `F₃·F₁ − F₂² = 2·1 − 1 = 1  = (−1)²`
- `n = 2`: `F₄·F₂ − F₃² = 3·1 − 4 = −1 = (−1)³`
- `n = 3`: `F₅·F₃ − F₄² = 5·2 − 9 = 1  = (−1)⁴`
- `n = 4`: `F₆·F₄ − F₅² = 8·3 − 25 = −1 = (−1)⁵`

## Approach

Pure induction on `n`, cast to `ℤ` so the alternating sign `(−1)ⁿ⁺¹` is
available.  The recurrence `Nat.fib_add_two : Fₙ₊₂ = Fₙ + Fₙ₊₁` (cast to ℤ)
rewrites the three consecutive terms at step `n+1` into `Fₙ, Fₙ₊₁`, and a single
`linear_combination` against the induction hypothesis closes the algebra — the
key cancellation is `Fₙ₊₂·Fₙ − Fₙ₊₁² = −(Fₙ₊₃·Fₙ₊₁ − Fₙ₊₂²)`, i.e. the
left-hand side simply negates each step, which is exactly `(−1)ⁿ⁺¹ → (−1)ⁿ⁺²`.

No `decide`/`native_decide` is used, so the proof is axiom-free (only Mathlib's
foundational axioms).

## Distinctness

Cassini's identity is **not** in Mathlib (`Mathlib.Data.Nat.Fib.Basic` has the
recurrence, `fib_add`, `fib_two_mul`, `fib_gcd`, etc., but no `±1` determinant
identity), and there is no Fibonacci-identity entry in the gallery.  This is the
first of the `fibonacci-identities` family; `oq-02` (strong divisibility) and
`oq-03` (doubling) cover different identities.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01

open Nat

/-- **Cassini's identity.**  For every `n`, the integer determinant of three
consecutive Fibonacci numbers is `(−1)ⁿ⁺¹`:

    Fₙ₊₂ · Fₙ − Fₙ₊₁² = (−1)ⁿ⁺¹. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ k ih =>
    -- Recurrence, cast to ℤ, for the two terms introduced at the successor step.
    have e2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k)
    have e3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + Nat.fib (k + 2) := by
      exact_mod_cast Nat.fib_add_two (n := k + 1)
    -- Goal at `k+1`, with indices put in `k+3 / k+2` form (definitionally equal).
    show (Nat.fib (k + 3) : ℤ) * Nat.fib (k + 1) - (Nat.fib (k + 2) : ℤ) ^ 2 = (-1) ^ (k + 2)
    rw [e2] at ih
    rw [e3, e2, pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- **Cassini, index-shifted form.**  For `n ≥ 1`,

    Fₙ₋₁ · Fₙ₊₁ − Fₙ² = (−1)ⁿ.

Stated on `n + 1` to avoid natural-number subtraction:
`Fₙ · Fₙ₊₂ − Fₙ₊₁² = (−1)ⁿ⁺¹`. -/
theorem fib_cassini_shift (n : ℕ) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  have h := fib_cassini n
  linear_combination h

/-- The unsigned form: consecutive Fibonacci "determinants" have absolute value
exactly `1`. -/
theorem fib_cassini_abs (n : ℕ) :
    |(Nat.fib (n + 2) : ℤ) * Nat.fib n - (Nat.fib (n + 1) : ℤ) ^ 2| = 1 := by
  rw [fib_cassini n, abs_pow]
  simp

/-! ## Concrete examples (the first few determinants) -/

example : (Nat.fib 3 : ℤ) * Nat.fib 1 - (Nat.fib 2 : ℤ) ^ 2 = 1 := by decide
example : (Nat.fib 4 : ℤ) * Nat.fib 2 - (Nat.fib 3 : ℤ) ^ 2 = -1 := by decide
example : (Nat.fib 5 : ℤ) * Nat.fib 3 - (Nat.fib 4 : ℤ) ^ 2 = 1 := by decide
example : (Nat.fib 6 : ℤ) * Nat.fib 4 - (Nat.fib 5 : ℤ) ^ 2 = -1 := by decide

end FibonacciIdentitiesOQ01
