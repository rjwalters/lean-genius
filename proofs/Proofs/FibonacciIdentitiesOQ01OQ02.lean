import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# d'Ocagne's Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
**d'Ocagne's identity** is the exact relation, for `n ≤ m`,

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · Fₘ₋ₙ      (over ℤ).

It is the "off-diagonal" companion of Cassini's identity: where Cassini
(`oq-01`) measures the determinant of *consecutive* Fibonacci numbers, d'Ocagne
measures the cross-determinant of two arbitrarily-spaced Fibonacci pairs
`(Fₘ, Fₘ₊₁)` and `(Fₙ, Fₙ₊₁)`, and pins it to a single signed Fibonacci number
`±Fₘ₋ₙ`.

For example:
- `m = 3, n = 1`: `F₃·F₂ − F₄·F₁ = 2·1 − 3·1 = −1 = (−1)¹·F₂ = (−1)·1`
- `m = 4, n = 2`: `F₄·F₃ − F₅·F₂ = 3·2 − 5·1 = 1  = (−1)²·F₂ = 1·1`
- `m = 5, n = 2`: `F₅·F₃ − F₆·F₂ = 5·2 − 8·1 = 2  = (−1)²·F₃ = 1·2`

Cassini is the diagonal case `m = n + 1`: then `Fₘ₋ₙ = F₁ = 1`, giving
`Fₙ₊₁² − Fₙ₊₂·Fₙ = (−1)ⁿ` (see `fib_docagne_cassini` below).

## Approach

Reparametrise `m = n + k` (legal since `n ≤ m`) and prove the core lemma

    Fₙ₊ₖ · Fₙ₊₁ − Fₙ₊ₖ₊₁ · Fₙ = (−1)ⁿ · Fₖ

by induction on `n` with `k` fixed.  Writing `g(n)` for the left-hand side, the
two-term recurrence collapses the successor step to `g(n+1) = −g(n)`: expanding
`Fₙ₊₂ = Fₙ + Fₙ₊₁` and `Fₙ₊ₖ₊₂ = Fₙ₊ₖ + Fₙ₊ₖ₊₁` makes the `Fₙ₊₁`-terms cancel,
leaving exactly the negation of the previous determinant — which matches
`(−1)ⁿ → (−1)ⁿ⁺¹`.  A single `linear_combination (-1) * ih` discharges the
algebra.  The base case `n = 0` is `Fₖ·1 − Fₖ₊₁·0 = Fₖ`.

Everything is cast to `ℤ` so the alternating sign is available; no
`decide`/`native_decide` on the theorems, so the proof is axiom-free (only
Mathlib's foundational axioms).

## Distinctness

d'Ocagne's identity is **not** in Mathlib (`Mathlib.Data.Nat.Fib.Basic` has the
recurrence, the addition formula `Nat.fib_add`, `fib_two_mul`, `fib_gcd`, etc.,
but no cross-determinant identity).  It answers the second open question of the
Cassini entry `fibonacci-identities-oq-01` ("Prove d'Ocagne's identity").  The
sibling `oq-01-oq-01` covers Catalan's identity (the *diagonal* generalisation,
spacing `r` symmetric about `n`); this is the *asymmetric* two-index form, and
it specialises back to Cassini on the diagonal `m = n + 1`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01OQ02

open Nat

/-- **d'Ocagne core (additive form).**  For all `n k`,

    Fₙ₊ₖ · Fₙ₊₁ − Fₙ₊ₖ₊₁ · Fₙ = (−1)ⁿ · Fₖ.

This is d'Ocagne's identity with the spacing made explicit (`m = n + k`), which
sidesteps natural-number subtraction.  Proved by induction on `n`; each step
negates the determinant, giving the alternating sign. -/
theorem fib_docagne_aux (k n : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1) - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero => simp [Nat.fib_one, Nat.fib_zero]
  | succ j ih =>
    -- Recurrences (cast to ℤ) for the two terms introduced at the successor step.
    have hj2 : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + Nat.fib (j + 1) := by
      exact_mod_cast Nat.fib_add_two (n := j)
    have hjk2 : (Nat.fib (j + k + 2) : ℤ) = (Nat.fib (j + k) : ℤ) + Nat.fib (j + k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := j + k)
    -- Normalise the successor indices into the `j+k+1 / j+2 / j+k+2` forms.
    rw [show j + 1 + k = j + k + 1 from by omega,
        show j + 1 + 1 = j + 2 from by omega,
        show j + k + 1 + 1 = j + k + 2 from by omega]
    rw [hj2, hjk2, pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- **d'Ocagne's identity.**  For `n ≤ m`,

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · Fₘ₋ₙ. -/
theorem fib_docagne {m n : ℕ} (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n
      = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact fib_docagne_aux k n

/-- **Cassini as the diagonal of d'Ocagne.**  Taking `m = n + 1` (so `Fₘ₋ₙ = F₁ = 1`)
recovers Cassini's identity in the form `Fₙ₊₁² − Fₙ₊₂·Fₙ = (−1)ⁿ`. -/
theorem fib_docagne_cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib (n + 2) : ℤ) * Nat.fib n = (-1) ^ n := by
  have h := fib_docagne (m := n + 1) (n := n) (Nat.le_succ n)
  simp only [Nat.add_sub_cancel_left, Nat.fib_one] at h
  linear_combination h

/-- **Unsigned form.**  The cross-determinant of two Fibonacci pairs has absolute
value exactly `Fₘ₋ₙ`. -/
theorem fib_docagne_abs {m n : ℕ} (h : n ≤ m) :
    |(Nat.fib m : ℤ) * Nat.fib (n + 1) - (Nat.fib (m + 1) : ℤ) * Nat.fib n| = Nat.fib (m - n) := by
  rw [fib_docagne h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    Nat.abs_cast]

/-! ## Concrete examples -/

example : (Nat.fib 3 : ℤ) * Nat.fib 2 - (Nat.fib 4 : ℤ) * Nat.fib 1 = -1 := by decide
example : (Nat.fib 4 : ℤ) * Nat.fib 3 - (Nat.fib 5 : ℤ) * Nat.fib 2 = 1 := by decide
example : (Nat.fib 5 : ℤ) * Nat.fib 3 - (Nat.fib 6 : ℤ) * Nat.fib 2 = 2 := by decide
example : (Nat.fib 7 : ℤ) * Nat.fib 4 - (Nat.fib 8 : ℤ) * Nat.fib 3 = -3 := by decide

end FibonacciIdentitiesOQ01OQ02
