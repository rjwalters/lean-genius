import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# d'Ocagne's Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
**d'Ocagne's identity** is the exact two-index relation

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · Fₘ₋ₙ      (m ≥ n, over ℤ).

It expresses the `2×2` "cross determinant" of two windows of the Fibonacci
sequence in terms of a single Fibonacci number `Fₘ₋ₙ`, with a sign that
alternates with `n`.  It is the genuine two-parameter generalisation of
Cassini's identity, which is the special case `m = n + 1`
(`Fₙ₊₁² − Fₙ₊₂·Fₙ = (−1)ⁿ`, since `F₁ = 1`).

To avoid natural-number subtraction, the headline lemma is phrased with the
gap `d = m − n` made explicit, `m = n + d`:

    F_{n+d} · F_{n+1} − F_{n+d+1} · F_n = (−1)ⁿ · F_d.

For example (`n = 1`):
- `d = 1`: `F₂·F₂ − F₃·F₁ = 1·1 − 2·1 = −1 = (−1)¹·F₁`
- `d = 2`: `F₃·F₂ − F₄·F₁ = 2·1 − 3·1 = −1 = (−1)¹·F₂`
- `d = 3`: `F₄·F₂ − F₅·F₁ = 3·1 − 5·1 = −2 = (−1)¹·F₃`

## Approach

Pure induction on `n` (with the gap `d` held fixed), cast to `ℤ` so the
alternating sign `(−1)ⁿ` is available.  The base case `n = 0` is immediate
(`F₀ = 0`, `F₁ = 1`).  In the successor step the recurrence
`Nat.fib_add_two : Fₖ₊₂ = Fₖ + Fₖ₊₁` (cast to ℤ) rewrites the two terms
introduced at `n = k+1` — both the inner index `k+2` and the shifted index
`k+d+2` — and a single `linear_combination (-1) * ih` closes the algebra: each
step negates the previous determinant, which is exactly `(−1)ᵏ → (−1)ᵏ⁺¹`.  The
key cancellation is `F_{k+d+1}·F_{k+1} − F_{k+d}·F_{k+2}` collapsing (via the
two recurrences) to `−(F_{k+d}·F_{k+1} − F_{k+d+1}·F_k)`.

No `decide`/`native_decide` is used, so the proof is axiom-free (only Mathlib's
foundational axioms).

## Distinctness

This is the second open question of the `fibonacci-identities-oq-01` (Cassini)
entry.  Mathlib has the recurrence, `fib_add`, `fib_two_mul`, `fib_gcd`, etc.,
but **no** d'Ocagne (cross-window determinant) identity, and the parent entry
proves only Cassini (`m = n + 1`).  The sibling `oq-01-oq-01` covers Catalan's
identity (`F_{n−r}·F_{n+r} − Fₙ²`), a *single*-window generalisation; d'Ocagne
is the *two*-window cross identity, and the final theorem here shows Cassini is
its `d = 1` specialisation.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01OQ02

open Nat

/-- **d'Ocagne's identity** (gap form, `m = n + d`).  For all `n d : ℕ`,

    F_{n+d} · F_{n+1} − F_{n+d+1} · F_n = (−1)ⁿ · F_d. -/
theorem fib_docagne (n d : ℕ) :
    (Nat.fib (n + d) : ℤ) * Nat.fib (n + 1)
      - (Nat.fib (n + d + 1) : ℤ) * Nat.fib n = (-1) ^ n * Nat.fib d := by
  induction n with
  | zero => simp [Nat.fib_zero, Nat.fib_one]
  | succ k ih =>
    -- Normalise the indices appearing at the successor step.
    have idx3 : k + 1 + d + 1 = k + d + 2 := by omega
    have idx1 : k + 1 + d = k + d + 1 := by omega
    have idx2 : k + 1 + 1 = k + 2 := by omega
    rw [idx3, idx1, idx2]
    -- The two Fibonacci terms introduced at this step, via the recurrence.
    have e1 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k)
    have e2 : (Nat.fib (k + d + 2) : ℤ) = Nat.fib (k + d) + Nat.fib (k + d + 1) := by
      exact_mod_cast Nat.fib_add_two (n := k + d)
    rw [pow_succ, e1, e2]
    linear_combination (-1 : ℤ) * ih

/-- **d'Ocagne's identity** (classical form).  For `n ≤ m`,

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · F_{m−n}. -/
theorem fib_docagne_le (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1)
      - (Nat.fib (m + 1) : ℤ) * Nat.fib n = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact fib_docagne n d

/-- **Cassini is the `d = 1` case of d'Ocagne.**  Specialising the gap to `1`
(`F₁ = 1`) recovers Cassini's identity `Fₙ₊₁² − Fₙ₊₂·Fₙ = (−1)ⁿ`. -/
theorem fib_cassini_via_docagne (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib (n + 2) * Nat.fib n = (-1) ^ n := by
  have h := fib_docagne n 1
  rw [Nat.fib_one, Nat.cast_one, mul_one] at h
  have e : (Nat.fib (n + 1 + 1) : ℤ) = Nat.fib (n + 2) := by rfl
  rw [e] at h
  linear_combination h

/-! ## Concrete examples -/

-- `n = 1, d = 1`: `F₂·F₂ − F₃·F₁ = −1`
example : (Nat.fib 2 : ℤ) * Nat.fib 2 - (Nat.fib 3 : ℤ) * Nat.fib 1 = -1 := by decide
-- `n = 1, d = 3`: `F₄·F₂ − F₅·F₁ = −F₃ = −2`
example : (Nat.fib 4 : ℤ) * Nat.fib 2 - (Nat.fib 5 : ℤ) * Nat.fib 1 = -(Nat.fib 3 : ℤ) := by decide
-- `n = 2, d = 2`: `F₄·F₃ − F₅·F₂ = F₂ = 1`
example : (Nat.fib 4 : ℤ) * Nat.fib 3 - (Nat.fib 5 : ℤ) * Nat.fib 2 = (Nat.fib 2 : ℤ) := by decide

end FibonacciIdentitiesOQ01OQ02
