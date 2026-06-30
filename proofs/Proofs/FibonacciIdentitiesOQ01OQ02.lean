import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# d'Ocagne's Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
**d'Ocagne's identity** is the two-index relation

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · Fₘ₋ₙ      (over ℤ, for m ≥ n).

It generalises Cassini's identity (`fibonacci-identities-oq-01`), which is the
special case `m = n + 1`:  `Fₙ₊₁² − Fₙ₊₂·Fₙ = (−1)ⁿ·F₁ = (−1)ⁿ`.

The natural-number subtraction `m − n` is the only obstruction to a fully
two-sided statement, so the clean engine is the **gap-parameterised form**: with
`k = m − n ≥ 0`,

    F_{n+k} · Fₙ₊₁ − F_{n+k+1} · Fₙ = (−1)ⁿ · F_k.

Here `k` is a genuine natural number and no subtraction appears.  The named
identity above is recovered by writing `m = n + k`.

For example (named form, `(−1)ⁿ·Fₘ₋ₙ`):
- `m = 3, n = 1`: `F₃·F₂ − F₄·F₁ = 2·1 − 3·1 = −1 = (−1)¹·F₂ = −1`
- `m = 5, n = 2`: `F₅·F₃ − F₆·F₂ = 5·2 − 8·1 =  2 = (−1)²·F₃ =  2`
- `m = 4, n = 1`: `F₄·F₂ − F₅·F₁ = 3·1 − 5·1 = −2 = (−1)¹·F₃ = −2`

## Approach

Pure induction on `n` in the gap-parameterised form, cast to `ℤ`.  The crux is
that the successor step simply **negates** the previous value:

    F_{n+k}·Fₙ₊₁ − F_{n+k+1}·Fₙ  =  −(F_{n+k+1}·Fₙ₊₂ − F_{n+k+2}·Fₙ₊₁),

which is exactly `(−1)ⁿ·F_k → (−1)ⁿ⁺¹·F_k`.  After rewriting the two terms
introduced at the successor step with the recurrence `Nat.fib_add_two` (cast to
ℤ), a single `linear_combination (-1) * ih` closes the algebra — the same
"one sign flip per step" mechanism that drives Cassini.  No closed form, Binet
formula, or matrices are needed; the only input beyond base values is the
recurrence.

No `decide`/`native_decide` is used in the theorems, so the proofs are
axiom-free (only Mathlib's foundational axioms).

## Distinctness

d'Ocagne's identity is **not** in Mathlib (`Mathlib.Data.Nat.Fib.Basic` has the
recurrence, `fib_add`, `fib_two_mul`, `fib_gcd`, etc., but no two-index ±Fₖ
determinant identity).  It is the second open question of
`fibonacci-identities-oq-01` (Cassini) and properly generalises that parent:
`fib_cassini_of_docagne` re-derives Cassini as the `m = n + 1` slice.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01OQ02

open Nat

/-- **d'Ocagne's identity, gap-parameterised form.**  For every `n` and every
gap `k`,

    F_{n+k} · Fₙ₊₁ − F_{n+k+1} · Fₙ = (−1)ⁿ · F_k.

This is the subtraction-free engine: `k` plays the role of `m − n`. -/
theorem fib_docagne_gap (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1)
      - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n = (-1) ^ n * Nat.fib k := by
  induction n with
  | zero =>
    -- F_k·F₁ − F_{k+1}·F₀ = F_k·1 − F_{k+1}·0 = F_k.
    simp [Nat.fib_zero, Nat.fib_one]
  | succ n ih =>
    -- The only non-definitional index normalisation: `n+1+k = n+k+1`.
    have i1 : n + 1 + k = n + k + 1 := by ring
    rw [i1]
    -- Remaining indices `n+k+1+1`, `n+1+1` are definitionally `n+k+2`, `n+2`.
    show (Nat.fib (n + k + 1) : ℤ) * Nat.fib (n + 2)
        - (Nat.fib (n + k + 2) : ℤ) * Nat.fib (n + 1) = (-1) ^ (n + 1) * Nat.fib k
    -- Recurrences, cast to ℤ, for the two terms introduced at the successor step.
    have e2 : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + Nat.fib (n + 1) := by
      exact_mod_cast Nat.fib_add_two (n := n)
    have e4 : (Nat.fib (n + k + 2) : ℤ) = (Nat.fib (n + k) : ℤ) + Nat.fib (n + k + 1) := by
      exact_mod_cast Nat.fib_add_two (n := n + k)
    rw [e2, e4, pow_succ]
    linear_combination (-1 : ℤ) * ih

/-- **d'Ocagne's identity (named two-index form).**  For `m ≥ n`,

    Fₘ · Fₙ₊₁ − Fₘ₊₁ · Fₙ = (−1)ⁿ · Fₘ₋ₙ. -/
theorem fib_docagne (m n : ℕ) (h : n ≤ m) :
    (Nat.fib m : ℤ) * Nat.fib (n + 1)
      - (Nat.fib (m + 1) : ℤ) * Nat.fib n = (-1) ^ n * Nat.fib (m - n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact fib_docagne_gap n k

/-- **Cassini as a special case of d'Ocagne.**  Taking `m = n + 1` (gap `1`,
`F₁ = 1`) recovers Cassini's identity in the form

    Fₙ₊₁² − Fₙ₊₂ · Fₙ = (−1)ⁿ. -/
theorem fib_cassini_of_docagne (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib (n + 2) : ℤ) * Nat.fib n = (-1) ^ n := by
  have h := fib_docagne_gap n 1
  -- F_{n+1}·F_{n+1} − F_{n+2}·F_n = (−1)ⁿ·F₁ = (−1)ⁿ.
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at h
  linear_combination h

/-! ## Concrete examples (named form `Fₘ·Fₙ₊₁ − Fₘ₊₁·Fₙ = (−1)ⁿ·Fₘ₋ₙ`) -/

example : (Nat.fib 3 : ℤ) * Nat.fib 2 - (Nat.fib 4 : ℤ) * Nat.fib 1 = -1 := by decide
example : (Nat.fib 5 : ℤ) * Nat.fib 3 - (Nat.fib 6 : ℤ) * Nat.fib 2 = 2 := by decide
example : (Nat.fib 4 : ℤ) * Nat.fib 2 - (Nat.fib 5 : ℤ) * Nat.fib 1 = -2 := by decide

end FibonacciIdentitiesOQ01OQ02
