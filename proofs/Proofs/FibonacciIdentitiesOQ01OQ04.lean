import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Proofs.FibonacciIdentitiesOQ01OQ02OQ01

/-
# The Gelin–Cesàro Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
the **Gelin–Cesàro identity** is the quartic product relation

    F_{n-2} · F_{n-1} · F_{n+1} · F_{n+2} = Fₙ⁴ − 1        (for n ≥ 2).

The four Fibonacci numbers symmetrically flanking `Fₙ` (two on each side) multiply to
exactly one less than the fourth power of the central term.

## Approach

The identity factors through **Catalan's identity** (proved in the sibling entry
`fibonacci-identities-oq-01-oq-02-oq-01` as `fib_catalan_gap`):

    F_{m+r}² − Fₘ · F_{m+2r} = (−1)ᵐ · Fᵣ².

Writing `m = n − 2` and pairing the outer and inner factors of the product:

* **Outer pair** (`r = 2`, `F₂ = 1`):  `Fₘ · F_{m+4} = F_{m+2}² − (−1)ᵐ`.
* **Inner pair** (`r = 1`, `F₁ = 1`):  `F_{m+1} · F_{m+3} = F_{m+2}² + (−1)ᵐ`.

Multiplying the two is a difference of squares:

    (F_{m+2}² − (−1)ᵐ)(F_{m+2}² + (−1)ᵐ) = F_{m+2}⁴ − ((−1)ᵐ)² = F_{m+2}⁴ − 1,

using `((−1)ᵐ)² = 1`. Re-indexing `m + 2 = n` recovers the named form for `n ≥ 2`.

No closed form, Binet formula, or `decide`/`native_decide` is used in the theorems, so
the proofs are axiom-free (only Mathlib's foundational axioms). The single sign fact
`((−1)ᵐ)² = 1` is discharged from `Even (m + m)`.

## Distinctness

Gelin–Cesàro is **not** in Mathlib (`Mathlib.Data.Nat.Fib.Basic` has the recurrence and
`fib_add` but no product identities). It is a genuine two-sided consequence of Catalan —
distinct from Cassini (`i = j = 1`), d'Ocagne (`j = 1`), and Catalan itself (a single
symmetric determinant) — obtained by *combining* the `r = 1` and `r = 2` Catalan slices.
This answers the fourth open question of `fibonacci-identities-oq-01`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01OQ04

open Nat

/-- `((−1)ᵐ)² = 1` over `ℤ`, the sign fact that collapses the difference of squares. -/
private theorem neg_one_pow_sq (m : ℕ) : ((-1 : ℤ) ^ m) ^ 2 = 1 := by
  rw [← pow_mul]
  exact Even.neg_one_pow ⟨m, by ring⟩

/-- **Outer pair from Catalan (`r = 2`).**  `Fₘ · F_{m+4} = F_{m+2}² − (−1)ᵐ`. -/
private theorem fib_outer_pair (m : ℕ) :
    (Nat.fib m : ℤ) * Nat.fib (m + 4) = (Nat.fib (m + 2) : ℤ) ^ 2 - (-1) ^ m := by
  have h := FibonacciIdentitiesOQ01OQ02OQ01.fib_catalan_gap m 2
  rw [show m + 2 * 2 = m + 4 by norm_num, Nat.fib_two] at h
  -- h : F_{m+2}² − Fₘ·F_{m+4} = (−1)ᵐ · (1)²
  push_cast at h
  linarith

/-- **Inner pair from Catalan (`r = 1`).**  `F_{m+1} · F_{m+3} = F_{m+2}² + (−1)ᵐ`. -/
private theorem fib_inner_pair (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) * Nat.fib (m + 3) = (Nat.fib (m + 2) : ℤ) ^ 2 + (-1) ^ m := by
  have h := FibonacciIdentitiesOQ01OQ02OQ01.fib_catalan_gap (m + 1) 1
  rw [show m + 1 + 1 = m + 2 by norm_num, show m + 1 + 2 * 1 = m + 3 by norm_num,
      Nat.fib_one] at h
  -- h : F_{m+2}² − F_{m+1}·F_{m+3} = (−1)^{m+1} · (1)²
  have hs : ((-1 : ℤ)) ^ (m + 1) = -((-1) ^ m) := by rw [pow_succ]; ring
  rw [hs] at h
  simp only [Nat.cast_one, one_pow, mul_one] at h
  -- h : F_{m+2}² − F_{m+1}·F_{m+3} = −(−1)ᵐ
  linarith

/-- **Gelin–Cesàro identity, gap-parameterised (subtraction-free) form.**  For all `m`,

    Fₘ · F_{m+1} · F_{m+3} · F_{m+4} = F_{m+2}⁴ − 1.

The engine: the outer pair (Catalan `r = 2`) and inner pair (Catalan `r = 1`) multiply
as a difference of squares, and `((−1)ᵐ)² = 1` kills the cross term. -/
theorem fib_gelin_cesaro_gap (m : ℕ) :
    (Nat.fib m : ℤ) * Nat.fib (m + 1) * Nat.fib (m + 3) * Nat.fib (m + 4)
      = (Nat.fib (m + 2) : ℤ) ^ 4 - 1 := by
  calc
    (Nat.fib m : ℤ) * Nat.fib (m + 1) * Nat.fib (m + 3) * Nat.fib (m + 4)
        = ((Nat.fib m : ℤ) * Nat.fib (m + 4))
            * ((Nat.fib (m + 1) : ℤ) * Nat.fib (m + 3)) := by ring
    _ = ((Nat.fib (m + 2) : ℤ) ^ 2 - (-1) ^ m)
            * ((Nat.fib (m + 2) : ℤ) ^ 2 + (-1) ^ m) := by
          rw [fib_outer_pair, fib_inner_pair]
    _ = (Nat.fib (m + 2) : ℤ) ^ 4 - ((-1) ^ m) ^ 2 := by ring
    _ = (Nat.fib (m + 2) : ℤ) ^ 4 - 1 := by rw [neg_one_pow_sq]

/-- **Gelin–Cesàro identity (named form).**  For `n ≥ 2`,

    F_{n−2} · F_{n−1} · F_{n+1} · F_{n+2} = Fₙ⁴ − 1.

The four Fibonacci numbers flanking `Fₙ` symmetrically multiply to `Fₙ⁴ − 1`. Obtained
from the gap form by the re-index `m = n − 2`. -/
theorem fib_gelin_cesaro (n : ℕ) (hn : 2 ≤ n) :
    (Nat.fib (n - 2) : ℤ) * Nat.fib (n - 1) * Nat.fib (n + 1) * Nat.fib (n + 2)
      = (Nat.fib n : ℤ) ^ 4 - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn   -- n = 2 + m
  have h := fib_gelin_cesaro_gap m
  rw [show 2 + m - 2 = m by omega, show 2 + m - 1 = m + 1 by omega,
      show 2 + m + 1 = m + 3 by omega, show 2 + m + 2 = m + 4 by omega,
      show 2 + m = m + 2 by omega]
  exact h

/-! ## Concrete examples -/

-- n = 4:  F₂·F₃·F₅·F₆ = 1·2·5·8 = 80 = F₄⁴ − 1 = 3⁴ − 1 = 81 − 1 = 80.
example : (Nat.fib 2 : ℤ) * Nat.fib 3 * Nat.fib 5 * Nat.fib 6 = (Nat.fib 4 : ℤ) ^ 4 - 1 := by
  decide
-- n = 6:  F₄·F₅·F₇·F₈ = 3·5·13·21 = 4095 = F₆⁴ − 1 = 8⁴ − 1 = 4096 − 1 = 4095.
example : (Nat.fib 4 : ℤ) * Nat.fib 5 * Nat.fib 7 * Nat.fib 8 = (Nat.fib 6 : ℤ) ^ 4 - 1 := by
  decide

end FibonacciIdentitiesOQ01OQ04
