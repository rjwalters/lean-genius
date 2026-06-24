import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic
import Proofs.FibonacciIdentitiesOQ01OQ02

/-
# Vajda's Identity and Catalan's Identity for Fibonacci Numbers

## What This Proves

With `Fₙ = Nat.fib n` the Fibonacci sequence (`F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`),
**Vajda's identity** is the two-parameter cross-determinant relation

    F_{n+i} · F_{n+j} − Fₙ · F_{n+i+j} = (−1)ⁿ · Fᵢ · Fⱼ      (over ℤ).

This single identity is the common engine for the whole family of "index-arithmetic"
Fibonacci identities:

* **d'Ocagne** is the slice `j = 1`  (`F₁ = 1`): `F_{n+i}·Fₙ₊₁ − Fₙ·F_{n+i+1} = (−1)ⁿ·Fᵢ`
  — exactly the parent's gap engine `fibonacci-identities-oq-01-oq-02`.
* **Cassini**  is the slice `i = j = 1`:                 `Fₙ₊₁² − Fₙ·Fₙ₊₂ = (−1)ⁿ`.
* **Catalan** is the symmetric slice `i = j = r`:        `Fₙ² − F_{n−r}·F_{n+r} = (−1)ⁿ⁻ʳ·Fᵣ²`.

Catalan's identity in the form on Wikipedia ("Cassini and Catalan identities") is

    Fₙ² − F_{n−r} · F_{n+r} = (−1)ⁿ⁻ʳ · Fᵣ²       (for r ≤ n).

(The orientation matters: with `n = 2, r = 1` one has `F₂² − F₁·F₃ = 1 − 2 = −1 = (−1)¹·F₁²`,
so it is `Fₙ² − F_{n−r}F_{n+r}`, *not* `F_{n−r}F_{n+r} − Fₙ²`, that equals `(−1)ⁿ⁻ʳFᵣ²`.)

## Approach

The key observation is that for fixed `n, i`, the cross-determinant

    g(j) := F_{n+i}·F_{n+j} − Fₙ·F_{n+i+j}

satisfies the **Fibonacci recurrence in `j`** — `g(j+2) = g(j) + g(j+1)` — because both
`F_{n+j}` and `F_{n+i+j}` do, and the map is ℤ-linear in those two entries. The target
`(−1)ⁿ·Fᵢ·Fⱼ` also satisfies the Fibonacci recurrence in `j` (only `Fⱼ` varies). Two
sequences obeying the same second-order recurrence agree everywhere once they agree at
`j = 0` and `j = 1`:

* `j = 0`:  `g(0) = F_{n+i}·Fₙ − Fₙ·F_{n+i} = 0 = (−1)ⁿ·Fᵢ·F₀`     (trivial, `F₀ = 0`);
* `j = 1`:  `g(1) = (−1)ⁿ·Fᵢ`  is **exactly d'Ocagne's identity** — supplied by the
  parent entry's `fib_docagne_gap`.

So Vajda is proved by `Nat.twoStepInduction` on `j`, with the inductive step closed by
`linear_combination ih₀ + ih₁` after rewriting the two recurrences. This *literally
unifies* Catalan with d'Ocagne: d'Ocagne is the base case `j = 1` of the induction that
yields Vajda, and Catalan is the diagonal specialisation `i = j = r`.

No closed form, Binet formula, or matrices are needed — only the recurrence and the
already-proved d'Ocagne identity.

No `decide`/`native_decide` is used in the theorems, so the proofs are axiom-free
(only Mathlib's foundational axioms).

## Distinctness

Vajda's and Catalan's identities are **not** in Mathlib (`Mathlib.Data.Nat.Fib.Basic`
has the recurrence, `fib_add`, `fib_two_mul`, `fib_gcd`, but no `(−1)ⁿ` determinant
identities). This entry answers the first open question of the parent d'Ocagne entry
(`fibonacci-identities-oq-01-oq-02`): prove Catalan's identity and unify it with
d'Ocagne via a single two-parameter cross-determinant lemma.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace FibonacciIdentitiesOQ01OQ02OQ01

open Nat

/-- **Vajda's identity (gap-parameterised, two-parameter form).**  For all `n, i, j`,

    F_{n+i} · F_{n+j} − Fₙ · F_{n+i+j} = (−1)ⁿ · Fᵢ · Fⱼ      (over ℤ).

This is the single cross-determinant lemma that specialises to d'Ocagne (`j = 1`),
Cassini (`i = j = 1`) and Catalan (`i = j = r`).  The proof is a two-step induction on
`j`: the quantity satisfies the Fibonacci recurrence in `j`, the `j = 0` case is trivial
(`F₀ = 0`), and the `j = 1` case is d'Ocagne's identity from the parent entry. -/
theorem fib_vajda_gap (n i j : ℕ) :
    (Nat.fib (n + i) : ℤ) * Nat.fib (n + j)
      - (Nat.fib n : ℤ) * Nat.fib (n + i + j)
      = (-1) ^ n * (Nat.fib i * Nat.fib j) := by
  induction j using Nat.twoStepInduction with
  | zero =>
    -- F_{n+i}·F_n − F_n·F_{n+i} = 0 = (−1)ⁿ·Fᵢ·F₀.
    simp [Nat.fib_zero]
    ring
  | one =>
    -- F_{n+i}·F_{n+1} − F_n·F_{n+i+1} = (−1)ⁿ·Fᵢ·F₁ = (−1)ⁿ·Fᵢ — d'Ocagne's identity.
    have h := FibonacciIdentitiesOQ01OQ02.fib_docagne_gap n i
    simp only [Nat.fib_one, Nat.cast_one, mul_one]
    linear_combination h
  | more j ih0 ih1 =>
    -- Fibonacci recurrence in j: g(j+2) = g(j) + g(j+1).
    have e1 : (Nat.fib (n + (j + 2)) : ℤ)
        = (Nat.fib (n + j) : ℤ) + Nat.fib (n + (j + 1)) := by
      have h1 : n + (j + 2) = (n + j) + 2 := by ring
      have h2 : n + (j + 1) = (n + j) + 1 := by ring
      rw [h1, h2]; exact_mod_cast Nat.fib_add_two (n := n + j)
    have e2 : (Nat.fib (n + i + (j + 2)) : ℤ)
        = (Nat.fib (n + i + j) : ℤ) + Nat.fib (n + i + (j + 1)) := by
      have h1 : n + i + (j + 2) = (n + i + j) + 2 := by ring
      have h2 : n + i + (j + 1) = (n + i + j) + 1 := by ring
      rw [h1, h2]; exact_mod_cast Nat.fib_add_two (n := n + i + j)
    have e3 : (Nat.fib (j + 2) : ℤ) = (Nat.fib j : ℤ) + Nat.fib (j + 1) := by
      exact_mod_cast Nat.fib_add_two (n := j)
    rw [e1, e2, e3]
    linear_combination ih0 + ih1

/-- **Catalan's identity, gap-parameterised form.**  For all `m` and `r`,

    F_{m+r}² − Fₘ · F_{m+2r} = (−1)ᵐ · Fᵣ².

The subtraction-free engine for Catalan: writing `m = n − r` recovers the named form. -/
theorem fib_catalan_gap (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - (Nat.fib m : ℤ) * Nat.fib (m + 2 * r)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  have h := fib_vajda_gap m r r
  -- h : F_{m+r}·F_{m+r} − F_m·F_{m+r+r} = (−1)ᵐ·(F_r·F_r).
  rw [show m + r + r = m + 2 * r from by ring] at h
  linear_combination h

/-- **Catalan's identity (named symmetric form).**  For `r ≤ n`,

    Fₙ² − F_{n−r} · F_{n+r} = (−1)ⁿ⁻ʳ · Fᵣ².

This is the symmetric companion of Cassini/d'Ocagne, obtained as the diagonal slice
`i = j = r` of Vajda's identity. -/
theorem fib_catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - (Nat.fib (n - r) : ℤ) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h    -- n = r + m
  rw [Nat.add_sub_cancel_left]                     -- (r + m) − r = m  (fib arg and exponent)
  rw [Nat.add_comm r m]                            -- r + m ↦ m + r everywhere
  rw [show m + r + r = m + 2 * r from by ring]
  linear_combination fib_catalan_gap m r

/-- **d'Ocagne's identity as the `j = 1` slice of Vajda** (gap-parameterised form),
re-deriving the parent entry's engine from the unified cross-determinant lemma:

    F_{n+k} · Fₙ₊₁ − F_{n+k+1} · Fₙ = (−1)ⁿ · F_k. -/
theorem fib_docagne_gap_of_vajda (n k : ℕ) :
    (Nat.fib (n + k) : ℤ) * Nat.fib (n + 1)
      - (Nat.fib (n + k + 1) : ℤ) * Nat.fib n = (-1) ^ n * Nat.fib k := by
  have h := fib_vajda_gap n k 1
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at h
  linear_combination h

/-- **Cassini's identity as the `i = j = 1` slice of Vajda.**

    Fₙ₊₁² − Fₙ · Fₙ₊₂ = (−1)ⁿ. -/
theorem fib_cassini_of_vajda (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * Nat.fib (n + 2) = (-1) ^ n := by
  have h := fib_vajda_gap n 1 1
  simp only [Nat.fib_one, Nat.cast_one, mul_one] at h
  -- h : F_{n+1}·F_{n+1} − F_n·F_{n+1+1} = (−1)ⁿ ; n+1+1 = n+2 definitionally.
  linear_combination h

/-! ## Concrete examples -/

-- Catalan, named form `Fₙ² − F_{n−r}·F_{n+r} = (−1)ⁿ⁻ʳ·Fᵣ²`:
-- n = 5, r = 2: F₅² − F₃·F₇ = 25 − 2·13 = −1 = (−1)³·F₂² = −1.
example : (Nat.fib 5 : ℤ) ^ 2 - (Nat.fib 3 : ℤ) * Nat.fib 7 = -1 := by decide
-- n = 6, r = 2: F₆² − F₄·F₈ = 64 − 3·21 = 1 = (−1)⁴·F₂² = 1.
example : (Nat.fib 6 : ℤ) ^ 2 - (Nat.fib 4 : ℤ) * Nat.fib 8 = 1 := by decide
-- Vajda, n = 2, i = 1, j = 3: F₃·F₅ − F₂·F₆ = 2·5 − 1·8 = 2 = (−1)²·F₁·F₃ = 2.
example : (Nat.fib 3 : ℤ) * Nat.fib 5 - (Nat.fib 2 : ℤ) * Nat.fib 6 = 2 := by decide

end FibonacciIdentitiesOQ01OQ02OQ01
