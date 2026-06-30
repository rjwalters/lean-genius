/-
# Catalan's Identity (the `r`-step generalization of Cassini)

Catalan's identity states that for the Fibonacci numbers `F` and `r ≤ n`,

  `Fₙ² − F_{n−r}·F_{n+r} = (−1)^{n−r} · Fᵣ²`.

It is the genuine generalization of the parent file's **Cassini identity**
(`CassiniIdentityOQ01.cassini`), which is exactly the step `r = 1`:
`F_{n+1}² − Fₙ·F_{n+2} = (−1)ⁿ`. Where Cassini compares two *consecutive*
Fibonacci numbers, Catalan compares the three numbers `F_{n−r}, Fₙ, F_{n+r}`
that sit in arithmetic progression of step `r`, and measures the failure of the
"middle square equals the product of the outer terms" by the square `Fᵣ²`.

Mathlib records neither Catalan's identity nor the general Vajda/d'Ocagne
bilinear identities for `Nat.fib`; it has only the integer-indexed Cassini
specialization. We give a short, fully elementary proof:

* `cassini_sub` — the Cassini identity in the normalized algebraic form
  `F_{m+1}² − Fₘ·F_{m+1} − Fₘ² = (−1)ᵐ`, proved by a one-line induction off the
  defining recurrence `Nat.fib_add_two`.

* `catalan_aux` — the subtraction-free reindexing
  `F_{m+r}² − Fₘ·F_{m+2r} = (−1)ᵐ · Fᵣ²` (set `m = n − r`). Its proof is pure
  algebra: expand `F_{m+r}` and `F_{m+2r}` with Mathlib's **addition formula**
  `Nat.fib_add`, then collapse the result with Cassini. No second induction.

* `catalan` — the classical signed form `Fₙ² − F_{n−r}F_{n+r} = (−1)^{n−r}Fᵣ²`
  for `r ≤ n`, obtained from `catalan_aux` by `m := n − r`.

No axioms, no `native_decide`, no sorries.
-/
import Mathlib

namespace CassiniIdentityOQ01OQ01

/-- **Cassini's identity, normalized algebraic form.**
`F_{m+1}² − Fₘ·F_{m+1} − Fₘ² = (−1)ᵐ`. This is the `r = 1` core that drives the
general Catalan identity. Proved by induction off `Nat.fib_add_two`. -/
theorem cassini_sub (m : ℕ) :
    (Nat.fib (m + 1) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 1) - (Nat.fib m : ℤ) ^ 2
      = (-1) ^ m := by
  induction m with
  | zero => norm_num [Nat.fib_one, Nat.fib_zero]
  | succ k ih =>
    have hrec : (Nat.fib (k + 1 + 1) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast (Nat.fib_add_two (n := k))
    rw [hrec]
    have hsign : (-1 : ℤ) ^ (k + 1) = -((-1) ^ k) := by ring
    rw [hsign]
    linear_combination -ih

/-- **Catalan's identity (subtraction-free form).**
`F_{m+r}² − Fₘ·F_{m+2r} = (−1)ᵐ · Fᵣ²`. The classical statement is recovered by
`m = n − r` (see `catalan`). The proof expands `F_{m+r}` and `F_{m+2r}` by the
Fibonacci addition formula `Nat.fib_add` and finishes with Cassini. -/
theorem catalan_aux (m r : ℕ) :
    (Nat.fib (m + r) : ℤ) ^ 2 - Nat.fib m * Nat.fib (m + 2 * r)
      = (-1) ^ m * (Nat.fib r : ℤ) ^ 2 := by
  cases r with
  | zero => simp only [Nat.mul_zero, Nat.add_zero, Nat.fib_zero]; ring
  | succ s =>
    have e1 : m + (s + 1) = m + s + 1 := by ring
    have e2 : m + 2 * (s + 1) = m + s + 1 + s + 1 := by ring
    rw [e1, e2]
    -- Addition-formula expansions (all indices in the normal form `· + 1`).
    have hA : (Nat.fib (m + s + 1) : ℤ)
        = Nat.fib m * Nat.fib s + Nat.fib (m + 1) * Nat.fib (s + 1) := by
      exact_mod_cast Nat.fib_add m s
    have hB : (Nat.fib (m + s + 1 + 1) : ℤ)
        = Nat.fib m * Nat.fib (s + 1) + Nat.fib (m + 1) * Nat.fib (s + 2) := by
      exact_mod_cast Nat.fib_add m (s + 1)
    have hC : (Nat.fib (m + s + 1 + s + 1) : ℤ)
        = Nat.fib (m + s + 1) * Nat.fib s + Nat.fib (m + s + 1 + 1) * Nat.fib (s + 1) := by
      exact_mod_cast Nat.fib_add (m + s + 1) s
    have hb2 : (Nat.fib (s + 2) : ℤ) = Nat.fib s + Nat.fib (s + 1) := by
      exact_mod_cast (Nat.fib_add_two (n := s))
    have hcas := cassini_sub m
    rw [hC, hA, hB, hb2]
    linear_combination (Nat.fib (s + 1) : ℤ) ^ 2 * hcas

/-- **Catalan's identity** (classical signed form).
For `r ≤ n`, `Fₙ² − F_{n−r}·F_{n+r} = (−1)^{n−r} · Fᵣ²`. The `r = 1` case is
Cassini's identity. -/
theorem catalan (n r : ℕ) (h : r ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - Nat.fib (n - r) * Nat.fib (n + r)
      = (-1) ^ (n - r) * (Nat.fib r : ℤ) ^ 2 := by
  have key := catalan_aux (n - r) r
  rw [Nat.sub_add_cancel h] at key
  have e : n - r + 2 * r = n + r := by omega
  rw [e] at key
  exact key

/-! ### Sanity checks against the classical statement -/

/-- `r = 1` recovers Cassini: `Fₙ² − F_{n−1}F_{n+1} = (−1)^{n−1}`. -/
theorem catalan_one (n : ℕ) (h : 1 ≤ n) :
    (Nat.fib n : ℤ) ^ 2 - Nat.fib (n - 1) * Nat.fib (n + 1) = (-1) ^ (n - 1) := by
  have := catalan n 1 h
  simpa using this

/-- `n = 5, r = 2`: `F₅² − F₃·F₇ = 25 − 2·13 = −1 = (−1)³·F₂² = (−1)³·1`. -/
theorem catalan_5_2 :
    (Nat.fib 5 : ℤ) ^ 2 - Nat.fib 3 * Nat.fib 7 = (-1) ^ 3 * (Nat.fib 2 : ℤ) ^ 2 := by
  have := catalan 5 2 (by norm_num)
  norm_num at this ⊢

/-- `n = 6, r = 2`: `F₆² − F₄·F₈ = 64 − 3·21 = 1 = (−1)⁴·F₂²`. -/
theorem catalan_6_2 :
    (Nat.fib 6 : ℤ) ^ 2 - Nat.fib 4 * Nat.fib 8 = (-1) ^ 4 * (Nat.fib 2 : ℤ) ^ 2 := by
  have := catalan 6 2 (by norm_num)
  norm_num at this ⊢

end CassiniIdentityOQ01OQ01
