/-
Lucas analogue of Cassini's identity (OQ-01-OQ-01-OQ-01-OQ-02)

The parent entry `combinations-formula-oq-01-oq-01-oq-01` ("Companion Lucas-number
shallow-diagonal identities") introduces the Lucas sequence

  `L 0 = 2, L 1 = 1, L (n+2) = L n + L (n+1)`   (`2, 1, 3, 4, 7, 11, …`)

together with the Lucas–Fibonacci bridge `L n + F n = 2·F(n+1)`, and leaves as one of
its open questions:

  *Establish the Lucas analogue of Cassini's identity,
   `L(n−1)·L(n+1) − L(n)² = (−1)^{n−1}·5`, over ℤ.*

This file answers it.  Working over ℤ (the right-hand side alternates sign), we prove:

* `fib_catalan_int`          — the Fibonacci Catalan/Cassini identity
                               `F(n+1)² − F n·F(n+2) = (−1)^n` over ℤ.  Mathlib has no
                               such lemma, so it is proved here by a one-step
                               sign-flipping induction.
* `lucas_cassini_int`        — the reindexed Lucas Cassini identity
                               `L n·L(n+2) − L(n+1)² = (−1)^n·5` (subtraction-free
                               indices), the mathematical heart of the result.
* `lucas_cassini`            — the literal open-question form
                               `L(n−1)·L(n+1) − L(n)² = (−1)^{n−1}·5` for `n ≥ 1`,
                               obtained from `lucas_cassini_int` by reindexing.
* `lucas_sq_sub_five_fib_sq` — the structural consequence
                               `L(n)² − 5·F(n)² = 4·(−1)^n`, the discriminant identity
                               linking the Lucas Cassini constant `5` to the
                               characteristic equation `x² = x + 1` (discriminant `5`).
                               Derived from the Fibonacci Catalan identity and the
                               parent's bridge `L n = 2·F(n+1) − F n`.

The Lucas constant `5` is exactly `(±1)·5`, mirroring the Fibonacci Cassini constant
`±1` but scaled by the discriminant of `x² − x − 1`; the constant gap `5` is the Lucas
sequence's signature.  Everything is axiom-free and reuses the parent's `lucas`.
-/

import Mathlib
import Proofs.CombinationsFormulaOQ01OQ01OQ01

namespace CombinationsFormulaOQ01OQ01OQ01OQ02

open CombinationsFormulaOQ01OQ01OQ01

/-! ### Fibonacci Catalan/Cassini identity (helper)

Mathlib provides `Nat.fib` and its recurrence but no Cassini/Catalan determinant
identity.  We prove the integer form `F(n+1)² − F n·F(n+2) = (−1)^n` directly; the
proof is the classic observation that the determinant flips sign at each step. -/

/-- **Fibonacci Catalan identity.** `F(n+1)² − F n·F(n+2) = (−1)^n` over ℤ. -/
theorem fib_catalan_int (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - (Nat.fib n : ℤ) * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      -- Expand the two Fibonacci recurrences as integer identities.
      have h2 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h3 : (Nat.fib (n + 3) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        rw [show n + 3 = (n + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
      rw [h2] at ih
      rw [show n + 1 + 2 = n + 3 from rfl, h3, h2, pow_succ]
      linear_combination -ih

/-! ### The Lucas analogue of Cassini's identity -/

/-- **Lucas Cassini identity (reindexed).** `L n·L(n+2) − L(n+1)² = (−1)^n·5` over ℤ.
Subtraction-free indices; the literal `n−1` form is `lucas_cassini` below.  Proved by
the same one-step sign-flipping induction as the Fibonacci case, using the parent's
Lucas recurrence `L(n+2) = L n + L(n+1)`. -/
theorem lucas_cassini_int (n : ℕ) :
    (lucas n : ℤ) * lucas (n + 2) - (lucas (n + 1) : ℤ) ^ 2 = (-1) ^ n * 5 := by
  induction n with
  | zero => decide
  | succ n ih =>
      have h2 : (lucas (n + 2) : ℤ) = lucas n + lucas (n + 1) := by
        rw [lucas_add_two]; push_cast; ring
      have h3 : (lucas (n + 3) : ℤ) = lucas (n + 1) + lucas (n + 2) := by
        rw [show n + 3 = (n + 1) + 2 from rfl, lucas_add_two]; push_cast; ring
      rw [h2] at ih
      rw [show n + 1 + 2 = n + 3 from rfl, h3, h2, pow_succ]
      linear_combination -ih

/-- **Lucas Cassini identity (open-question form).** For `n ≥ 1`,
`L(n−1)·L(n+1) − L(n)² = (−1)^{n−1}·5` over ℤ.  This is the exact statement of the
parent's open question; it is `lucas_cassini_int` reindexed to start at `n−1`. -/
theorem lucas_cassini {n : ℕ} (hn : 1 ≤ n) :
    (lucas (n - 1) : ℤ) * lucas (n + 1) - (lucas n : ℤ) ^ 2 = (-1) ^ (n - 1) * 5 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have e1 : 1 + m - 1 = m := by omega
  have e2 : 1 + m + 1 = m + 2 := by omega
  have e3 : 1 + m = m + 1 := by omega
  rw [e1, e2, e3]
  exact lucas_cassini_int m

/-! ### Structural consequence: the discriminant identity -/

/-- **Lucas–Fibonacci discriminant identity.** `L(n)² − 5·F(n)² = 4·(−1)^n` over ℤ.
The constant `5` is the discriminant of the characteristic polynomial `x² − x − 1`,
so this is the algebraic shadow of the Lucas Cassini constant.  Derived from the
Fibonacci Catalan identity `fib_catalan_int` and the parent's bridge
`L n = 2·F(n+1) − F n`. -/
theorem lucas_sq_sub_five_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1) ^ n := by
  -- Bridge in subtraction form: L n = 2·F(n+1) − F n.
  have hb : (lucas n : ℤ) = 2 * Nat.fib (n + 1) - Nat.fib n := by
    have h : (lucas n : ℤ) + Nat.fib n = 2 * Nat.fib (n + 1) := by
      exact_mod_cast lucas_add_fib n
    omega
  -- Fibonacci Catalan identity with F(n+2) expanded.
  have hc := fib_catalan_int n
  have hf : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  rw [hf] at hc
  rw [hb]
  linear_combination 4 * hc

end CombinationsFormulaOQ01OQ01OQ01OQ02
