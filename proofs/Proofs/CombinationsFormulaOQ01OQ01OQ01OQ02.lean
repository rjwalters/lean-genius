/-
Lucas analogue of Cassini's identity (OQ-01-OQ-01-OQ-01-OQ-02)

Parent entry `combinations-formula-oq-01-oq-01-oq-01`
("Companion Lucas-Number Shallow-Diagonal Identities") introduces the Lucas
sequence `L 0 = 2, L 1 = 1, L (n+2) = L n + L (n+1)` (Mathlib has `Nat.fib` but
no Lucas numbers) and the Lucas–Fibonacci bridge `L n + F n = 2·F(n+1)`.  It
leaves open the *quantitative* second-order identities for the Lucas sequence.

This file answers the **Lucas analogue of Cassini's identity**:

  `L(n-1)·L(n+1) − L(n)² = (−1)^(n−1)·5`.

Working over `ℤ` to accommodate the alternating sign, we prove:

* `lucas_cassini`        — the subtraction-free shifted form
                           `L n · L(n+2) − L(n+1)² = 5·(−1)^n`, by induction on
                           the determinant alternation `D(n+1) = −D(n)`.
* `lucas_cassini_pred`   — the literal predecessor form
                           `L(n-1)·L(n+1) − L(n)² = (−1)^(n-1)·5` for `n ≥ 1`.
* `fib_cassini`          — Cassini's identity for the Fibonacci numbers
                           `F n · F(n+2) − F(n+1)² = (−1)^(n+1)` (Mathlib lacks it).
* `lucas_sq_sub_five_fib_sq` — the companion `L(n)² − 5·F(n)² = 4·(−1)^n`, which
                           exhibits where the constant `5` in Lucas–Cassini comes
                           from: it is the discriminant of `x² − x − 1`.

The Lucas sequence and the bridge `lucas_add_fib` are imported from the parent.
Everything is axiom-free.
-/

import Mathlib
import Proofs.CombinationsFormulaOQ01OQ01OQ01

namespace CombinationsFormulaOQ01OQ01OQ01OQ02

open CombinationsFormulaOQ01OQ01OQ01

/-! ### Cassini's identity for the Lucas numbers -/

/-- **Lucas analogue of Cassini's identity (shifted, subtraction-free form).**

  `L n · L(n+2) − L(n+1)² = 5·(−1)^n`.

For any sequence obeying `a(n+2) = a(n) + a(n+1)`, the "second-order determinant"
`D(n) = a n · a(n+2) − a(n+1)²` satisfies `D(n+1) = −D(n)`; the proof is a direct
induction using that alternation, with base value `D(0) = 2·3 − 1² = 5`. -/
theorem lucas_cassini (n : ℕ) :
    (lucas n : ℤ) * lucas (n + 2) - (lucas (n + 1) : ℤ) ^ 2 = 5 * (-1) ^ n := by
  induction n with
  | zero => norm_num [lucas]
  | succ k ih =>
      -- normalise the goal's index shapes `k+1+1 → k+2`, `k+1+2 → k+3`
      simp only [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl]
      have e2 : (lucas (k + 2) : ℤ) = (lucas k : ℤ) + lucas (k + 1) := by
        exact_mod_cast lucas_add_two k
      have e3 : (lucas (k + 3) : ℤ) = (lucas (k + 1) : ℤ) + lucas (k + 2) := by
        have h := lucas_add_two (k + 1)
        simp only [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl] at h
        exact_mod_cast h
      rw [e2] at ih
      rw [e3, e2, pow_succ]
      linear_combination -ih

/-- **Lucas analogue of Cassini's identity (literal predecessor form).**

  `L(n-1)·L(n+1) − L(n)² = (−1)^(n-1)·5`  for `n ≥ 1`. -/
theorem lucas_cassini_pred (n : ℕ) (hn : 1 ≤ n) :
    (lucas (n - 1) : ℤ) * lucas (n + 1) - (lucas n : ℤ) ^ 2 = (-1) ^ (n - 1) * 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  show (lucas m : ℤ) * lucas (m + 2) - (lucas (m + 1) : ℤ) ^ 2 = (-1) ^ (m + 1 - 1) * 5
  rw [Nat.add_sub_cancel]
  linear_combination lucas_cassini m

/-! ### Cassini's identity for the Fibonacci numbers

Mathlib provides `Nat.fib` and `Nat.fib_add_two` but no Cassini identity, so we
prove it here over `ℤ`; it is used below to locate the `5` in Lucas–Cassini. -/

/-- **Cassini's identity for the Fibonacci numbers.**

  `F n · F(n+2) − F(n+1)² = (−1)^(n+1)`.

Same determinant alternation as the Lucas case, base value `F 0·F 2 − F 1² = −1`. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib n : ℤ) * Nat.fib (n + 2) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h2 : (Nat.fib (k + 1 + 1) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
        exact_mod_cast Nat.fib_add_two
      have h3 : (Nat.fib (k + 1 + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + Nat.fib (k + 1 + 1) := by
        exact_mod_cast Nat.fib_add_two
      have h2' : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + Nat.fib (k + 1) := by
        exact_mod_cast Nat.fib_add_two
      rw [h2'] at ih
      rw [h3, h2, pow_succ]
      linear_combination -ih

/-! ### Where the `5` comes from -/

/-- **Lucas–Fibonacci "Pell-like" companion.**  `L(n)² − 5·F(n)² = 4·(−1)^n`.

This identity explains the constant `5` appearing in `lucas_cassini`: it is the
discriminant `b² − 4·(−1)` for the recurrence `x² = x + 1` (i.e. of `x² − x − 1`),
and here it links the Lucas and Fibonacci Cassini determinants.  Derived purely
algebraically from the bridge `L n + F n = 2·F(n+1)` and `fib_cassini`. -/
theorem lucas_sq_sub_five_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1) ^ n := by
  have hb : (lucas n : ℤ) + Nat.fib n = 2 * Nat.fib (n + 1) := by
    exact_mod_cast lucas_add_fib n
  have hf2 : (Nat.fib (n + 2) : ℤ) = (Nat.fib n : ℤ) + Nat.fib (n + 1) := by
    exact_mod_cast Nat.fib_add_two
  have hc := fib_cassini n
  rw [hf2, pow_succ] at hc
  linear_combination
    ((lucas n : ℤ) + 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ)) * hb - 4 * hc

end CombinationsFormulaOQ01OQ01OQ01OQ02
