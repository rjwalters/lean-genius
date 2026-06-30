/-
Companion Lucas-number shallow-diagonal identities (OQ-01-OQ-01-OQ-01)

Parent entry `combinations-formula-oq-01-oq-01` ("The Fibonacci Shallow-Diagonal Sum
of Pascal's Triangle") proves the Fibonacci diagonal identity

  `∑_{j} C(n−j, j) = F(n+1)`

and leaves as its *second* open question:

  *Prove the companion Lucas-number diagonal identities and the mixed
   Fibonacci–Lucas diagonal sums.*

Mathlib has Fibonacci numbers (`Nat.fib`) but **no Lucas numbers** (only the
unrelated Lucas–Lehmer primality test).  This file therefore introduces the Lucas
sequence and proves:

* `lucas_add_fib`            — the bridge `L n + F n = 2·F(n+1)` (no subtraction).
* `lucas_eq`                — `L(n+1) = F(n+2) + F n`, the Lucas–Fibonacci relation.
* `lucas_shallow_diagonal`  — `L(n+2)` is the sum of **two consecutive shallow
                              diagonals** of Pascal's triangle, answering the
                              "companion Lucas-number diagonal" question by reduction
                              to the parent's `fib_shallow_diagonal`.
* `lucas_shallow_diagonal_alt` — the mirror form, companion to the parent's
                              `fib_shallow_diagonal_alt`.
* `fib_two_mul_lucas`       — the mixed Fibonacci–Lucas identity `F(2n) = F n · L n`,
                              obtained from Mathlib's `Nat.fib_two_mul`.

Everything is axiom-free.

The diagonal results all reduce to the parent's Fibonacci diagonal sum
`fib_shallow_diagonal`, replicated here so this file is self-contained.
-/

import Mathlib

namespace CombinationsFormulaOQ01OQ01OQ01

open Finset

/-! ### The Lucas sequence -/

/-- The **Lucas numbers** `L 0 = 2`, `L 1 = 1`, `L (n+2) = L n + L (n+1)`:
`2, 1, 3, 4, 7, 11, …`.  Mathlib has `Nat.fib` but no Lucas sequence. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl

theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ### The Lucas–Fibonacci bridge -/

/-- **Bridge identity.** `L n + F n = 2·F(n+1)`.  Phrased additively to avoid natural
subtraction; everything else follows from it.  Proved by two-step induction matching
the Lucas/Fibonacci recurrences. -/
theorem lucas_add_fib (n : ℕ) : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
      -- goal: `lucas (n+2) + fib (n+2) = 2 * fib (n+2+1)`
      have e : n + 2 + 1 = n + 1 + 2 := by omega
      rw [lucas_add_two, e, Nat.fib_add_two (n := n), Nat.fib_add_two (n := n + 1)]
      omega

/-- **Lucas–Fibonacci relation.** `L(n+1) = F(n+2) + F n`.  Equivalently the Lucas
numbers are the sum of the two Fibonacci numbers straddling the index. -/
theorem lucas_eq (n : ℕ) : lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n := by
  have A := lucas_add_fib (n + 1)          -- L(n+1) + F(n+1) = 2·F(n+1+1)
  have C : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have D : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  omega

/-! ### Shallow-diagonal sums of Pascal's triangle

The parent file's Fibonacci diagonal identity, replicated so this file stands alone. -/

/-- **Fibonacci shallow-diagonal sum (mirror form).** `∑_{k} C(k, n−k) = F(n+1)`.
(Parent `combinations-formula-oq-01-oq-01`.) -/
theorem fib_shallow_diagonal_alt (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose k (n - k) = Nat.fib (n + 1) := by
  rw [Nat.fib_succ_eq_sum_choose, Finset.Nat.sum_antidiagonal_eq_sum_range_succ Nat.choose]

/-- **Fibonacci shallow-diagonal sum.** `∑_{j} C(n−j, j) = F(n+1)`.
(Parent `combinations-formula-oq-01-oq-01`.) -/
theorem fib_shallow_diagonal (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), Nat.choose (n - j) j = Nat.fib (n + 1) := by
  rw [← fib_shallow_diagonal_alt,
      ← Finset.sum_range_reflect (fun k => Nat.choose k (n - k)) (n + 1)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e2 : n - (n - j) = j := by omega
  simp only [e1, e2]

/-! ### Companion Lucas-number diagonal identities -/

/-- **Lucas shallow-diagonal sum.** The Lucas number `L(n+2)` is the sum of **two
consecutive shallow diagonals** of Pascal's triangle:

  `L(n+2) = ∑_{j} C(n+2−j, j) + ∑_{j} C(n−j, j)`.

This is the companion of the parent's Fibonacci diagonal identity, obtained from the
Lucas–Fibonacci relation `L(n+2) = F(n+3) + F(n+1)` by expanding each Fibonacci term
as a shallow diagonal. -/
theorem lucas_shallow_diagonal (n : ℕ) :
    lucas (n + 2) =
      (∑ j ∈ Finset.range (n + 2 + 1), Nat.choose (n + 2 - j) j) +
        ∑ j ∈ Finset.range (n + 1), Nat.choose (n - j) j := by
  rw [fib_shallow_diagonal (n + 2), fib_shallow_diagonal n]
  -- goal: `L(n+2) = F(n+2+1) + F(n+1)`
  have A := lucas_add_fib (n + 2)          -- L(n+2) + F(n+2) = 2·F(n+2+1)
  have C : Nat.fib (n + 2 + 1) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  omega

/-- **Lucas shallow-diagonal sum (mirror form).** The mirror companion, summing
`C(k, ·)` instead of `C(·, j)`:

  `L(n+2) = ∑_{k} C(k, n+2−k) + ∑_{k} C(k, n−k)`.

Mirrors the parent's `fib_shallow_diagonal_alt`. -/
theorem lucas_shallow_diagonal_alt (n : ℕ) :
    lucas (n + 2) =
      (∑ k ∈ Finset.range (n + 2 + 1), Nat.choose k (n + 2 - k)) +
        ∑ k ∈ Finset.range (n + 1), Nat.choose k (n - k) := by
  rw [fib_shallow_diagonal_alt (n + 2), fib_shallow_diagonal_alt n]
  have A := lucas_add_fib (n + 2)
  have C : Nat.fib (n + 2 + 1) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  omega

/-! ### Mixed Fibonacci–Lucas identity -/

/-- **Mixed Fibonacci–Lucas product identity.** `F(2n) = F n · L n`.  The even-index
Fibonacci numbers factor through the Lucas sequence.  Obtained from Mathlib's
`Nat.fib_two_mul` (`F(2n) = F n · (2·F(n+1) − F n)`) together with the bridge
`L n + F n = 2·F(n+1)`. -/
theorem fib_two_mul_lucas (n : ℕ) : Nat.fib (2 * n) = Nat.fib n * lucas n := by
  have h : 2 * Nat.fib (n + 1) - Nat.fib n = lucas n := by
    have := lucas_add_fib n; omega
  rw [Nat.fib_two_mul, h]

end CombinationsFormulaOQ01OQ01OQ01
