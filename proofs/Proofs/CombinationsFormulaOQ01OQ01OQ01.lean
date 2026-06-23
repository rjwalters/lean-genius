/-
The Lucas shallow-diagonal sum of Pascal's triangle (OQ-01-OQ-01-OQ-01)

Parent entry `combinations-formula-oq-01-oq-01` ("The Fibonacci Shallow-Diagonal Sum of
Pascal's Triangle") proves the classical identity

  `∑_{j} C(n − j, j) = F(n + 1)`

(the shallow diagonals of Pascal's triangle are the Fibonacci numbers), and leaves as its
*second* open question the **companion Lucas-number diagonal identities and the mixed
Fibonacci–Lucas diagonal sums**.

This file answers that question, axiom-free.  The Lucas numbers `L` (`L 0 = 2`, `L 1 = 1`,
`L (n+2) = L (n+1) + L n`) are the second canonical solution of the Fibonacci recurrence.
They are tied to the Fibonacci numbers by `L (n+1) = F (n+2) + F n`, so adding the *two*
adjacent shallow diagonals of Pascal's triangle that produce `F (n+2)` and `F n` recovers
the Lucas numbers:

  `L (n+1) = (∑_{j} C(n+1 − j, j)) + (∑_{j} C(n−1 − j, j))`.

Main results:
* `lucas_succ_eq_fib`        — the Fibonacci bridge `L (n+1) = F (n+2) + F n`.
* `lucas_eq_fib_add_fib`     — the symmetric corollary `L (n+1) = F n + F (n+2)`.
* `fib_shallow_diagonal'`    — the index-shifted shallow diagonal `∑_{j<n} C(n−1−j, j) = F n`.
* `lucas_shallow_diagonal`   — the mixed Fibonacci–Lucas diagonal sum (headline result).
-/

import Mathlib
import Proofs.CombinationsFormulaOQ01OQ01

namespace CombinationsFormulaOQ01OQ01OQ01

open Finset

/-- **Lucas numbers.** The second canonical solution of the Fibonacci recurrence,
with `L 0 = 2`, `L 1 = 1`, `L (n+2) = L (n+1) + L n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- **Fibonacci bridge.** Each Lucas number is a sum of two Fibonacci numbers two apart:
`L (n+1) = F (n+2) + F n`.  Proved by two-step induction, matching the Lucas recurrence. -/
theorem lucas_succ_eq_fib (n : ℕ) : lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    -- Goal: `lucas (n + 3) = F (n + 4) + F (n + 2)` (after definitional normalisation).
    show lucas (n + 3) = Nat.fib (n + 4) + Nat.fib (n + 2)
    have key : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    have ih2' : lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := ih2
    have hf : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two (n := n + 2)
    have hf2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two (n := n)
    rw [key, ih2', ih1]
    omega

/-- Symmetric restatement of the bridge: `L (n+1) = F n + F (n+2)`. -/
theorem lucas_eq_fib_add_fib (n : ℕ) : lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  rw [lucas_succ_eq_fib, Nat.add_comm]

/-- **Index-shifted shallow diagonal.** Summing `C(n−1−j, j)` over `j < n` gives `F n`.
This is the parent's `fib_shallow_diagonal` re-indexed so the Fibonacci index is `n`
(rather than `n+1`); the empty `n = 0` sum recovers `F 0 = 0`. -/
theorem fib_shallow_diagonal' (n : ℕ) :
    ∑ j ∈ range n, Nat.choose (n - 1 - j) j = Nat.fib n := by
  cases n with
  | zero => simp
  | succ m =>
    -- `n = m+1`: goal reduces to the parent statement `∑_{j<m+1} C(m−j, j) = F (m+1)`.
    simpa using CombinationsFormulaOQ01OQ01.fib_shallow_diagonal m

/-- **Mixed Fibonacci–Lucas shallow-diagonal sum.**  The Lucas number `L (n+1)` is the sum
of two adjacent shallow diagonals of Pascal's triangle:

  `L (n+1) = (∑_{j < n+2} C(n+1 − j, j)) + (∑_{j < n} C(n−1 − j, j))`.

The first sum is the Fibonacci diagonal for `F (n+2)`, the second for `F n`; their sum is
`F (n+2) + F n = L (n+1)`.  This is the companion of the parent's pure-Fibonacci diagonal
sum and resolves the parent's second open question. -/
theorem lucas_shallow_diagonal (n : ℕ) :
    lucas (n + 1)
      = (∑ j ∈ range (n + 2), Nat.choose (n + 1 - j) j)
      + (∑ j ∈ range n, Nat.choose (n - 1 - j) j) := by
  have h : (∑ j ∈ range (n + 2), Nat.choose (n + 1 - j) j) = Nat.fib (n + 2) :=
    CombinationsFormulaOQ01OQ01.fib_shallow_diagonal (n + 1)
  rw [lucas_succ_eq_fib, fib_shallow_diagonal' n, h]

end CombinationsFormulaOQ01OQ01OQ01
