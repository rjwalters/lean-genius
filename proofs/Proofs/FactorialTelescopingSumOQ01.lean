/-
  Factorial Telescoping Sum:  ∑_{k=1}^{n} k · k! = (n+1)! − 1

  Source / context: classical factorial identity (Gauss-style telescoping).
  Status: VERIFIED (0 sorries, 0 axioms, no native_decide).

  Statement:
    For every natural number n,
        ∑_{k=1}^{n} k · k!  =  (n+1)! − 1.

  The Key Insight (telescoping):
    Each summand collapses a factorial difference,
        k · k!  =  (k+1)! − k!,
    so the sum telescopes:
        ∑_{k=1}^{n} k · k!  =  ∑_{k=1}^{n} ((k+1)! − k!)  =  (n+1)! − 1! = (n+1)! − 1.

  Lean strategy:
    Over ℕ, truncated subtraction makes the telescoped form awkward to manipulate,
    so the engine is the *additive* (subtraction-free) reformulation
        (∑_{k=0}^{n} k · k!) + 1 = (n+1)!,
    proved by a one-line induction (`Finset.sum_range_succ` + `Nat.factorial_succ`).
    The headline subtraction form and the literal `∑_{k=1}^{n}` (over `Finset.Icc 1 n`)
    are then derived from it (`omega` discharges the ℕ-subtraction step; the `k = 0`
    term vanishes, so the `range (n+1)` and `Icc 1 n` sums agree).
-/

import Mathlib

open Finset

namespace FactorialTelescopingSum

/-- **Additive (subtraction-free) form.**  `(∑_{k=0}^{n} k·k!) + 1 = (n+1)!`.

    The `k = 0` term is `0·0! = 0`, so the left sum equals `∑_{k=1}^{n} k·k!`.
    This is the genuine content of the identity: it is proved directly by induction,
    using the telescoping step `(n+1)·(n+1)! + (n+1)! = (n+2)!`, and avoids ℕ
    truncated subtraction entirely. -/
theorem sum_mul_factorial_add_one (n : ℕ) :
    (∑ k ∈ range (n + 1), k * k !) + 1 = (n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      -- Regroup so the inductive hypothesis `(∑) + 1 = (n+1)!` applies.
      have key : (∑ k ∈ range (n + 1), k * k !) + (n + 1) * (n + 1)! + 1
          = ((∑ k ∈ range (n + 1), k * k !) + 1) + (n + 1) * (n + 1)! := by ring
      rw [key, ih, Nat.factorial_succ (n + 1)]
      ring

/-- **Headline identity (ℕ-subtraction form).**  `∑_{k=0}^{n} k·k! = (n+1)! − 1`.

    Since the `k = 0` summand vanishes this is exactly `∑_{k=1}^{n} k·k! = (n+1)! − 1`.
    Derived from `sum_mul_factorial_add_one`; `omega` handles the truncated subtraction
    (valid because `(n+1)! ≥ 1`). -/
theorem sum_mul_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), k * k ! = (n + 1)! - 1 := by
  have h := sum_mul_factorial_add_one n
  omega

/-- The `range (n+1)` sum equals the literal `∑_{k=1}^{n}` over `Finset.Icc 1 n`:
    the only extra index is `k = 0`, whose summand `0·0!` is zero. -/
theorem sum_Icc_eq_sum_range (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, k * k ! = ∑ k ∈ range (n + 1), k * k ! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]

/-- **Literal `∑_{k=1}^{n}` form.**  `∑_{k=1}^{n} k·k! = (n+1)! − 1`,
    stated over `Finset.Icc 1 n` to match the usual lower limit `k = 1`. -/
theorem sum_Icc_mul_factorial (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, k * k ! = (n + 1)! - 1 := by
  rw [sum_Icc_eq_sum_range, sum_mul_factorial]

/-- Pointwise telescoping identity behind the proof: `k·k! = (k+1)! − k!`. -/
theorem mul_factorial_eq (k : ℕ) : k * k ! = (k + 1)! - k ! := by
  rw [Nat.factorial_succ]
  have : k ! ≤ (k + 1) * k ! := Nat.le_mul_of_pos_left _ (by omega)
  omega

-- Sanity checks (small concrete values).
example : ∑ k ∈ range 4, k * k ! = 23 := by decide   -- 0+1+4+18 = 23 = 4! − 1
example : ∑ k ∈ Finset.Icc 1 5, k * k ! = 719 := by decide  -- 6! − 1 = 719

end FactorialTelescopingSum
