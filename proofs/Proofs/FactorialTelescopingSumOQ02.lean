/-
  Finite Factorial Telescoping (fractional form):
      ∑_{k=1}^{n} k / (k+1)!  =  1 − 1/(n+1)!

  Source / context: the finite closed form underlying the convergent series
      ∑_{k=1}^{∞} k/(k+1)! = 1.
  Sibling of `FactorialTelescopingSumOQ01` (∑ k·k! = (n+1)! − 1); this is the
  reciprocal (division) counterpart, worked over ℚ.
  Status: VERIFIED (0 sorries, 0 axioms, no native_decide).

  Statement:
    For every natural number n,
        ∑_{k=1}^{n} (k : ℚ)/(k+1)!  =  1 − 1/(n+1)!.

  The Key Insight (telescoping):
    Each summand is an exact factorial-reciprocal difference,
        k/(k+1)!  =  1/k! − 1/(k+1)!,
    since  1/k! − 1/(k+1)! = ((k+1) − 1)/(k+1)! = k/(k+1)!  (using (k+1)! = (k+1)·k!).
    Hence the sum telescopes:
        ∑_{k=1}^{n} k/(k+1)! = ∑_{k=1}^{n} (1/k! − 1/(k+1)!) = 1/1! − 1/(n+1)! = 1 − 1/(n+1)!.

  Lean strategy:
    Work over ℚ so that division is genuine (no ℕ truncation).  The engine is a
    one-line induction on the `range (n+1)` form; the `k = 0` term is `0/1! = 0`,
    so it agrees with the literal `∑_{k=1}^{n}` over `Finset.Icc 1 n`.  The pointwise
    step is discharged by `field_simp`/`ring` after rewriting `(k+1)! = (k+1)·k!`.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Nat

namespace FactorialTelescopingSumFractional

/-- **Pointwise telescoping identity.**  `k/(k+1)! = 1/k! − 1/(k+1)!` over ℚ.

    This is the genuine content: `1/k! − 1/(k+1)! = ((k+1) − 1)/(k+1)! = k/(k+1)!`,
    using `(k+1)! = (k+1)·k!`. -/
theorem term_telescope (k : ℕ) :
    (k : ℚ) / (k + 1)! = 1 / (k ! : ℚ) - 1 / ((k + 1)! : ℚ) := by
  have hk : (k ! : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1' : (k : ℚ) + 1 ≠ 0 := by positivity
  -- `(k+1)! = (k+1)·k!`, cast to ℚ, so both reciprocals share the common denominator.
  have hrec : ((k + 1)! : ℚ) = ((k : ℚ) + 1) * k ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hrec]
  field_simp
  ring

/-- **Range form.**  `∑_{k=0}^{n} k/(k+1)! = 1 − 1/(n+1)!` over ℚ.

    Proved directly by induction using the telescoping step
    `(n+1)/(n+2)! + 1/(n+2)! = 1/(n+1)!` (equivalently `(n+2)/(n+2)! = 1/(n+1)!`). -/
theorem sum_range_div_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), (k : ℚ) / (k + 1)! = 1 - 1 / (n + 1)! := by
  induction n with
  | zero => norm_num [Finset.sum_range_one]
  | succ n ih =>
      -- Peel off the top summand `(n+1)/(n+2)!`, rewrite it via the pointwise
      -- telescoping identity, and let `ring` cancel the interior `1/(n+1)!` terms.
      rw [Finset.sum_range_succ, ih, term_telescope (n + 1)]
      ring

/-- The `range (n+1)` sum equals the literal `∑_{k=1}^{n}` over `Finset.Icc 1 n`:
    the only extra index is `k = 0`, whose summand `0/1! = 0` vanishes. -/
theorem sum_Icc_eq_sum_range (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℚ) / (k + 1)! = ∑ k ∈ range (n + 1), (k : ℚ) / (k + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_range_succ, ih]

/-- **Headline identity.**  `∑_{k=1}^{n} k/(k+1)! = 1 − 1/(n+1)!`,
    stated over `Finset.Icc 1 n` to match the usual lower limit `k = 1`. -/
theorem sum_Icc_div_factorial (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℚ) / (k + 1)! = 1 - 1 / (n + 1)! := by
  rw [sum_Icc_eq_sum_range, sum_range_div_factorial]

-- Sanity checks (small concrete values), derived from the closed form.
-- n = 3:  1/2 + 2/6 + 3/24 = 23/24 = 1 − 1/4!.
example : ∑ k ∈ Finset.Icc (1 : ℕ) 3, (k : ℚ) / (k + 1)! = 23 / 24 := by
  rw [sum_Icc_div_factorial]; norm_num
-- n = 4:  add 4/120 = 1/30 → 119/120 = 1 − 1/5!.
example : ∑ k ∈ Finset.Icc (1 : ℕ) 4, (k : ℚ) / (k + 1)! = 119 / 120 := by
  rw [sum_Icc_div_factorial]; norm_num

end FactorialTelescopingSumFractional
