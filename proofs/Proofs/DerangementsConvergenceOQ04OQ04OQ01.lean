/-
  The multiplicative derangement recurrence  D(n) = n·D(n−1) + (−1)ⁿ
  Open Question: derangements-convergence-oq-04-oq-04-oq-01

  Let `D(n) = numDerangements n` count the fixed-point-free permutations of an
  `n`-element set.  The parent entry `derangements-convergence-oq-04-oq-04`
  proved, bijectively from the `Option` recursion equivalence

    derangements (Option α) ≃ Σ a : α, derangements ({a}ᶜ) ⊕ derangements α,

  the **additive** recurrence

    D(n) = (n − 1) · (D(n−1) + D(n−2))            (for n ≥ 2).

  Its open question OQ0 asks for the second classical recurrence — the
  **multiplicative** one —

    D(n) = n · D(n−1) + (−1)ⁿ                     (for n ≥ 1),

  as a corollary of the *same* decomposition.  This file supplies it.

  ## What this entry adds

  The multiplicative recurrence is recorded in Mathlib only as
  `numDerangements_succ`, proved there by a self-contained integer induction.
  Here we instead derive it as a genuine corollary of the additive recurrence
  (equivalently the `Option` decomposition), via the **derangement defect**

    e(m) := D(m+1) − (m+1)·D(m)   (over ℤ).

  1. `defect_step` — the additive recurrence forces `e(m+1) = −e(m)`: the defect
     merely flips sign at each step.  This is the whole combinatorial content.

  2. `defect_eq` — telescoping that sign flip from the base value
     `e(0) = D(1) − D(0) = −1` gives `e(m) = (−1)^{m+1}` for every `m`.

  3. `numDerangements_mul_recurrence` — reading the defect off gives the
     multiplicative recurrence `D(m+1) = (m+1)·D(m) + (−1)^{m+1}`, i.e.
     `D(n) = n·D(n−1) + (−1)ⁿ`, valid for **all** `n` (no `n ≥ 1` hypothesis is
     needed: the base case `D(1) = 0 = 1·1 − 1` already fits).

  4. `numDerangements_mul_recurrence'` — the same in the `n ≥ 1`, subtracted-index
     form `D(n) = n·D(n−1) + (−1)ⁿ` used in the literature.

  5. `abs_defect_eq_one` / `numDerangements_sub_mul_pred` — the exact defect
     `|D(n) − n·D(n−1)| = 1`: `D(n)` is always the integer nearest to `n·D(n−1)`,
     off by exactly one with alternating sign (the source of the closed form
     `D(n) = round(n!/e)`).

  6. `agrees_with_mathlib` — a compatibility check that the derived recurrence is
     definitionally the same statement as Mathlib's `numDerangements_succ`.

  Everything is machine-checked over `ℤ`/`ℕ` with no additional axioms beyond
  Mathlib's foundational ones; the numerical checks use `decide` (no
  `native_decide`).
-/

import Mathlib

/-
  The additive recurrence used below is Mathlib's `numDerangements_add_two`, which
  is exactly the counted form of the `Option` decomposition studied in the parent
  entry `derangements-convergence-oq-04-oq-04`; this file depends only on Mathlib.
-/

namespace DerangementsConvergenceOQ040404OQ01

/-! ## The derangement defect and its sign-flip -/

/-- The **derangement defect** `e(m) = D(m+1) − (m+1)·D(m)`, over `ℤ`. -/
def defect (m : ℕ) : ℤ :=
  (numDerangements (m + 1) : ℤ) - (m + 1) * (numDerangements m : ℤ)

/-- **The defect flips sign.**  Feeding the additive recurrence
    `D(m+2) = (m+1)·(D(m) + D(m+1))` (Mathlib's `numDerangements_add_two`, the
    counted form of the `Option` decomposition used in the parent entry) into the
    definition of `e` collapses it to `e(m+1) = −e(m)`. -/
theorem defect_step (m : ℕ) : defect (m + 1) = -defect m := by
  have h : numDerangements (m + 1 + 1)
      = (m + 1) * (numDerangements m + numDerangements (m + 1)) := numDerangements_add_two m
  simp only [defect, h]
  push_cast
  ring

/-- **The defect is a pure alternating sign.**  Telescoping `defect_step` from the
    base value `e(0) = D(1) − D(0) = 0 − 1 = −1` gives `e(m) = (−1)^{m+1}`. -/
theorem defect_eq (m : ℕ) : defect m = (-1) ^ (m + 1) := by
  induction m with
  | zero => decide
  | succ k ih => rw [defect_step, ih, pow_succ]; ring

/-! ## The multiplicative recurrence -/

/-- **Multiplicative derangement recurrence (shifted index).**  Reading the defect
    off `defect_eq` gives, for every `m`,
      `D(m+1) = (m+1)·D(m) + (−1)^{m+1}`. -/
theorem numDerangements_mul_recurrence (m : ℕ) :
    (numDerangements (m + 1) : ℤ) = (m + 1) * (numDerangements m : ℤ) + (-1) ^ (m + 1) := by
  have h := defect_eq m
  simp only [defect] at h
  linarith

/-- **Multiplicative derangement recurrence, classical form.**  For every `n ≥ 1`,
      `D(n) = n · D(n−1) + (−1)ⁿ`,
    written with truncated subtraction on the index. -/
theorem numDerangements_mul_recurrence' (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements n : ℤ) = n * (numDerangements (n - 1) : ℤ) + (-1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using numDerangements_mul_recurrence m

/-! ## The exact defect: `D(n)` is nearest to `n·D(n−1)` -/

/-- **The exact signed defect.**  `D(n) − n·D(n−1) = (−1)ⁿ` for every `n ≥ 1`. -/
theorem numDerangements_sub_mul_pred (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements n : ℤ) - n * (numDerangements (n - 1) : ℤ) = (-1) ^ n := by
  rw [numDerangements_mul_recurrence' n hn]; ring

/-- **`|D(n) − n·D(n−1)| = 1`.**  The number of derangements is always the integer
    nearest to `n·D(n−1)`, off by exactly one — the arithmetic heart of the closed
    form `D(n) = round(n!/e)`. -/
theorem abs_defect_eq_one (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℤ) - n * (numDerangements (n - 1) : ℤ)| = 1 := by
  rw [numDerangements_sub_mul_pred n hn, abs_pow, abs_neg, abs_one, one_pow]

/-! ## Compatibility with Mathlib -/

/-- **Agreement with Mathlib.**  The derived recurrence is the same statement as
    Mathlib's `numDerangements_succ` (`D(n+1) = (n+1)·D(n) − (−1)ⁿ`); the two
    sign conventions `+(−1)^{n+1}` and `−(−1)^n` coincide. -/
theorem agrees_with_mathlib (m : ℕ) :
    (m + 1) * (numDerangements m : ℤ) + (-1) ^ (m + 1)
      = (m + 1) * (numDerangements m : ℤ) - (-1) ^ m := by
  rw [pow_succ]; ring

/-! ## Numerical sanity checks (0-axiom `decide`) -/

example : numDerangements 1 = 0 := by decide
example : numDerangements 2 = 1 := by decide
example : numDerangements 3 = 2 := by decide
example : numDerangements 4 = 9 := by decide
example : numDerangements 5 = 44 := by decide

/-- Multiplicative recurrence checked at `n = 5`:
    `D(5) = 5·D(4) + (−1)^5 = 5·9 − 1 = 44`. -/
example : (numDerangements 5 : ℤ) = 5 * (numDerangements 4 : ℤ) + (-1) ^ 5 := by decide

/-- Multiplicative recurrence checked at `n = 6`:
    `D(6) = 6·D(5) + (−1)^6 = 6·44 + 1 = 265`. -/
example : (numDerangements 6 : ℤ) = 6 * (numDerangements 5 : ℤ) + (-1) ^ 6 := by decide

/-- Defect is `±1` checked at `n = 6`: `D(6) − 6·D(5) = 265 − 264 = 1`. -/
example : (numDerangements 6 : ℤ) - 6 * (numDerangements 5 : ℤ) = 1 := by decide

end DerangementsConvergenceOQ040404OQ01
