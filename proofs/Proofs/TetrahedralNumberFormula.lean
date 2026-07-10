import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-
# Sum of Triangular Numbers Equals the Tetrahedral Number

## Open Question (tetrahedral-number-formula)

"The running total of the first `n` triangular numbers is the `n`-th tetrahedral
number":

    ∑_{k=1}^{n} T_k = C(n+2, 3) = n·(n+1)·(n+2)/6,   where T_k = C(k+1, 2) = k·(k+1)/2.

This is the `d = 3` rung of the figurate-number ladder (linear → triangular →
tetrahedral) and the `d = 3` case of the hockey-stick identity
`∑_{k} C(k+d-2, d-1) = C(n+d-1, d)`.

## Result

A fully machine-checked, self-contained proof by induction, phrased with
`Nat.choose` so that no division ever appears:

* `sum_triangular_choose` : `∑_{k<n+1} C(k+1, 2) = C(n+2, 3)`   — the clean
  hockey-stick statement (each summand is the triangular number `T_k`);
* `six_mul_sum_triangular` : `6·∑_{k<n+1} C(k+1, 2) = n·(n+1)·(n+2)` — the
  division-free polynomial identity requested by the problem;
* `six_mul_choose_three` : `6·C(n+2, 3) = n·(n+1)·(n+2)`         — the cleared
  closed form for the tetrahedral number itself.

The inductive steps use only `Finset.sum_range_succ`, Pascal's rule
(`Nat.choose_succ_succ`), and `ring`/`omega`; the sole ℕ-division in the
classical statement is bypassed by working with `Nat.choose` and clearing
denominators.

## Novelty

Mathlib has `Nat.choose_two_right` and Pascal's rule but neither the tetrahedral
(sum-of-triangular-numbers) closed form nor the `d = 3` hockey-stick identity as
a named lemma. This file supplies both, alongside the explicit
`T_k = k·(k+1)/2` phrasing that connects the `choose` form to the elementary
triangular-number definition.

0 sorries, 0 axioms.
-/

namespace TetrahedralNumberFormula

open Finset

/-- The `k`-th triangular number as a binomial coefficient, `T_k = C(k+1, 2)`,
equals the elementary closed form `k·(k+1)/2`. Provided so the `choose`-based
identities below can be read in the familiar `T_k = k(k+1)/2` notation. -/
theorem triangular_choose_eq (k : ℕ) : (k + 1).choose 2 = k * (k + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- Twice the `k`-th triangular number is `k·(k+1)`: a division-free restatement
of `T_k = k·(k+1)/2`. Since `k·(k+1)` is even, clearing the `/2` is exact. -/
theorem two_mul_triangular_choose (k : ℕ) :
    2 * (k + 1).choose 2 = k * (k + 1) := by
  rw [triangular_choose_eq]
  exact Nat.mul_div_cancel' (Nat.even_mul_succ_self k).two_dvd

/-- **Tetrahedral number formula (division-free).** Six times the sum of the
first `n` triangular numbers `T_k = C(k+1, 2)` (for `k = 0,…,n`, the `k = 0`
term being `0`) equals `n·(n+1)·(n+2)`:

`6·∑_{k<n+1} C(k+1, 2) = n·(n+1)·(n+2)`.

This is the cleared-denominator form of the classical
`∑ T_k = n(n+1)(n+2)/6`. Proved directly by induction: the new summand
`T_{m+1} = C(m+2, 2)` contributes `6·C(m+2, 2) = 3·(m+1)·(m+2)` via
`two_mul_triangular_choose`, and `ring` closes the polynomial step. -/
theorem six_mul_sum_triangular (n : ℕ) :
    6 * ∑ k ∈ range (n + 1), (k + 1).choose 2 = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, Nat.mul_add]
    -- 6·∑_{k<m+1} + 6·C(m+2, 2) = (m+1)·(m+2)·(m+3)
    rw [ih]
    have hnew : 6 * (m + 1 + 1).choose 2 = 3 * ((m + 1) * (m + 1 + 1)) := by
      have h := two_mul_triangular_choose (m + 1)
      omega
    rw [hnew]
    ring

/-- **Sum of triangular numbers = tetrahedral number (hockey-stick, `d = 3`).**
The sum of the first `n` triangular numbers `T_k = C(k+1, 2)` equals the
tetrahedral number `C(n+2, 3)`:

`∑_{k<n+1} C(k+1, 2) = C(n+2, 3)`.

The inductive step is a single application of Pascal's rule
`C(m+3, 3) = C(m+2, 2) + C(m+2, 3)`, matching the newly added summand
`T_{m+1} = C(m+2, 2)`. -/
theorem sum_triangular_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), (k + 1).choose 2 = (n + 2).choose 3 := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, ih]
    -- C(m+2, 3) + C(m+1+1, 2) = C(m+1+2, 3)
    have pascal : (m + 1 + 2).choose 3
        = (m + 1 + 1).choose 2 + (m + 2).choose 3 :=
      Nat.choose_succ_succ (m + 2) 2
    rw [pascal]
    omega

/-- **Tetrahedral closed form.** Six times the tetrahedral number `C(n+2, 3)`
equals `n·(n+1)·(n+2)`; the cleared-denominator form of
`C(n+2, 3) = n(n+1)(n+2)/6`. Immediate from the hockey-stick identity and the
polynomial sum formula. -/
theorem six_mul_choose_three (n : ℕ) :
    6 * (n + 2).choose 3 = n * (n + 1) * (n + 2) := by
  rw [← sum_triangular_choose]
  exact six_mul_sum_triangular n

/-- **Tetrahedral closed form (with division).** The tetrahedral number
`C(n+2, 3)` equals `n·(n+1)·(n+2)/6` exactly — the classical closed form as it
is usually written, recovered from the division-free `six_mul_choose_three` by
dividing by `6` (exact because `n·(n+1)·(n+2)` is divisible by `6`). This is the
`C(n+2, 3) = n(n+1)(n+2)/6` identity promised in the problem statement. -/
theorem choose_three_closed_form (n : ℕ) :
    (n + 2).choose 3 = n * (n + 1) * (n + 2) / 6 := by
  have h := six_mul_choose_three n
  omega

/-- **Classical tetrahedral number formula (with division).** The running total
of the first `n` triangular numbers `T_k = C(k+1, 2)` equals `n·(n+1)·(n+2)/6` —
the classical `∑ T_k = n(n+1)(n+2)/6` written with the familiar `/6`, recovered
from the division-free `six_mul_sum_triangular`. -/
theorem sum_triangular_closed_form (n : ℕ) :
    ∑ k ∈ range (n + 1), (k + 1).choose 2 = n * (n + 1) * (n + 2) / 6 := by
  have h := six_mul_sum_triangular n
  omega

/-- The hockey-stick identity phrased with the elementary triangular number
`T_k = k·(k+1)/2` in place of `C(k+1, 2)`:

`∑_{k<n+1} k·(k+1)/2 = C(n+2, 3)`. -/
theorem sum_triangular_div (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (k + 1) / 2 = (n + 2).choose 3 := by
  rw [← sum_triangular_choose]
  exact Finset.sum_congr rfl fun k _ => (triangular_choose_eq k).symm

end TetrahedralNumberFormula
