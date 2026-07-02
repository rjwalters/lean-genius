import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-
# Combinations Formula — OQ-04 → OQ-03: Ultra-Log-Concavity of a Pascal Row (exact form)

## Research Problem: combinations-formula-oq-04-oq-03

The parent (`combinations-formula-oq-04`, "Log-Concavity of a Pascal Row") proves the
*inequality*

      C(n,k) · C(n,k+2)  ≤  C(n,k+1)²,

by clearing denominators with Mathlib's adjacent-ratio relation `Nat.choose_succ_right_eq` and
then **discarding** the exact multiplicative factor.  Its first listed open question asks to
strengthen this to *ultra-log-concavity* (ULC).

This file supplies that strengthening by keeping the factor that the parent threw away.  The
adjacent-ratio relations multiply to an **exact identity**:

      C(n,k) · C(n,k+2) · (n−k)(k+2)  =  C(n,k+1)² · (k+1)(n−k−1).            (★)

Equivalently, writing the middle index as `j = k+1`,

      C(n,j−1) · C(n,j+1) · (j+1)(n−j+1)  =  C(n,j)² · j(n−j),

which is Liggett's ultra-log-concavity bound

      C(n,j)²  =  (1 + 1/j)(1 + 1/(n−j)) · C(n,j−1) · C(n,j+1)

met with **equality**.  So the binomial row is the *extremal* ultra-log-concave sequence: no
sequence indexed against `C(n,·)` can do better.  The parent's log-concavity `a·c ≤ b²` drops
straight out of (★) because `(k+1)(n−k−1) ≤ (n−k)(k+2)` (their difference is `n+1 > 0`), so
the exact identity is strictly more information.

## Mechanism

For `k + 2 ≤ n` write `n = k + 2 + t`.  `Nat.choose_succ_right_eq` gives the two ratios

      a·(t+2) = b·(k+1),        c·(k+2) = b·(t+1),

with `a = C(n,k)`, `b = C(n,k+1)`, `c = C(n,k+2)`.  Multiplying eliminates `b`'s neighbours and
`ring` closes (★).  Outside the row (`n < k+2`) both sides vanish: `C(n,k+2) = 0` kills the left
side, and `n − k − 1 = 0` (truncated subtraction, since `n − k ≤ 1`) kills the right — so (★)
in fact holds for **all** `n, k`, with no side conditions.

## What is proved

* `choose_mul_choose_mul_eq`      — the exact identity (★), for all `n, k`.
* `choose_ulc_equality`           — centered form: `C(n,j−1)·C(n,j+1)·(j+1)(n−j+1) = C(n,j)²·j(n−j)`.
* `choose_mul_choose_le_sq`       — log-concavity re-derived as a corollary of (★).
* `choose_mul_choose_lt_sq`       — strict interior form, from the *strict* factor inequality.

Tags: combinatorics, binomial-coefficients, pascals-triangle, log-concavity, ultra-log-concavity,
newton-inequality
-/

namespace CombinationsFormulaOQ04OQ03

open Nat

/-- **Exact adjacent-triple identity (★).**  For every `n, k`,

      C(n,k) · C(n,k+2) · ((n−k)(k+2))  =  C(n,k+1)² · ((k+1)(n−k−1)).

This is the equality behind the parent's log-concavity inequality: the parent keeps only that the
left factor `(k+1)(n−k−1)` is `≤` the right factor `(n−k)(k+2)` and discards the rest.  Here we
retain the whole identity.  It holds unconditionally — outside the row both sides are `0`. -/
theorem choose_mul_choose_mul_eq (n k : ℕ) :
    n.choose k * n.choose (k + 2) * ((n - k) * (k + 2))
      = (n.choose (k + 1)) ^ 2 * ((k + 1) * (n - k - 1)) := by
  rcases lt_or_ge n (k + 2) with h | h
  · -- Outside the row: `C(n,k+2) = 0` and `n − k − 1 = 0` (since `n − k ≤ 1`).
    have hz : n - k - 1 = 0 := by omega
    rw [Nat.choose_eq_zero_of_lt h, hz]; ring
  · -- Interior: parametrise `n = k + 2 + t`; the subtractions become `t + 2`, `t + 1`.
    obtain ⟨t, rfl⟩ : ∃ t, n = k + 2 + t := ⟨n - (k + 2), by omega⟩
    have R1 : (k + 2 + t).choose (k + 1) * (k + 1) = (k + 2 + t).choose k * (t + 2) := by
      have := Nat.choose_succ_right_eq (k + 2 + t) k
      simpa [show (k + 2 + t) - k = t + 2 by omega] using this
    have R2 : (k + 2 + t).choose (k + 2) * (k + 2) = (k + 2 + t).choose (k + 1) * (t + 1) := by
      have := Nat.choose_succ_right_eq (k + 2 + t) (k + 1)
      simpa [show (k + 2 + t) - (k + 1) = t + 1 by omega] using this
    set a := (k + 2 + t).choose k
    set b := (k + 2 + t).choose (k + 1)
    set c := (k + 2 + t).choose (k + 2)
    have e1 : a * (t + 2) = b * (k + 1) := R1.symm
    have e2 : c * (k + 2) = b * (t + 1) := R2
    -- `(n − k) = t + 2`, `(n − k − 1) = t + 1`.  Rewrite the `−1` form first so the shorter
    -- pattern `(k+2+t) − k` does not consume it.
    rw [show (k + 2 + t) - k - 1 = t + 1 by omega, show (k + 2 + t) - k = t + 2 by omega]
    calc a * c * ((t + 2) * (k + 2))
        = (a * (t + 2)) * (c * (k + 2)) := by ring
      _ = (b * (k + 1)) * (b * (t + 1)) := by rw [e1, e2]
      _ = b ^ 2 * ((k + 1) * (t + 1)) := by ring

/-- **Ultra-log-concavity, exact centered form.**  With middle index `j = k+1`,

      C(n,j−1) · C(n,j+1) · ((j+1)(n−j+1))  =  C(n,j)² · (j(n−j)).

This is Liggett's ULC bound `C(n,j)² = (1 + 1/j)(1 + 1/(n−j))·C(n,j−1)·C(n,j+1)` met with
equality: the Pascal row is the extremal ultra-log-concave sequence.  Stated in the row's range
`1 ≤ j ≤ n`, where the centered factor `n − j + 1` carries its intended value. -/
theorem choose_ulc_equality (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    n.choose (j - 1) * n.choose (j + 1) * ((j + 1) * (n - j + 1))
      = (n.choose j) ^ 2 * (j * (n - j)) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have key := choose_mul_choose_mul_eq n k
  -- Rewrite the `+1` (longer) subtraction pattern before the bare one so it is not consumed.
  rw [show (k + 1) - 1 = k by omega, show (k + 1) + 1 = k + 2 by omega,
      show n - (k + 1) + 1 = n - k by omega, show n - (k + 1) = n - k - 1 by omega]
  calc n.choose k * n.choose (k + 2) * ((k + 2) * (n - k))
      = n.choose k * n.choose (k + 2) * ((n - k) * (k + 2)) := by ring
    _ = (n.choose (k + 1)) ^ 2 * ((k + 1) * (n - k - 1)) := key

/-- **Log-concavity as a corollary of (★).**  `C(n,k) · C(n,k+2) ≤ C(n,k+1)²`.  Multiply the
target by the positive factor `(n−k)(k+2)`, apply the exact identity (★), and bound
`(k+1)(n−k−1) ≤ (n−k)(k+2)`.  This re-derives the parent inequality from strictly sharper data. -/
theorem choose_mul_choose_le_sq (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases lt_or_ge n (k + 2) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · -- `(n − k)(k + 2) > 0`; cancel it after using (★).
    obtain ⟨d, hd⟩ : ∃ d, n - k = d + 2 := ⟨n - k - 2, by omega⟩
    have hpos : 0 < (n - k) * (k + 2) := by rw [hd]; positivity
    have hle : (k + 1) * (n - k - 1) ≤ (n - k) * (k + 2) := by
      rw [hd, show d + 2 - 1 = d + 1 by omega]; nlinarith
    have key := choose_mul_choose_mul_eq n k
    have hstep : n.choose k * n.choose (k + 2) * ((n - k) * (k + 2))
        ≤ (n.choose (k + 1)) ^ 2 * ((n - k) * (k + 2)) := by
      rw [key]; exact Nat.mul_le_mul (le_refl _) hle
    exact Nat.le_of_mul_le_mul_right hstep hpos

/-- **Strict log-concavity in the interior** (`k + 2 ≤ n`).  Same as above but the factor
inequality is strict and `C(n,k+1) > 0`. -/
theorem choose_mul_choose_lt_sq (n k : ℕ) (h : k + 2 ≤ n) :
    n.choose k * n.choose (k + 2) < (n.choose (k + 1)) ^ 2 := by
  obtain ⟨d, hd⟩ : ∃ d, n - k = d + 2 := ⟨n - k - 2, by omega⟩
  have hpos : 0 < (n - k) * (k + 2) := by rw [hd]; positivity
  have hlt : (k + 1) * (n - k - 1) < (n - k) * (k + 2) := by
    rw [hd, show d + 2 - 1 = d + 1 by omega]; nlinarith
  have key := choose_mul_choose_mul_eq n k
  have hpow : 0 < (n.choose (k + 1)) ^ 2 := pow_pos (Nat.choose_pos (by omega)) 2
  have hstep : n.choose k * n.choose (k + 2) * ((n - k) * (k + 2))
      < (n.choose (k + 1)) ^ 2 * ((n - k) * (k + 2)) := by
    rw [key]; exact mul_lt_mul_of_pos_left hlt hpow
  exact Nat.lt_of_mul_lt_mul_right hstep

#check @choose_mul_choose_mul_eq
#check @choose_ulc_equality
#check @choose_mul_choose_le_sq
#check @choose_mul_choose_lt_sq

/-
## Summary

Proved (0 sorries, 0 axioms; imports only Mathlib):

* `choose_mul_choose_mul_eq` — the **exact** adjacent-triple identity (★)
  `C(n,k)·C(n,k+2)·(n−k)(k+2) = C(n,k+1)²·(k+1)(n−k−1)`, for all `n, k`.
* `choose_ulc_equality` — its centered form = Liggett's ultra-log-concavity bound met with
  equality, exhibiting the Pascal row as the extremal ULC sequence.
* `choose_mul_choose_le_sq` / `choose_mul_choose_lt_sq` — the parent's log-concavity (weak and
  strict) recovered as immediate corollaries of the exact identity.

Where the parent (`combinations-formula-oq-04`) proves the log-concavity *inequality* by
discarding the exact multiplicative factor, this entry keeps that factor: the resulting equality
is strictly more information and settles the parent's ultra-log-concavity open question.
-/

end CombinationsFormulaOQ04OQ03
