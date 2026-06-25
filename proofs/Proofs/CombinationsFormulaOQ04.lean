import Mathlib

/-
# Combinations Formula — OQ-04: Log-Concavity of a Pascal Row

## Research Problem: combinations-formula-oq-04

The parent (`combinations-formula`) is the basic count `C(n,k) = n!/(k!(n-k)!)`, and the large
sibling family develops binomial *identities* — Vandermonde, hockey-stick, Catalan numbers,
sums of squares, weighted moments, alternating sums, q-analogs.  Every one of them is an
*equality*.

This file proves the row's fundamental *inequality*: **each Pascal row `k ↦ C(n,k)` is
log-concave**,

      C(n,k) · C(n,k+2)  ≤  C(n,k+1)²        for all n, k,

with **strict** inequality throughout the interior (`k + 2 ≤ n`).  This is the binomial case of
Newton's inequalities and the structural reason the row is unimodal (Mathlib already has the
unimodal maximum `Nat.choose_le_middle`, but not the log-concavity that underlies it).  Mathlib
has the ratio relation `Nat.choose_succ_right_eq` but no log-concavity statement.

## The mechanism

Write `a = C(n,k)`, `b = C(n,k+1)`, `c = C(n,k+2)`.  Mathlib's `choose_succ_right_eq` gives the
two adjacent-ratio relations (after substituting `n = k + 2 + t`, eliminating all truncated
subtraction):

      a · (t+2) = b · (k+1),        c · (k+2) = b · (t+1).

Multiplying,

      a · c · (t+2)(k+2)  =  b² · (k+1)(t+1).

Since `(k+1)(t+1) < (t+2)(k+2)` — their difference is `t + k + 3 > 0` — and `(t+2)(k+2) > 0`,
cancelling the common positive factor yields `a · c ≤ b²` (strictly when `b > 0`, i.e. in the
interior).  Outside the row (`n < k+2`) the coefficient `c` vanishes and the bound is trivial.

## What is proved

* `choose_mul_choose_le_sq` — `C(n,k) · C(n,k+2) ≤ C(n,k+1)²` for all `n, k`.
* `choose_mul_choose_lt_sq` — the strict form for `k + 2 ≤ n`.
* `choose_mul_choose_le_sq'` — the centered restatement `C(n,j−1) · C(n,j+1) ≤ C(n,j)²`.

Tags: combinatorics, binomial-coefficients, pascals-triangle, log-concavity, newton-inequality
-/

namespace CombinationsFormulaOQ04

open Nat

/-- **Log-concavity of a Pascal row.**  Along any fixed row `n`, consecutive binomial
    coefficients satisfy `C(n,k) · C(n,k+2) ≤ C(n,k+1)²`.  Outside the row the right factor
    vanishes and the bound is trivial; inside, it is the cancelled form of the two
    adjacent-ratio relations from `choose_succ_right_eq`. -/
theorem choose_mul_choose_le_sq (n k : ℕ) :
    n.choose k * n.choose (k + 2) ≤ (n.choose (k + 1)) ^ 2 := by
  rcases lt_or_ge n (k + 2) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · obtain ⟨t, rfl⟩ : ∃ t, n = k + 2 + t := ⟨n - (k + 2), by omega⟩
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
    have hmul : a * c * ((t + 2) * (k + 2)) = b ^ 2 * ((k + 1) * (t + 1)) := by
      have step : a * c * ((t + 2) * (k + 2)) = (a * (t + 2)) * (c * (k + 2)) := by ring
      rw [step, e1, e2]; ring
    have hle : (k + 1) * (t + 1) ≤ (t + 2) * (k + 2) := by nlinarith
    have hpos : 0 < (t + 2) * (k + 2) := by positivity
    have hfinal : a * c * ((t + 2) * (k + 2)) ≤ b ^ 2 * ((t + 2) * (k + 2)) := by
      rw [hmul]; exact Nat.mul_le_mul (le_refl (b ^ 2)) hle
    exact Nat.le_of_mul_le_mul_right hfinal hpos

/-- **Strict log-concavity in the interior of the row.**  For `k + 2 ≤ n`, the inequality is
    strict: `C(n,k) · C(n,k+2) < C(n,k+1)²`.  This is the binomial case of Newton's
    inequalities. -/
theorem choose_mul_choose_lt_sq (n k : ℕ) (h : k + 2 ≤ n) :
    n.choose k * n.choose (k + 2) < (n.choose (k + 1)) ^ 2 := by
  obtain ⟨t, rfl⟩ : ∃ t, n = k + 2 + t := ⟨n - (k + 2), by omega⟩
  have R1 : (k + 2 + t).choose (k + 1) * (k + 1) = (k + 2 + t).choose k * (t + 2) := by
    have := Nat.choose_succ_right_eq (k + 2 + t) k
    simpa [show (k + 2 + t) - k = t + 2 by omega] using this
  have R2 : (k + 2 + t).choose (k + 2) * (k + 2) = (k + 2 + t).choose (k + 1) * (t + 1) := by
    have := Nat.choose_succ_right_eq (k + 2 + t) (k + 1)
    simpa [show (k + 2 + t) - (k + 1) = t + 1 by omega] using this
  set a := (k + 2 + t).choose k
  set b := (k + 2 + t).choose (k + 1) with hb
  set c := (k + 2 + t).choose (k + 2)
  have e1 : a * (t + 2) = b * (k + 1) := R1.symm
  have e2 : c * (k + 2) = b * (t + 1) := R2
  have hmul : a * c * ((t + 2) * (k + 2)) = b ^ 2 * ((k + 1) * (t + 1)) := by
    have step : a * c * ((t + 2) * (k + 2)) = (a * (t + 2)) * (c * (k + 2)) := by ring
    rw [step, e1, e2]; ring
  have hbpos : 0 < b := by rw [hb]; exact Nat.choose_pos (by omega)
  have hlt : (k + 1) * (t + 1) < (t + 2) * (k + 2) := by nlinarith
  have hfinal : a * c * ((t + 2) * (k + 2)) < b ^ 2 * ((t + 2) * (k + 2)) := by
    rw [hmul]; gcongr
  exact Nat.lt_of_mul_lt_mul_right hfinal

/-- **Centered restatement.**  Rewriting `k = j − 1`, for `1 ≤ j` the row is log-concave at the
    interior index `j`: `C(n,j−1) · C(n,j+1) ≤ C(n,j)²`. -/
theorem choose_mul_choose_le_sq' (n j : ℕ) (hj : 1 ≤ j) :
    n.choose (j - 1) * n.choose (j + 1) ≤ (n.choose j) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simpa using choose_mul_choose_le_sq n k

#check @choose_mul_choose_le_sq
#check @choose_mul_choose_lt_sq
#check @choose_mul_choose_le_sq'

/-
## Summary

Proved (0 sorries, 0 axioms; imports only Mathlib):

* `choose_mul_choose_le_sq` — every Pascal row is log-concave:
  `C(n,k) · C(n,k+2) ≤ C(n,k+1)²` for all `n, k`.
* `choose_mul_choose_lt_sq` — strict in the interior `k + 2 ≤ n` (Newton's inequality).
* `choose_mul_choose_le_sq'` — the centered form `C(n,j−1) · C(n,j+1) ≤ C(n,j)²`.

Where the sibling family records binomial *identities*, this entry supplies the row's basic
*inequality*: log-concavity, the structural fact underlying unimodality
(`Nat.choose_le_middle`).  The proof clears denominators with Mathlib's adjacent-ratio relation
`choose_succ_right_eq` and reduces to `(k+1)(t+1) < (t+2)(k+2)`, whose difference `t + k + 3`
is manifestly positive.
-/

end CombinationsFormulaOQ04
