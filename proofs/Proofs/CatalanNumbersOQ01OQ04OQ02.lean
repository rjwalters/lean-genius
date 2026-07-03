import Mathlib

/-
# Strict log-concavity of the Catalan growth-ratio sequence

The parent leaf `catalan-numbers-oq-01-oq-04` establishes that the Catalan
numbers themselves are strictly log-*convex* (a Turán inequality
`catalan (n+1)^2 < catalan n * catalan (n+2)`).  A log-convex sequence is *not*
log-concave, so to see log-concavity we pass to a sequence *derived* from the
Catalan numbers.  The natural choice is the sequence of consecutive **growth
ratios**

  `ρ n := catalan (n+1) / catalan n`,

which is exactly the multiplier appearing in the first-order recurrence
`(n+2) · catalan (n+1) = 2(2n+1) · catalan n`, namely
`ρ n = 2(2n+1)/(n+2)`.  This problem asks to apply the parent's "surplus"
method to a Catalan-derived sequence and prove a *strict* inequality.

## The result

`ρ` is strictly log-concave:

  `ρ (n) ^ 2 > ρ (n-1) · ρ (n+1)`.

Placed at the middle index `n = m+1` and cleared of denominators (all Catalan
numbers are positive), this is precisely the integer inequality

  `catalan (m+1)^3 * catalan (m+3) < catalan (m+2)^3 * catalan m`.       (★)

## Proof idea (the surplus method, one degree up)

Three consecutive instances of the linear recurrence, written over `ℤ` with
`a = catalan m`, `b = catalan (m+1)`, `c = catalan (m+2)`, `d = catalan (m+3)`:

  `(m+2) b = 2(2m+1) a`,  `(m+3) c = 2(2m+3) b`,  `(m+4) d = 2(2m+5) c`.

Multiplying (★) through by the positive quantity
`K = 2(2m+1)(m+3)^3(m+4)` and repeatedly substituting the recurrences collapses
both sides to a multiple of `b^4`:

  `K · (c^3 a) = 8(2m+3)^3(m+4)(m+2) · b^4`,
  `K · (b^3 d) = 8(2m+1)(2m+5)(2m+3)(m+3)^2 · b^4`.

Their difference is `8(2m+3) · (12m+27) · b^4 > 0`, because the polynomial
surplus

  `(2m+3)^2(m+4)(m+2) − (2m+1)(2m+5)(m+3)^2 = 12m+27`

is strictly positive.  Cancelling `K > 0` gives (★).  Everything is carried out
over `ℤ` (where `linear_combination` and cancellation are available) and
transferred back to `ℕ`.  Mathlib supplies the Catalan API but no such
higher-order (log-concave ratio) inequality.
-/

namespace CatalanNumbersOQ01OQ04OQ02

open Nat

/-- The one-step Catalan recurrence `(n+2) · catalan (n+1) = 2(2n+1) · catalan n`,
over `ℤ`.  Derived from Mathlib's central-binomial recurrence by cancelling the
positive factor `n+1`. -/
theorem catalan_recurrence (n : ℕ) :
    ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) = 2 * (2 * n + 1) * (catalan n : ℤ) := by
  have e1 : ((Nat.centralBinom n : ℤ)) = ((n : ℤ) + 1) * (catalan n : ℤ) := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).symm
  have e2 : ((Nat.centralBinom (n + 1) : ℤ)) = ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom (n + 1)).symm
  have r1 : ((n : ℤ) + 1) * (Nat.centralBinom (n + 1) : ℤ)
      = 2 * (2 * n + 1) * (Nat.centralBinom n : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn1 : ((n : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hn1
  linear_combination r1 + 2 * (2 * n + 1) * e1 - ((n : ℤ) + 1) * e2

/-- Positivity of the Catalan numbers, recovered from the central-binomial API. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h : (n + 1) * catalan n = Nat.centralBinom n :=
    succ_mul_catalan_eq_centralBinom n
  have hb : 0 < Nat.centralBinom n := Nat.centralBinom_pos n
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | hpos
  · rw [h0, Nat.mul_zero] at h; omega
  · exact hpos

/-- **Strict log-concavity of the Catalan growth-ratio sequence.**

For every `m`,
`catalan (m+1)^3 * catalan (m+3) < catalan (m+2)^3 * catalan m`.

Equivalently, the ratio sequence `ρ n = catalan (n+1) / catalan n` is strictly
log-concave: `ρ (m+1)^2 > ρ m * ρ (m+2)`.  The multiplicative surplus is exactly
`(12m+27)` after clearing denominators; Mathlib has the Catalan API but no such
higher-order inequality. -/
theorem catalan_ratio_strict_log_concave (m : ℕ) :
    catalan (m + 1) ^ 3 * catalan (m + 3) < catalan (m + 2) ^ 3 * catalan m := by
  -- Move to `ℤ`.
  zify
  -- Three consecutive recurrence instances, in raw cast form (so `set` folds them).
  have h0 : ((m : ℤ) + 2) * (catalan (m + 1) : ℤ) = 2 * (2 * m + 1) * (catalan m : ℤ) :=
    catalan_recurrence m
  have h1 : ((m : ℤ) + 3) * (catalan (m + 2) : ℤ) = 2 * (2 * m + 3) * (catalan (m + 1) : ℤ) := by
    have h := catalan_recurrence (m + 1)
    have he : m + 1 + 1 = m + 2 := rfl
    rw [he] at h
    push_cast at h ⊢
    linear_combination h
  have h2 : ((m : ℤ) + 4) * (catalan (m + 3) : ℤ) = 2 * (2 * m + 5) * (catalan (m + 2) : ℤ) := by
    have h := catalan_recurrence (m + 2)
    have he : m + 2 + 1 = m + 3 := rfl
    rw [he] at h
    push_cast at h ⊢
    linear_combination h
  have pb : 0 < (catalan (m + 1) : ℤ) := by exact_mod_cast catalan_pos (m + 1)
  have pc : 0 < (catalan (m + 2) : ℤ) := by exact_mod_cast catalan_pos (m + 2)
  -- Abbreviate the four Catalan values.
  set a : ℤ := (catalan m : ℤ) with ha
  set b : ℤ := (catalan (m + 1) : ℤ) with hb
  set c : ℤ := (catalan (m + 2) : ℤ) with hc
  set d : ℤ := (catalan (m + 3) : ℤ) with hd
  -- Cube of the middle recurrence: `((m+3) c)^3 = (2(2m+3) b)^3`.
  have hcube : ((m : ℤ) + 3) ^ 3 * c ^ 3 = 8 * (2 * m + 3) ^ 3 * b ^ 3 := by
    have hh : (((m : ℤ) + 3) * c) ^ 3 = (2 * (2 * m + 3) * b) ^ 3 := by rw [h1]
    linear_combination hh
  -- Collapse `K · (c^3 a)` to a multiple of `b^4`.
  have L : (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4)) * (c ^ 3 * a)
      = 8 * (2 * (m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4) * ((m : ℤ) + 2) * b ^ 4 := by
    linear_combination (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 4) * a) * hcube
      - (8 * (2 * (m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4) * b ^ 3) * h0
  -- Collapse `K · (b^3 d)` to a multiple of `b^4`.
  have Rr : (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4)) * (b ^ 3 * d)
      = 8 * (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 5) * (2 * (m : ℤ) + 3) * ((m : ℤ) + 3) ^ 2 * b ^ 4 := by
    linear_combination (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * b ^ 3) * h2
      + (4 * (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 5) * ((m : ℤ) + 3) ^ 2 * b ^ 3) * h1
  -- The positive quantities.
  have hK : (0 : ℤ) < 2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4) := by positivity
  have hsurplus : (0 : ℤ) < 8 * (2 * (m : ℤ) + 3) * (12 * (m : ℤ) + 27) * b ^ 4 := by positivity
  -- The surplus identity: `X · b^4 − Y · b^4 = 8(2m+3)(12m+27) · b^4`.
  have hXY : 8 * (2 * (m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4) * ((m : ℤ) + 2) * b ^ 4
      - 8 * (2 * (m : ℤ) + 1) * (2 * (m : ℤ) + 5) * (2 * (m : ℤ) + 3) * ((m : ℤ) + 3) ^ 2 * b ^ 4
      = 8 * (2 * (m : ℤ) + 3) * (12 * (m : ℤ) + 27) * b ^ 4 := by ring
  -- Hence `K · (b^3 d) < K · (c^3 a)`, then cancel `K`.
  have hKlt : (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4)) * (b ^ 3 * d)
      < (2 * (2 * (m : ℤ) + 1) * ((m : ℤ) + 3) ^ 3 * ((m : ℤ) + 4)) * (c ^ 3 * a) := by
    rw [L, Rr]; linarith [hsurplus, hXY]
  exact lt_of_mul_lt_mul_left hKlt (le_of_lt hK)

/-- **The ratio form.**  Writing `ρ n = catalan (n+1) / catalan n` for the
consecutive growth ratio (over `ℚ`), the sequence `ρ` is strictly log-concave:

  `ρ m * ρ (m+2) < ρ (m+1) ^ 2`.

This is the content of `catalan_ratio_strict_log_concave` stated as a genuine
log-concavity of the derived sequence. -/
theorem catalan_ratio_log_concave_rat (m : ℕ) :
    ((catalan (m + 1) : ℚ) / catalan m) * ((catalan (m + 3) : ℚ) / catalan (m + 2))
      < ((catalan (m + 2) : ℚ) / catalan (m + 1)) ^ 2 := by
  have pa : (0 : ℚ) < catalan m := by exact_mod_cast catalan_pos m
  have pb : (0 : ℚ) < catalan (m + 1) := by exact_mod_cast catalan_pos (m + 1)
  have pc : (0 : ℚ) < catalan (m + 2) := by exact_mod_cast catalan_pos (m + 2)
  have key : (catalan (m + 1) : ℚ) ^ 3 * catalan (m + 3) < (catalan (m + 2) : ℚ) ^ 3 * catalan m := by
    exact_mod_cast catalan_ratio_strict_log_concave m
  -- The difference of the two sides is a positive numerator over a positive denominator.
  have hnum : (0 : ℚ) < (catalan (m + 2) : ℚ) ^ 3 * catalan m - (catalan (m + 1) : ℚ) ^ 3 * catalan (m + 3) := by
    linarith [key]
  have hden : (0 : ℚ) < (catalan m : ℚ) * catalan (m + 1) ^ 2 * catalan (m + 2) := by positivity
  have hpos : (0 : ℚ) <
      ((catalan (m + 2) : ℚ) ^ 3 * catalan m - (catalan (m + 1) : ℚ) ^ 3 * catalan (m + 3))
        / ((catalan m : ℚ) * catalan (m + 1) ^ 2 * catalan (m + 2)) := div_pos hnum hden
  have expand :
      ((catalan (m + 2) : ℚ) / catalan (m + 1)) ^ 2
        - ((catalan (m + 1) : ℚ) / catalan m) * ((catalan (m + 3) : ℚ) / catalan (m + 2))
      = ((catalan (m + 2) : ℚ) ^ 3 * catalan m - (catalan (m + 1) : ℚ) ^ 3 * catalan (m + 3))
        / ((catalan m : ℚ) * catalan (m + 1) ^ 2 * catalan (m + 2)) := by
    field_simp
    ring
  linarith [hpos, expand]

end CatalanNumbersOQ01OQ04OQ02
