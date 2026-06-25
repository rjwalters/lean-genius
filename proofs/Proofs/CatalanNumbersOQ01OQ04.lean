import Mathlib

/-
# Strict log-convexity of the Catalan numbers (a Turán-type inequality)

For every `n` the Catalan numbers satisfy the **strict** Turán inequality

  `catalan (n+1) ^ 2 < catalan n * catalan (n+2)`.

Equivalently, the sequence `n ↦ catalan n` is *strictly* log-convex.  This is
the leaf `oq-01-oq-04` of `catalan-numbers-oq-01`.

## Proof idea (pointwise, no induction)

The only inputs are two instances of the standard one-step recurrence
`(n+2) · catalan (n+1) = 2(2n+1) · catalan n`, derived here from Mathlib's
central-binomial API:

* `succ_mul_catalan_eq_centralBinom : (n+1) * catalan n = centralBinom n`
* `Nat.succ_mul_centralBinom_succ : (n+1) * centralBinom (n+1)
      = 2(2n+1) * centralBinom n`.

Combining them and cancelling the positive factor `n+1` yields the catalan
recurrence; doing the same one step further gives the `n+1` instance.  Writing
`a = catalan n`, `b = catalan (n+1)`, `c = catalan (n+2)`, the two recurrences

  `(n+2) b = 2(2n+1) a`,   `(n+3) c = 2(2n+3) b`

force, after multiplying out by the positive quantity `2(2n+1)(2n+3)`,

  `D · (a·c) = D · b² + 3 · (b·c)`   with `D = 2(2n+1)(2n+3) > 0`,

because `(2n+3)(n+2) − (2n+1)(n+3) = 3`.  Since `b, c > 0` the surplus
`3 · (b·c)` is strictly positive, so `b² < a·c`.

All arithmetic is carried out over `ℤ` (where `linear_combination` and
cancellation are available) and transferred back to `ℕ` at the end.
-/

namespace CatalanNumbersOQ01OQ04

open Nat

/-- The one-step Catalan recurrence `(n+2) · catalan (n+1) = 2(2n+1) · catalan n`,
expressed over `ℤ`.  Derived from the central-binomial recurrence by cancelling
the positive factor `n+1`. -/
theorem catalan_recurrence (n : ℕ) :
    ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) = 2 * (2 * n + 1) * (catalan n : ℤ) := by
  -- cast the two Mathlib identities to ℤ
  have e1 : ((Nat.centralBinom n : ℤ)) = ((n : ℤ) + 1) * (catalan n : ℤ) := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom n).symm
  have e2 : ((Nat.centralBinom (n + 1) : ℤ)) = ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) := by
    exact_mod_cast (succ_mul_catalan_eq_centralBinom (n + 1)).symm
  have r1 : ((n : ℤ) + 1) * (Nat.centralBinom (n + 1) : ℤ)
      = 2 * (2 * n + 1) * (Nat.centralBinom n : ℤ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hn1 : ((n : ℤ) + 1) ≠ 0 := by positivity
  -- cancel (n+1) after substituting e1, e2 into r1
  apply mul_left_cancel₀ hn1
  linear_combination r1 + 2 * (2 * n + 1) * e1 - ((n : ℤ) + 1) * e2

/-- Positivity of the Catalan numbers, recovered from the central-binomial API:
`(n+1) · catalan n = centralBinom n > 0`, and `n+1 > 0`. -/
theorem catalan_pos (n : ℕ) : 0 < catalan n := by
  have h : (n + 1) * catalan n = Nat.centralBinom n :=
    succ_mul_catalan_eq_centralBinom n
  have hb : 0 < Nat.centralBinom n := Nat.centralBinom_pos n
  -- if catalan n = 0 then (n+1)*catalan n = 0, contradicting centralBinom n > 0
  rcases Nat.eq_zero_or_pos (catalan n) with h0 | hpos
  · rw [h0, Nat.mul_zero] at h; omega
  · exact hpos

/-- **Strict log-convexity (Turán inequality) of the Catalan numbers.**

For every `n`,
`catalan (n+1) ^ 2 < catalan n * catalan (n+2)`.

This is strict for all `n` (the multiplicative gap is exactly the factor
`(2n²+7n+6)/(2n²+7n+3) > 1`); Mathlib has the Catalan API but no Turán-type
inequality. -/
theorem catalan_turan (n : ℕ) :
    catalan (n + 1) ^ 2 < catalan n * catalan (n + 2) := by
  -- Two consecutive recurrence instances, as facts over ℤ.
  have R1 : ((n : ℤ) + 2) * (catalan (n + 1) : ℤ) = 2 * (2 * n + 1) * (catalan n : ℤ) :=
    catalan_recurrence n
  have R2 : ((n : ℤ) + 3) * (catalan (n + 2) : ℤ)
      = 2 * (2 * n + 3) * (catalan (n + 1) : ℤ) := by
    have h := catalan_recurrence (n + 1)
    have he : n + 1 + 1 = n + 2 := rfl
    rw [he] at h
    push_cast at h ⊢
    linear_combination h
  have hBpos : 0 < (catalan (n + 1) : ℤ) := by exact_mod_cast catalan_pos (n + 1)
  have hCpos : 0 < (catalan (n + 2) : ℤ) := by exact_mod_cast catalan_pos (n + 2)
  -- abbreviate; `set` folds the facts above to use A, B, C automatically
  set A : ℤ := (catalan n : ℤ) with hA
  set B : ℤ := (catalan (n + 1) : ℤ) with hB
  set C : ℤ := (catalan (n + 2) : ℤ) with hC
  have hD : (0 : ℤ) < 2 * (2 * n + 1) * (2 * n + 3) := by positivity
  -- the key surplus identity: D·(A·C) = D·B² + 3·(B·C)
  have key : 2 * (2 * n + 1) * (2 * n + 3) * (A * C)
      = 2 * (2 * n + 1) * (2 * n + 3) * B ^ 2 + 3 * (B * C) := by
    linear_combination ((2 * (n : ℤ) + 1) * B) * R2 - (((2 : ℤ) * n + 3) * C) * R1
  -- 3·(B·C) > 0, so D·B² < D·(A·C), hence B² < A·C
  have hbc : 0 < 3 * (B * C) := by positivity
  have hlt : 2 * (2 * n + 1) * (2 * n + 3) * B ^ 2
      < 2 * (2 * n + 1) * (2 * n + 3) * (A * C) := by
    rw [key]; linarith
  have hZ : B ^ 2 < A * C := lt_of_mul_lt_mul_left hlt (le_of_lt hD)
  -- transfer back to ℕ
  rw [hA, hB, hC] at hZ
  exact_mod_cast hZ

end CatalanNumbersOQ01OQ04
