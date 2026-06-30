/-
# Erdős Problem #396 — OQ-04: The Catalan factor of the central binomial recurrence

Erdős Problem #396 asks, for every `k`, whether some `n` satisfies
`n(n−1)⋯(n−k) ∣ C(2n, n)`. The entry point to all such divisibility questions
is the classical fact that `n+1` always divides the central binomial
coefficient `C(2n, n) = Nat.centralBinom n`, giving the integer Catalan numbers
`catalan n = C(2n,n)/(n+1)`.

This follow-up sharpens the **arithmetic of the central binomial recurrence**.
Mathlib provides two facts:

* `Nat.succ_mul_centralBinom_succ`:
    `(n+1) · C(2(n+1), n+1) = 2·(2n+1) · C(2n, n)`
* `succ_mul_catalan_eq_centralBinom`:
    `(n+1) · catalan n = C(2n, n)`

Substituting the second into the first and cancelling the common factor `n+1`
yields a clean **closed form for the next central binomial coefficient in terms
of the current Catalan number**:

  `C(2(n+1), n+1) = 2·(2n+1) · catalan n`.

Mathlib derives the Catalan numbers' integrality through a Gosper-style
telescoping (`gosperCatalan`); it does **not** record this elementary product
form or the resulting two-term Catalan recurrence
`(n+2)·catalan(n+1) = 2·(2n+1)·catalan n`. Both are proved here from scratch,
together with the divisibility refinements they imply for the central binomial
coefficients that drive Problem #396.

Reference: https://erdosproblems.com/396
-/

import Mathlib

open Nat

namespace Erdos396OQ04

/- ## The closed form -/

/-- **Closed form for the successor central binomial coefficient.**
    `C(2(n+1), n+1) = 2·(2n+1) · catalan n`.

    This is obtained by substituting `C(2n,n) = (n+1)·catalan n` into the
    Mathlib recurrence `(n+1)·C(2(n+1),n+1) = 2·(2n+1)·C(2n,n)` and cancelling
    the nonzero factor `n+1`. It exposes the Catalan number as the *exact*
    cofactor of `2(2n+1)` inside the next central binomial coefficient — a form
    Mathlib does not record. -/
theorem centralBinom_succ_eq (n : ℕ) :
    Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom n] at h
  -- h : (n+1) * C(2(n+1),n+1) = 2*(2n+1) * ((n+1) * catalan n)
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega) ?_
  rw [h]; ring

/- ## Divisibility refinements -/

/-- The Catalan number `catalan n` divides the next central binomial
    coefficient `C(2(n+1), n+1)`, with explicit cofactor `2(2n+1)`. -/
theorem catalan_dvd_centralBinom_succ (n : ℕ) :
    catalan n ∣ Nat.centralBinom (n + 1) :=
  ⟨2 * (2 * n + 1), by rw [centralBinom_succ_eq]; ring⟩

/-- `2·(2n+1)` divides the next central binomial coefficient. -/
theorem two_mul_succ_dvd_centralBinom_succ (n : ℕ) :
    2 * (2 * n + 1) ∣ Nat.centralBinom (n + 1) :=
  ⟨catalan n, by rw [centralBinom_succ_eq]⟩

/-- The odd factor `2n+1` divides the next central binomial coefficient.
    (Stronger than Mathlib's `two_dvd_centralBinom_succ`, which only records the
    even factor `2`.) -/
theorem odd_factor_dvd_centralBinom_succ (n : ℕ) :
    (2 * n + 1) ∣ Nat.centralBinom (n + 1) :=
  (dvd_mul_left (2 * n + 1) 2).trans (two_mul_succ_dvd_centralBinom_succ n)

/-- Re-derivation of Mathlib's `two_dvd_centralBinom_succ` as a corollary of the
    closed form: `2 ∣ C(2(n+1), n+1)`. -/
theorem two_dvd_centralBinom_succ (n : ℕ) :
    2 ∣ Nat.centralBinom (n + 1) :=
  (dvd_mul_right 2 (2 * n + 1)).trans (two_mul_succ_dvd_centralBinom_succ n)

/- ## The two-term Catalan recurrence -/

/-- **Elementary two-term Catalan recurrence.**
    `(n+2)·catalan(n+1) = 2·(2n+1)·catalan n`.

    Equivalently `catalan(n+1) = 2(2n+1)/(n+2) · catalan n`, the standard
    recurrence used to compute Catalan numbers without binomial coefficients.
    Mathlib proves integrality of `catalan` via the Gosper telescoping but does
    not state this recurrence directly. -/
theorem catalan_recurrence (n : ℕ) :
    (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * catalan n := by
  have h := succ_mul_catalan_eq_centralBinom (n + 1)
  -- h : (n+1+1) * catalan (n+1) = C(2(n+1), n+1)
  rw [centralBinom_succ_eq] at h
  exact h

/-- `n+2` divides `2·(2n+1)·catalan n` (the divisibility content of the
    recurrence: `(n+2)` is absorbed by the right-hand product). -/
theorem succ_succ_dvd (n : ℕ) :
    (n + 2) ∣ 2 * (2 * n + 1) * catalan n :=
  ⟨catalan (n + 1), (catalan_recurrence n).symm⟩

/- ## Coprimality of the two divisors -/

/-- The two natural divisors `n+1` and `2n+1` of consecutive central binomial
    coefficients are coprime. (gcd peels: `2n+1 = n + 1·(n+1)`, reducing to
    `gcd(n+1, n) = gcd(n, 1) = 1`.) -/
theorem coprime_succ_two_mul_succ (n : ℕ) :
    Nat.Coprime (n + 1) (2 * n + 1) := by
  have h : 2 * n + 1 = n + 1 * (n + 1) := by ring
  rw [h, Nat.coprime_add_mul_right_right, Nat.coprime_comm,
      Nat.coprime_self_add_right]
  exact Nat.coprime_one_right n

/- ## Sanity checks against the explicit Catalan values -/

/-- `C(2·1, 1) = 2 = 2·(2·0+1)·catalan 0`. -/
example : Nat.centralBinom 1 = 2 * (2 * 0 + 1) * catalan 0 :=
  centralBinom_succ_eq 0

/-- `C(2·3, 3) = C(6,3) = 20 = 2·(2·2+1)·catalan 2 = 2·5·2`. -/
example : Nat.centralBinom 3 = 20 := by decide

/-- Recurrence check at `n = 2`: `4·catalan 3 = 2·5·catalan 2`, i.e. `4·5 = 20`. -/
example : (2 + 2) * catalan (2 + 1) = 2 * (2 * 2 + 1) * catalan 2 :=
  catalan_recurrence 2

end Erdos396OQ04
