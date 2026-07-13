import Proofs.TetrahedralNumberFormulaOQ01

/-
# Uniform Cleared-Denominator Polynomial Form for Higher-Dimensional Figurate Sums

## Open Question (tetrahedral-number-formula-oq-02)

The base entry `TetrahedralNumberFormula` gives the `d = 3` cleared-denominator
identity for the running total of triangular numbers,

    6 · ∑_{k≤n} C(k+1, 2) = n·(n+1)·(n+2),

and the follow-up `TetrahedralNumberFormulaOQ01` proves, separately, the
general-dimension hockey-stick identity `sum_simplex`

    ∑_{k≤n} P_d(k) = P_{d+1}(n)          where `P_d(n) = C(n+d, d)`,

and the general-dimension cleared closed form `factorial_mul_simplexNumber_prod`

    d! · P_d(n) = ∏_{i<d} (n+1+i).

This entry supplies the missing **uniform** statement that ties the two together:
a single division-free polynomial identity for the *partial sum itself*, valid
for every dimension `d` at once.

## Result

Let `S_d(n) = ∑_{k≤n} P_d(k)` be the running total of the `d`-dimensional
figurate row. Then

* `factorial_mul_sum_simplex` :
    `(d+1)! · S_d(n) = ∏_{i<d+1} (n+1+i) = (n+1)(n+2)⋯(n+d+1)`
  — the uniform cleared-denominator polynomial form. The right side is an
  explicit product of `d+1` consecutive integers, a monic polynomial of degree
  `d+1` in `n`; the left side clears the sole `(d+1)!` denominator of the closed
  form `S_d(n) = C(n+d+1, d+1)`.

* `factorial_mul_sum_simplex_asc` : the same with the product written as the
  ascending factorial `(n+1)^{(d+1)} = (n+1).ascFactorial (d+1)`.

* `sum_simplex_closed` : `S_d(n) = C(n+d+1, d+1)` — the closed form as a single
  binomial coefficient.

* `factorial_dvd_prod_consec` : `(d+1)! ∣ ∏_{i<d+1} (n+1+i)` — the integrality
  content: a product of `d+1` consecutive integers is divisible by `(d+1)!`
  (obtained here as a corollary of the cleared identity, since the quotient is
  exactly `S_d(n)`).

* `sum_simplex_eq_prod_div` : `S_d(n) = (∏_{i<d+1} (n+1+i)) / (d+1)!` — the
  classical division form, now with the division proved exact.

* `sum_simplex_two`, `sum_simplex_three` : the `d = 2` and `d = 3` rungs written
  out, `6·S_2(n) = (n+1)(n+2)(n+3)` and `24·S_3(n) = (n+1)(n+2)(n+3)(n+4)`,
  recovering the parent's tetrahedral pattern one dimension up the ladder.

## Novelty

`OQ01` proves the hockey-stick identity and the closed-form product *separately*;
neither file states the combined cleared-denominator identity for the partial
sum, nor the resulting `(d+1)! ∣ ∏` integrality corollary in this uniform,
dimension-free shape. Every result below is an immediate but previously
unrecorded composition of the two `OQ01` lemmas.

0 sorries, 0 axioms.
-/

namespace TetrahedralNumberFormulaOQ02

open Finset TetrahedralNumberFormulaOQ01

/-- The running total of the `d`-dimensional figurate row, `S_d(n) = ∑_{k≤n} P_d(k)`. -/
abbrev figurateSum (d n : ℕ) : ℕ := ∑ k ∈ range (n + 1), simplexNumber d k

/-- **Uniform cleared-denominator polynomial form.** For every dimension `d`,

`(d+1)! · S_d(n) = ∏_{i<d+1} (n+1+i) = (n+1)(n+2)⋯(n+d+1)`.

The single sum `S_d(n)`, cleared of its unique `(d+1)!` denominator, is exactly
the product of the `d+1` consecutive integers `n+1, …, n+d+1`. This is the
dimension-free companion to the parent's `6·∑ triangular = n(n+1)(n+2)`. -/
theorem factorial_mul_sum_simplex (d n : ℕ) :
    Nat.factorial (d + 1) * figurateSum d n = ∏ i ∈ range (d + 1), (n + 1 + i) := by
  unfold figurateSum
  rw [sum_simplex, factorial_mul_simplexNumber_prod]

/-- The uniform cleared form with the product written as an ascending factorial:
`(d+1)! · S_d(n) = (n+1)^{(d+1)}`. -/
theorem factorial_mul_sum_simplex_asc (d n : ℕ) :
    Nat.factorial (d + 1) * figurateSum d n = (n + 1).ascFactorial (d + 1) := by
  unfold figurateSum
  rw [sum_simplex, factorial_mul_simplexNumber]

/-- **Closed form of the figurate sum as a single binomial coefficient:**
`S_d(n) = C(n+d+1, d+1)`. The `d`-dimensional hockey-stick identity read as the
`(d+1)`-dimensional simplex number. -/
theorem sum_simplex_closed (d n : ℕ) :
    figurateSum d n = (n + d + 1).choose (d + 1) := by
  unfold figurateSum
  rw [sum_simplex, simplexNumber, show n + (d + 1) = n + d + 1 from by ring]

/-- **Integrality corollary.** The product of `d+1` consecutive integers
`(n+1)(n+2)⋯(n+d+1)` is divisible by `(d+1)!`. Immediate from the cleared
identity: the quotient is precisely `S_d(n)`, an honest natural number. -/
theorem factorial_dvd_prod_consec (d n : ℕ) :
    Nat.factorial (d + 1) ∣ ∏ i ∈ range (d + 1), (n + 1 + i) := by
  rw [← factorial_mul_sum_simplex]
  exact Dvd.intro _ rfl

/-- **Classical division form, with the division proved exact.**
`S_d(n) = (∏_{i<d+1} (n+1+i)) / (d+1)!`. -/
theorem sum_simplex_eq_prod_div (d n : ℕ) :
    figurateSum d n = (∏ i ∈ range (d + 1), (n + 1 + i)) / Nat.factorial (d + 1) := by
  rw [← factorial_mul_sum_simplex, Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]

/-- **Dimension `d = 2` rung.** `6 · S_2(n) = (n+1)(n+2)(n+3)`: the running total
of the two-dimensional figurate (triangular) row, cleared of denominators, is a
product of three consecutive integers — the tetrahedral pattern one step up from
the parent entry. -/
theorem sum_simplex_two (n : ℕ) :
    6 * figurateSum 2 n = (n + 1) * (n + 2) * (n + 3) := by
  have h := factorial_mul_sum_simplex 2 n
  rw [show Nat.factorial (2 + 1) = 6 from rfl] at h
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero]
  ring

/-- **Dimension `d = 3` rung.** `24 · S_3(n) = (n+1)(n+2)(n+3)(n+4)`: the running
total of the three-dimensional (tetrahedral) figurate row cleared to a product of
four consecutive integers. -/
theorem sum_simplex_three (n : ℕ) :
    24 * figurateSum 3 n = (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
  have h := factorial_mul_sum_simplex 3 n
  rw [show Nat.factorial (3 + 1) = 24 from rfl] at h
  rw [h, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_zero]
  ring

end TetrahedralNumberFormulaOQ02
