import Mathlib

/-
# The Generating Identity for Unsigned Stirling Numbers of the First Kind

## What This Proves
The unsigned Stirling numbers of the first kind `c(n,k) = Nat.stirlingFirst n k` -- the number
of permutations of `n` elements with exactly `k` disjoint cycles -- are exactly the coefficients
of the **rising factorial**

    x^(n↑) = x (x+1) (x+2) ⋯ (x + n − 1) = ascPochhammer R n.

Concretely, as a polynomial identity over any commutative semiring `R`:

    ascPochhammer R n = ∑_{k=0}^{n} c(n,k) • Xᵏ        (`ascPochhammer_eq_sum_stirlingFirst`)

equivalently, coefficient-wise,

    (ascPochhammer R n).coeff k = c(n,k)               (`coeff_ascPochhammer_eq_stirlingFirst`).

## Context / Mathlib gap
Mathlib defines `Nat.stirlingFirst` (`Combinatorics/Enumerative/Stirling.lean`) with its
recurrences, and `ascPochhammer` (`RingTheory/Polynomial/Pochhammer.lean`) with the rising
factorial recurrence -- but it never connects the two. In fact `Nat.stirlingFirst` is not
referenced anywhere outside its own defining file. This entry supplies the missing bridge: the
combinatorial cycle counts ARE the polynomial coefficients of the rising factorial.

## Approach
Induction on `n`, comparing coefficients. The Pochhammer recurrence
`ascPochhammer R (n+1) = ascPochhammer R n * (X + n)` multiplies the coefficient sequence by
`(X + n)`, i.e. sends `coeff k ↦ coeff (k−1) + n · coeff k`. This is exactly the Stirling
recurrence `c(n+1, k) = c(n, k−1) + n · c(n,k)` (`Nat.stirlingFirst_succ_succ`).

## Corollaries
- `eval_ascPochhammer_eq_sum` -- the rising factorial value `x(x+1)⋯(x+n−1) = ∑ c(n,k) xᵏ`.
- `sum_stirlingFirst_eq_factorial` -- the row sum `∑ₖ c(n,k) = n!` (specialise to `x = 1`).
-/

open Polynomial Finset

namespace StirlingFirstGenerating

variable {R : Type*} [CommSemiring R]

/-- **Coefficient form.** The coefficients of the rising factorial `ascPochhammer R n` are the
unsigned Stirling numbers of the first kind: `(ascPochhammer R n).coeff k = c(n,k)`. -/
theorem coeff_ascPochhammer_eq_stirlingFirst (n k : ℕ) :
    (ascPochhammer R n).coeff k = (Nat.stirlingFirst n k : R) := by
  induction n generalizing k with
  | zero =>
    rw [ascPochhammer_zero, coeff_one]
    rcases k with _ | k
    · simp
    · simp
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, coeff_add, ← C_eq_natCast, coeff_mul_C]
    rcases k with _ | m
    · -- constant term: `(P * X)` has no constant coefficient
      rw [mul_coeff_zero, coeff_X_zero, mul_zero, zero_add, ih]
      rcases n with _ | t
      · simp
      · simp
    · -- coefficient of `Xᵐ⁺¹`: the Pochhammer/Stirling recurrence
      rw [coeff_mul_X, ih m, ih (m + 1), Nat.stirlingFirst_succ_succ]
      push_cast
      ring

/-- **Generating identity (headline).** The rising factorial `x(x+1)⋯(x+n−1)` is the polynomial
whose coefficients are the unsigned Stirling numbers of the first kind:
`ascPochhammer R n = ∑_{k=0}^{n} c(n,k) Xᵏ`. -/
theorem ascPochhammer_eq_sum_stirlingFirst (n : ℕ) :
    ascPochhammer R n = ∑ k ∈ range (n + 1), C (Nat.stirlingFirst n k : R) * X ^ k := by
  ext j
  rw [coeff_ascPochhammer_eq_stirlingFirst, finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (range (n + 1)) j (fun k => (Nat.stirlingFirst n k : R))]
  split_ifs with hj
  · rfl
  · rw [Finset.mem_range, not_lt] at hj
    rw [Nat.stirlingFirst_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- **Evaluation form.** The value of the rising factorial: `x(x+1)⋯(x+n−1) = ∑ c(n,k) xᵏ`. -/
theorem eval_ascPochhammer_eq_sum (n : ℕ) (x : R) :
    (ascPochhammer R n).eval x = ∑ k ∈ range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k := by
  rw [ascPochhammer_eq_sum_stirlingFirst, eval_finset_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [eval_mul, eval_C, eval_pow, eval_X]

/-- **Row sum.** The unsigned Stirling numbers of the first kind in row `n` sum to `n!`,
reflecting that the `n!` permutations are partitioned by their number of cycles. -/
theorem sum_stirlingFirst_eq_factorial (n : ℕ) :
    (∑ k ∈ range (n + 1), Nat.stirlingFirst n k) = Nat.factorial n := by
  have h := eval_ascPochhammer_eq_sum (R := ℕ) n 1
  rw [ascPochhammer_eval_one] at h
  simpa using h.symm

end StirlingFirstGenerating
