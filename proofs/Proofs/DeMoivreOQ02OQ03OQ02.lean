/-
# Degree and Leading Coefficient of the Chebyshev Polynomials Tₙ

For the first-kind Chebyshev polynomials `T n` (Mathlib's `Polynomial.Chebyshev.T`)
over `ℤ`, this file proves the two facts that Mathlib's `Chebyshev` file lists as
open TODOs ("Compute zeroes and extrema", which presuppose the degree):

* `natDegree (T ℤ n) = n`;
* `leadingCoeff (T ℤ n) = 2 ^ (n - 1)`  (so `Tₙ` has leading coefficient `2ⁿ⁻¹`
  for `n ≥ 1`, and `T₀ = 1`).

Mathlib provides the defining three-term recurrence
`T (n+2) = 2·X·T (n+1) − T n` with `T 0 = 1`, `T 1 = X`, but records no degree
or leading-coefficient lemma; both results here are fresh.

## Strategy

A single two-step induction on `n` tracking `natDegree` and `leadingCoeff`
simultaneously.  Base cases `T 0 = 1` (degree 0, leading coeff `1 = 2⁰`) and
`T 1 = X` (degree 1, leading coeff `1 = 2⁰`).  For the step, write
`T (n+2) = 2·X·T (n+1) − T n`.  Over the domain `ℤ`:

* `2·X·T (n+1)` has degree `1 + (n+1) = n+2` and leading coefficient
  `2 · 2ⁿ = 2ⁿ⁺¹` (degree and leading coefficient are additive/multiplicative
  on products of nonzero polynomials);
* `T n` has degree `n < n+2`, so subtracting it changes neither the degree
  nor the leading coefficient of the `n+2` term.

Hence `natDegree (T (n+2)) = n+2` and `leadingCoeff (T (n+2)) = 2ⁿ⁺¹`, completing
the induction.  Using `ℕ`-subtraction in the exponent `2 ^ (n-1)` makes the
formula uniform across `n = 0` (`2⁰ = 1`) without a special case.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Polynomial Polynomial.Chebyshev

namespace DeMoivreOQ02OQ03OQ02

/-- `2 * X` over `ℤ` has `natDegree` one and leading coefficient `2`. -/
theorem natDegree_two_mul_X : (2 * X : ℤ[X]).natDegree = 1 := by
  have : (2 * X : ℤ[X]) = C 2 * X := by simp
  rw [this, natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0), natDegree_X]

theorem leadingCoeff_two_mul_X : (2 * X : ℤ[X]).leadingCoeff = 2 := by
  have : (2 * X : ℤ[X]) = C 2 * X := by simp
  rw [this, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]

theorem two_mul_X_ne_zero : (2 * X : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_two_mul_X, natDegree_zero] at this
  exact one_ne_zero this

/-- **Degree and leading coefficient of `Tₙ`.**  Over `ℤ`, the `n`-th first-kind
Chebyshev polynomial has degree `n` and leading coefficient `2 ^ (n-1)`. -/
theorem T_natDegree_leadingCoeff (n : ℕ) :
    (T ℤ (n : ℤ)).natDegree = n ∧ (T ℤ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero =>
      constructor
      · simp
      · simp
  | one =>
      constructor
      · simp [T_one]
      · simp [T_one]
  | more n ih0 ih1 =>
      obtain ⟨hd0, hl0⟩ := ih0
      obtain ⟨hd1, hl1⟩ := ih1
      -- The defining recurrence, with the index cast through ℕ.
      have hrec : T ℤ ((n + 2 : ℕ) : ℤ)
          = 2 * X * T ℤ ((n + 1 : ℕ) : ℤ) - T ℤ ((n : ℕ) : ℤ) := by
        have h := T_add_two ℤ (n : ℤ)
        push_cast
        push_cast at h
        linear_combination h
      -- `T (n+1) ≠ 0` since its leading coefficient `2ⁿ` is nonzero.
      have hTn1_ne : T ℤ ((n + 1 : ℕ) : ℤ) ≠ 0 := by
        intro h0
        rw [h0, leadingCoeff_zero] at hl1
        have : (2 : ℤ) ^ (n + 1 - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        exact this hl1.symm
      -- Degree and leading coefficient of `A := 2·X·T (n+1)`.
      have hdA : (2 * X * T ℤ ((n + 1 : ℕ) : ℤ)).natDegree = n + 2 := by
        rw [natDegree_mul two_mul_X_ne_zero hTn1_ne, natDegree_two_mul_X, hd1]
        omega
      have hlA : (2 * X * T ℤ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ (n + 1) := by
        rw [leadingCoeff_mul, leadingCoeff_two_mul_X, hl1]
        have : n + 1 - 1 = n := by omega
        rw [this]; ring
      -- `T n` has strictly smaller degree.
      have hdeg_lt : (T ℤ ((n : ℕ) : ℤ)).natDegree
          < (2 * X * T ℤ ((n + 1 : ℕ) : ℤ)).natDegree := by
        rw [hdA, hd0]; omega
      constructor
      · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hdeg_lt, hdA]
      · rw [hrec]
        have hsub : (2 * X * T ℤ ((n + 1 : ℕ) : ℤ) - T ℤ ((n : ℕ) : ℤ)).leadingCoeff
            = (2 * X * T ℤ ((n + 1 : ℕ) : ℤ)).leadingCoeff := by
          rw [sub_eq_add_neg]
          rw [leadingCoeff_add_of_degree_lt']
          rw [degree_neg]
          exact degree_lt_degree hdeg_lt
        rw [hsub, hlA]
        have : n + 2 - 1 = n + 1 := by omega
        rw [this]

/-- **Degree of `Tₙ`.**  `natDegree (T ℤ n) = n`. -/
theorem T_natDegree (n : ℕ) : (T ℤ (n : ℤ)).natDegree = n :=
  (T_natDegree_leadingCoeff n).1

/-- **Leading coefficient of `Tₙ`.**  `leadingCoeff (T ℤ n) = 2 ^ (n-1)`
(so `Tₙ` has leading coefficient `2ⁿ⁻¹` for `n ≥ 1`, and `T₀ = 1`). -/
theorem T_leadingCoeff (n : ℕ) : (T ℤ (n : ℤ)).leadingCoeff = 2 ^ (n - 1) :=
  (T_natDegree_leadingCoeff n).2

/-- For `n ≥ 1`, the leading coefficient of `Tₙ` is `2ⁿ⁻¹`, written without
truncated subtraction. -/
theorem T_leadingCoeff_succ (n : ℕ) :
    (T ℤ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ n := by
  have := T_leadingCoeff (n + 1)
  simpa using this

end DeMoivreOQ02OQ03OQ02
