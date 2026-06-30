/-
# Degree and Leading Coefficient of the Second-Kind Chebyshev Polynomials Uₙ

For the second-kind Chebyshev polynomials `U n` (Mathlib's `Polynomial.Chebyshev.U`)
over `ℤ`, this file proves

* `natDegree (U ℤ n) = n`;
* `leadingCoeff (U ℤ n) = 2 ^ n`.

This is the second-kind companion to `DeMoivreOQ02OQ03OQ02` (which handled the
first-kind `Tₙ`, with `leadingCoeff (T ℤ n) = 2 ^ (n-1)`).  Mathlib's
`RingTheory/Polynomial/Chebyshev.lean` provides the defining three-term
recurrence `U (n+2) = 2·X·U (n+1) − U n` with `U 0 = 1`, `U 1 = 2·X`, but records
no degree or leading-coefficient lemma for either family — both results here are
fresh.

The second-kind formula is *cleaner* than the first-kind one: because
`U 1 = 2·X` already carries the factor of two, the leading coefficient is the
uniform `2 ^ n` with no truncated subtraction, valid at `n = 0` too
(`U 0 = 1 = 2⁰`).

## Strategy

A single two-step induction on `n` tracking `natDegree` and `leadingCoeff`
simultaneously.  Base cases `U 0 = 1` (degree 0, leading coeff `1 = 2⁰`) and
`U 1 = 2·X` (degree 1, leading coeff `2 = 2¹`).  For the step, write
`U (n+2) = 2·X·U (n+1) − U n`.  Over the domain `ℤ`:

* `2·X·U (n+1)` has degree `1 + (n+1) = n+2` and leading coefficient
  `2 · 2ⁿ⁺¹ = 2ⁿ⁺²` (degree and leading coefficient are additive/multiplicative
  on products of nonzero polynomials);
* `U n` has degree `n < n+2`, so subtracting it changes neither the degree
  nor the leading coefficient of the `n+2` term.

Hence `natDegree (U (n+2)) = n+2` and `leadingCoeff (U (n+2)) = 2ⁿ⁺²`, completing
the induction.

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Polynomial Polynomial.Chebyshev

namespace DeMoivreOQ02OQ03OQ02OQ01

/-- `2 * X` over `ℤ` has `natDegree` one. -/
theorem natDegree_two_mul_X : (2 * X : ℤ[X]).natDegree = 1 := by
  have : (2 * X : ℤ[X]) = C 2 * X := by simp
  rw [this, natDegree_C_mul (by norm_num : (2 : ℤ) ≠ 0), natDegree_X]

/-- `2 * X` over `ℤ` has leading coefficient `2`. -/
theorem leadingCoeff_two_mul_X : (2 * X : ℤ[X]).leadingCoeff = 2 := by
  have : (2 * X : ℤ[X]) = C 2 * X := by simp
  rw [this, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]

theorem two_mul_X_ne_zero : (2 * X : ℤ[X]) ≠ 0 := by
  intro h
  have := congrArg natDegree h
  rw [natDegree_two_mul_X, natDegree_zero] at this
  exact one_ne_zero this

/-- **Degree and leading coefficient of `Uₙ`.**  Over `ℤ`, the `n`-th second-kind
Chebyshev polynomial has degree `n` and leading coefficient `2 ^ n`. -/
theorem U_natDegree_leadingCoeff (n : ℕ) :
    (U ℤ (n : ℤ)).natDegree = n ∧ (U ℤ (n : ℤ)).leadingCoeff = 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
      refine ⟨?_, ?_⟩
      · simp [U_zero]
      · simp [U_zero]
  | one =>
      have hU1 : U ℤ ((1 : ℕ) : ℤ) = 2 * X := by simp [U_one]
      refine ⟨?_, ?_⟩
      · rw [hU1, natDegree_two_mul_X]
      · rw [hU1, leadingCoeff_two_mul_X]; norm_num
  | more n ih0 ih1 =>
      obtain ⟨hd0, _hl0⟩ := ih0
      obtain ⟨hd1, hl1⟩ := ih1
      -- The defining recurrence, with the index cast through ℕ.
      have hrec : U ℤ ((n + 2 : ℕ) : ℤ)
          = 2 * X * U ℤ ((n + 1 : ℕ) : ℤ) - U ℤ ((n : ℕ) : ℤ) := by
        have h := U_add_two ℤ (n : ℤ)
        push_cast
        push_cast at h
        linear_combination h
      -- `U (n+1) ≠ 0` since its leading coefficient `2ⁿ⁺¹` is nonzero.
      have hUn1_ne : U ℤ ((n + 1 : ℕ) : ℤ) ≠ 0 := by
        intro h0
        rw [h0, leadingCoeff_zero] at hl1
        have : (2 : ℤ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        exact this hl1.symm
      -- Degree and leading coefficient of `A := 2·X·U (n+1)`.
      have hdA : (2 * X * U ℤ ((n + 1 : ℕ) : ℤ)).natDegree = n + 2 := by
        rw [natDegree_mul two_mul_X_ne_zero hUn1_ne, natDegree_two_mul_X, hd1]
        omega
      have hlA : (2 * X * U ℤ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ (n + 2) := by
        rw [leadingCoeff_mul, leadingCoeff_two_mul_X, hl1]
        ring
      -- `U n` has strictly smaller degree.
      have hdeg_lt : (U ℤ ((n : ℕ) : ℤ)).natDegree
          < (2 * X * U ℤ ((n + 1 : ℕ) : ℤ)).natDegree := by
        rw [hdA, hd0]; omega
      refine ⟨?_, ?_⟩
      · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hdeg_lt, hdA]
      · rw [hrec]
        have hsub : (2 * X * U ℤ ((n + 1 : ℕ) : ℤ) - U ℤ ((n : ℕ) : ℤ)).leadingCoeff
            = (2 * X * U ℤ ((n + 1 : ℕ) : ℤ)).leadingCoeff := by
          rw [sub_eq_add_neg]
          rw [leadingCoeff_add_of_degree_lt']
          rw [degree_neg]
          exact degree_lt_degree hdeg_lt
        rw [hsub, hlA]

/-- **Degree of `Uₙ`.**  `natDegree (U ℤ n) = n`. -/
theorem U_natDegree (n : ℕ) : (U ℤ (n : ℤ)).natDegree = n :=
  (U_natDegree_leadingCoeff n).1

/-- **Leading coefficient of `Uₙ`.**  `leadingCoeff (U ℤ n) = 2 ^ n`. -/
theorem U_leadingCoeff (n : ℕ) : (U ℤ (n : ℤ)).leadingCoeff = 2 ^ n :=
  (U_natDegree_leadingCoeff n).2

/-- `Uₙ` is monic up to the scalar `2ⁿ`: it is never the zero polynomial. -/
theorem U_ne_zero (n : ℕ) : U ℤ (n : ℤ) ≠ 0 := by
  intro h0
  have := U_leadingCoeff n
  rw [h0, leadingCoeff_zero] at this
  exact (pow_ne_zero n (by norm_num : (2 : ℤ) ≠ 0)) this.symm

end DeMoivreOQ02OQ03OQ02OQ01
