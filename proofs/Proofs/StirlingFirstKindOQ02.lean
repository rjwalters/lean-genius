/-
Stirling Numbers of the First Kind, II: the rising-factorial generating identity
  c(n,k) = [Xᵏ] X(X+1)⋯(X+n−1) = (ascPochhammer ℤ n).coeff k,
and the row sum ∑ₖ c(n,k) = n! recovered from it by evaluation at X = 1.

Source: Follow-up open question to stirling-first-kind-oq-01 (the row sum)
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingFirst n k` is the unsigned Stirling number of the first kind: the
number of permutations of an `n`-element set with exactly `k` disjoint cycles.
Mathlib (`Mathlib/Combinatorics/Enumerative/Stirling.lean`, 2025) provides the
Pascal recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)` and the boundary columns, and
the companion gallery entry `stirling-first-kind-oq-01` proves the row sum
`∑ₖ c(n,k) = n!` by a direct combinatorial induction.

What is recorded NOWHERE — neither in Mathlib nor in oq-01 — is the *defining
generating-function identity* of these numbers:

      X(X+1)(X+2)⋯(X+n−1)  =  ∑ₖ c(n,k)·Xᵏ.

The product on the left is exactly Mathlib's rising factorial `ascPochhammer ℤ n`,
so the identity says precisely that

      (ascPochhammer ℤ n).coeff k  =  c(n,k).

This is the most structural fact about the first-kind triangle: the entire row is
the coefficient list of one polynomial. We prove it (theorem 1), and then *recover
the row sum as a corollary* (theorem 2) by a route entirely different from oq-01:
setting `X = 1` sends `Xᵏ ↦ 1`, collapsing the coefficient list to its sum, while
the polynomial value there is `(ascPochhammer ℤ n).eval 1 = n!`
(`ascPochhammer_eval_one`). So the same `n!` is reached through the generating
function rather than through a bespoke induction.

We prove:
1. `stirlingFirst_eq_ascPochhammer_coeff` — c(n,k) is the Xᵏ-coefficient of the
   rising factorial `ascPochhammer ℤ n`  (the generating identity)
2. `stirlingFirst_row_sum`               — ∑ₖ c(n,k) = n!, derived from (1) by
   evaluating the generating polynomial at X = 1
3. `stirlingFirst_row_four`              — numeric sanity check: row 4 sums to 24
-/

import Mathlib

open Nat Polynomial

namespace StirlingFirstKindOQ02

/-- **Generating identity for the first kind.** The unsigned Stirling number
`c(n,k)` is the coefficient of `Xᵏ` in the rising factorial
`X(X+1)⋯(X+n−1) = ascPochhammer ℤ n`.

Proof by induction on `n`. The step uses
`ascPochhammer ℤ (n+1) = ascPochhammer ℤ n · (X + n)` (`ascPochhammer_succ_right`):
extracting the `Xᵏ`-coefficient of the product — `coeff_mul_X` for the `X` factor
(an index shift) and `coeff_mul_C` for the constant `n` — reproduces exactly the
Pascal recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)`, while the `k = 0` case yields
`c(n+1,0) = 0`. -/
theorem stirlingFirst_eq_ascPochhammer_coeff (n k : ℕ) :
    (ascPochhammer ℤ n).coeff k = (Nat.stirlingFirst n k : ℤ) := by
  induction n generalizing k with
  | zero =>
    rw [ascPochhammer_zero, Polynomial.coeff_one]
    cases k with
    | zero => simp
    | succ k => simp [Nat.stirlingFirst_zero_succ]
  | succ n ih =>
    rw [ascPochhammer_succ_right, ← Polynomial.C_eq_natCast, mul_add,
      Polynomial.coeff_add, Polynomial.coeff_mul_C]
    cases k with
    | zero =>
      rw [Polynomial.coeff_mul_X_zero, zero_add, ih, Nat.stirlingFirst_succ_zero]
      have hz : Nat.stirlingFirst n 0 * n = 0 := by
        cases n with
        | zero => simp
        | succ m => simp [Nat.stirlingFirst_succ_zero]
      push_cast
      exact_mod_cast hz
    | succ j =>
      rw [Polynomial.coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

/-- **Row sum via the generating function.** `∑_{k=0}^{n} c(n,k) = n!`, obtained
from the generating identity by evaluating at `X = 1`.

`(ascPochhammer ℤ n).eval 1 = n!` (`ascPochhammer_eval_one`); expanding the
evaluation as a sum of coefficients over `range (natDegree + 1) = range (n+1)`
(`eval_eq_sum_range`, `ascPochhammer_natDegree`) and replacing each coefficient by
`c(n,k)` via theorem 1 gives `∑ₖ (c(n,k) : ℤ) = n!`, which descends to ℕ. This is a
generating-function proof of the row sum, distinct from the direct induction of
`stirling-first-kind-oq-01`. -/
theorem stirlingFirst_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.stirlingFirst n k = n ! := by
  have h1 : (ascPochhammer ℤ n).eval 1 = (n ! : ℤ) := ascPochhammer_eval_one ℤ n
  rw [Polynomial.eval_eq_sum_range, ascPochhammer_natDegree ℤ n] at h1
  simp only [one_pow, mul_one] at h1
  rw [Finset.sum_congr rfl (fun k _ => stirlingFirst_eq_ascPochhammer_coeff n k),
    ← Nat.cast_sum] at h1
  exact_mod_cast h1

/-- **Numeric sanity check.** Row `4` is `c(4,0..4) = 0, 6, 11, 6, 1`, summing to
`24 = 4!`, matching `stirlingFirst_row_sum`. -/
theorem stirlingFirst_row_four :
    ∑ k ∈ Finset.range 5, Nat.stirlingFirst 4 k = 24 := by
  simp [Finset.sum_range_succ, Nat.stirlingFirst]

end StirlingFirstKindOQ02
