import Proofs.TetrahedralNumberFormulaOQ02Polynomial
import Mathlib

/-
# The Figurate Partial Sum `S_d` as a Rational Polynomial (Faulhaber form)

## Context

`TetrahedralNumberFormulaOQ02` proves the uniform cleared-denominator identity
`(d+1)! · S_d(n) = ∏_{i<d+1} (n+1+i)` for the running total
`S_d(n) = ∑_{k≤n} P_d(k)` of the `d`-dimensional figurate row, and
`TetrahedralNumberFormulaOQ02Polynomial` packages the *cleared* right-hand side
as a genuine monic `Polynomial ℤ` `figuratePoly d` of degree `d+1` with
`figuratePoly d (n) = (d+1)! · S_d(n)`.

This file supplies the **remaining `nextStep`** of `OQ02`: expressing `S_d`
*itself* — not just `(d+1)!·S_d` — as a first-class `Polynomial ℚ`, the
Faulhaber/Bernoulli viewpoint in which a power-sum / figurate-sum is a rational
polynomial in the upper limit.

## Result

`figurateSumPoly d : Polynomial ℚ := C ((d+1)!)⁻¹ · (figuratePoly d).map (ℤ→ℚ)`
is the degree-`d+1` rational polynomial whose value at every natural number `n`
is exactly the figurate partial sum `S_d(n)`:

* `figurateSumPoly_eval` : `(figurateSumPoly d).eval n = S_d(n)` — the bridge to
  the arithmetic partial sum, over `ℚ`. This is the sense in which `S_d` *is* a
  polynomial: a single rational polynomial reproduces the entire sequence
  `n ↦ ∑_{k≤n} P_d(k)`.
* `figurateSumPoly_natDegree` : `deg (figurateSumPoly d) = d + 1` — one more than
  the dimension, matching the closed form `S_d(n) = C(n+d+1, d+1)`.
* `figurateSumPoly_leadingCoeff` : the leading coefficient is `1/(d+1)!` — the
  reciprocal factorial that Faulhaber's formula predicts for the top term
  `n^{d+1}/(d+1)!`.

Together these exhibit `S_d` as a monic-up-to-`1/(d+1)!` rational polynomial of
degree `d+1`, the exact shape of a Faulhaber summation polynomial.

0 sorries, 0 axioms.
-/

namespace TetrahedralNumberFormulaOQ02

open Finset Polynomial TetrahedralNumberFormulaOQ01

/-- The **rational figurate-sum polynomial** `S_d` as a `Polynomial ℚ`:
`figurateSumPoly d = (1/(d+1)!) · Q_d` where `Q_d = figuratePoly d` is the
integer cleared-form polynomial `∏_{i<d+1}(X+(i+1))`. Dividing the cleared form
by its sole `(d+1)!` denominator turns the *cleared* figurate sum back into the
figurate sum itself, now realized as a rational polynomial in the upper limit. -/
noncomputable def figurateSumPoly (d : ℕ) : Polynomial ℚ :=
  Polynomial.C ((Nat.factorial (d + 1) : ℚ)⁻¹) *
    (figuratePoly d).map (Int.castRingHom ℚ)

/-- **Evaluation bridge.** The rational figurate-sum polynomial reproduces the
arithmetic partial sum at every natural number: `(figurateSumPoly d).eval n = S_d(n)`.

Combines the integer evaluation `figuratePoly d (n) = (d+1)!·S_d(n)` with the
`(d+1)!` scalar, cancelling exactly because `(d+1)! ≠ 0` in `ℚ`. -/
theorem figurateSumPoly_eval (d n : ℕ) :
    (figurateSumPoly d).eval (n : ℚ) = (figurateSum d n : ℚ) := by
  have hfac : (Nat.factorial (d + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (d + 1)).ne'
  rw [figurateSumPoly, eval_mul, eval_C, eval_natCast_map, figuratePoly_eval,
    eq_intCast, Int.cast_natCast, Nat.cast_mul, inv_mul_cancel_left₀ hfac]

/-- **Degree.** `figurateSumPoly d` has degree exactly `d + 1`. Scaling the
monic degree-`d+1` polynomial `Q_d` by the nonzero constant `1/(d+1)!` preserves
the degree; mapping `ℤ → ℚ` is injective and so degree-preserving. -/
theorem figurateSumPoly_natDegree (d : ℕ) :
    (figurateSumPoly d).natDegree = d + 1 := by
  have hc : (Nat.factorial (d + 1) : ℚ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Nat.factorial_pos (d + 1)).ne')
  rw [figurateSumPoly, natDegree_C_mul hc,
    natDegree_map_eq_of_injective (Int.castRingHom ℚ).injective_int,
    figuratePoly_natDegree]

/-- **Leading coefficient.** The top coefficient of `figurateSumPoly d` is
`1/(d+1)!` — the reciprocal-factorial leading term of Faulhaber's formula,
`S_d(n) = n^{d+1}/(d+1)! + (lower order)`. It is `1/(d+1)!` times the leading
coefficient `1` of the monic cleared-form polynomial `Q_d`. -/
theorem figurateSumPoly_leadingCoeff (d : ℕ) :
    (figurateSumPoly d).leadingCoeff = (Nat.factorial (d + 1) : ℚ)⁻¹ := by
  rw [figurateSumPoly, leadingCoeff_mul, leadingCoeff_C,
    leadingCoeff_map_of_injective (Int.castRingHom ℚ).injective_int,
    (figuratePoly_monic d).leadingCoeff, map_one, mul_one]

end TetrahedralNumberFormulaOQ02
