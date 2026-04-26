/-
  Aristotle targets for AngleTrisectionCos20GalOQ01OQ02
  Routine supporting lemmas for automated proof search.
  See AngleTrisectionCos20GalOQ01OQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main Galois group formula (which requires cyclotomic field theory)
  - Known mathematical result: irreducibility via rational root theorem
  - No definition sorries
  - No axioms

  Included targets (3):
  - pCos5_natDegree: natDegree of 4X²-2X-1 is 2
  - pCos5_no_rat_root_one: f(1) ≠ 0 (evaluation check)
  - pCos5_irreducible: 4X²-2X-1 is irreducible over ℚ

  NOT included (too complex for Aristotle):
  - gal_order_eq_totient_div2_general: requires cyclotomic field theory
  - cos_36_gal_card: depends on irreducibility + splitting field theory (some parts need sorry)
-/
import Mathlib

open Polynomial

namespace AngleTrisectionCos20GalOQ01OQ02Aristotle

/-- The degree of 4X²-2X-1 over ℚ is 2. -/
theorem pCos5_natDegree : (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]).natDegree = 2 := by
  sorry

/-- 4X²-2X-1 evaluated at 1 is 1 ≠ 0. -/
theorem pCos5_eval_one : Polynomial.eval 1 (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 evaluated at -1 is 5 ≠ 0. -/
theorem pCos5_eval_neg_one : Polynomial.eval (-1) (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 evaluated at 1/2 is -1 ≠ 0. -/
theorem pCos5_eval_half : Polynomial.eval (1/2) (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 evaluated at -1/2 is 1 ≠ 0. -/
theorem pCos5_eval_neg_half : Polynomial.eval (-1/2) (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 evaluated at 1/4 is -5/4 ≠ 0. -/
theorem pCos5_eval_quarter : Polynomial.eval (1/4) (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 evaluated at -1/4 is -1/4 ≠ 0. -/
theorem pCos5_eval_neg_quarter : Polynomial.eval (-1/4) (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) ≠ 0 := by
  norm_num

/-- 4X²-2X-1 is irreducible over ℚ.
    Proof: By the rational root theorem (applied to the integer polynomial 4X²-2X-1,
    with leading coeff 4 and constant term -1), the only possible rational roots are
    ±1, ±1/2, ±1/4. All are non-roots (checked above). For a degree-2 polynomial over
    a field, no roots implies irreducible. -/
theorem pCos5_irreducible : Irreducible (4 * X ^ 2 - 2 * X - C 1 : ℚ[X]) := by
  sorry

end AngleTrisectionCos20GalOQ01OQ02Aristotle
