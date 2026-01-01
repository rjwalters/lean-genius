/-
# Vieta's Formulas

This file formalizes Vieta's formulas, which relate the coefficients of a polynomial
to sums and products of its roots.

**Status**: DEEP DIVE
- Uses Mathlib's Vieta infrastructure
- Provides pedagogical wrappers for quadratic/cubic cases
- Concrete numerical examples

**Vieta's Formulas** (1615):
For a monic polynomial xⁿ + aₙ₋₁xⁿ⁻¹ + ... + a₁x + a₀ with roots r₁, r₂, ..., rₙ:
- Sum of roots: r₁ + r₂ + ... + rₙ = -aₙ₋₁
- Sum of products of pairs: Σᵢ<ⱼ rᵢrⱼ = aₙ₋₂
- Product of all roots: r₁r₂...rₙ = (-1)ⁿa₀

**Named after**: François Viète (Franciscus Vieta), French mathematician (1540-1603)
-/

import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

namespace VietasFormulas

open Polynomial Multiset Finset

/-!
## Quadratic Case

For x² - bx + c = 0 with roots r and s:
- r + s = b
- r · s = c

Note: The standard form uses x² - bx + c so the sum of roots is positive b.
-/

/-- Vieta's formula for quadratics: if x is a root of x² - bx + c = 0,
    then there exists another root y with x + y = b and x * y = c -/
theorem vieta_quadratic {R : Type*} [CommRing R] {b c x : R}
    (h : x * x - b * x + c = 0) :
    ∃ y : R, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c :=
  vieta_formula_quadratic h

/-!
## Concrete Examples

We verify Vieta's formulas on specific polynomials.
-/

section Examples

/-- x² - 5x + 6 = 0 has roots 2 and 3
    Sum: 2 + 3 = 5, Product: 2 * 3 = 6 -/
example : (2 : ℤ) + 3 = 5 := rfl
example : (2 : ℤ) * 3 = 6 := rfl

/-- Verify 2 is a root of x² - 5x + 6 = 0 -/
example : (2 : ℤ) * 2 - 5 * 2 + 6 = 0 := by norm_num

/-- Verify 3 is a root of x² - 5x + 6 = 0 -/
example : (3 : ℤ) * 3 - 5 * 3 + 6 = 0 := by norm_num

/-- x² - 7x + 12 = 0 has roots 3 and 4 -/
example : (3 : ℤ) + 4 = 7 := rfl
example : (3 : ℤ) * 4 = 12 := rfl

/-- x² + x - 6 = 0 has roots -3 and 2 (rewritten as x² - (-1)x + (-6) = 0) -/
example : (-3 : ℤ) + 2 = -1 := rfl
example : (-3 : ℤ) * 2 = -6 := rfl

/-- Verify -3 is a root of x² + x - 6 = 0 -/
example : (-3 : ℤ) * (-3) + (-3) - 6 = 0 := by norm_num

/-- Verify 2 is a root of x² + x - 6 = 0 -/
example : (2 : ℤ) * 2 + 2 - 6 = 0 := by norm_num

/-- x³ - 6x² + 11x - 6 = 0 has roots 1, 2, 3
    Sum of roots = 1 + 2 + 3 = 6
    Sum of products of pairs = 1·2 + 1·3 + 2·3 = 11
    Product of all roots = 1·2·3 = 6 -/
example : (1 : ℤ) + 2 + 3 = 6 := rfl
example : (1 : ℤ) * 2 + 1 * 3 + 2 * 3 = 11 := rfl
example : (1 : ℤ) * 2 * 3 = 6 := rfl

/-- Verify 1, 2, 3 are roots of x³ - 6x² + 11x - 6 = 0 -/
example : (1 : ℤ)^3 - 6 * 1^2 + 11 * 1 - 6 = 0 := by norm_num
example : (2 : ℤ)^3 - 6 * 2^2 + 11 * 2 - 6 = 0 := by norm_num
example : (3 : ℤ)^3 - 6 * 3^2 + 11 * 3 - 6 = 0 := by norm_num

end Examples

/-!
## The Core Vieta Formula for Polynomials

For a monic polynomial p that splits (has all roots in the field),
the coefficients are determined by elementary symmetric functions of roots.
-/

/-- The core Vieta relation from Mathlib: coefficients equal elementary symmetric
    functions of roots (with appropriate signs), multiplied by the leading coefficient -/
theorem vieta_polynomial_coeff {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hroots : Multiset.card p.roots = p.natDegree)
    (k : ℕ) (hk : k ≤ p.natDegree) :
    p.coeff k = p.leadingCoeff * (-1) ^ (p.natDegree - k) * Multiset.esymm p.roots (p.natDegree - k) :=
  Polynomial.coeff_eq_esymm_roots_of_card hroots hk

/-- For monic polynomials, the formula simplifies (leadingCoeff = 1) -/
theorem vieta_monic_coeff {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p.Monic) (hroots : Multiset.card p.roots = p.natDegree)
    (k : ℕ) (hk : k ≤ p.natDegree) :
    p.coeff k = (-1) ^ (p.natDegree - k) * Multiset.esymm p.roots (p.natDegree - k) := by
  rw [vieta_polynomial_coeff p hroots k hk, hp.leadingCoeff, one_mul]

/-!
## Applications

Vieta's formulas are useful for:
1. Finding polynomial coefficients given roots
2. Checking if proposed roots are correct
3. Relating roots without computing them explicitly
4. The foundation of Galois theory
-/

/-- Given two roots, reconstruct the quadratic -/
theorem quadratic_from_roots_sum_prod {R : Type*} [CommRing R] (s p : R) (x : R) :
    x * x - s * x + p = (x - s) * x + p := by ring

/-- Relationship between roots and coefficients for monic quadratic -/
theorem monic_quadratic_vieta {R : Type*} [CommRing R] (r₁ r₂ : R) :
    ∀ x : R, (x - r₁) * (x - r₂) = x * x - (r₁ + r₂) * x + r₁ * r₂ := by
  intro x
  ring

/-- Relationship between roots and coefficients for monic cubic -/
theorem monic_cubic_vieta {R : Type*} [CommRing R] (r₁ r₂ r₃ : R) :
    ∀ x : R, (x - r₁) * (x - r₂) * (x - r₃) =
      x^3 - (r₁ + r₂ + r₃) * x^2 + (r₁*r₂ + r₁*r₃ + r₂*r₃) * x - r₁*r₂*r₃ := by
  intro x
  ring

/-!
## Sign Pattern

Note the alternating signs in Vieta's formulas for monic polynomials:
- Coefficient of xⁿ⁻¹ = -(sum of roots)
- Coefficient of xⁿ⁻² = +(sum of products of pairs)
- Coefficient of xⁿ⁻³ = -(sum of products of triples)
- Constant term = (-1)ⁿ · (product of all roots)
-/

/-- (-1)^k * (-1)^k = 1 for any k -/
theorem neg_one_pow_sq (k : ℕ) : (-1 : ℤ) ^ k * (-1) ^ k = 1 := by
  rw [← pow_add, ← two_mul]
  simp [pow_mul]

/-!
## Historical Note

François Viète (1540-1603) introduced the systematic use of letters for
unknowns and parameters, which made general statements about equations possible.
His formulas appeared in "De aequationum recognitione et emendatione tractatus duo"
(1615), published posthumously.

The formulas show that coefficients are elementary symmetric functions of roots,
which is fundamental to:
- Galois theory
- The proof of unsolvability of quintics (Abel-Ruffini)
- Newton's identities
- Symmetric function theory
-/

#check vieta_quadratic
#check vieta_polynomial_coeff
#check monic_quadratic_vieta
#check monic_cubic_vieta

end VietasFormulas
