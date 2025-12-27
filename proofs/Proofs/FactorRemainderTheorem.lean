import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Factor and Remainder Theorems (Wiedijk #89)

## What This Proves
Two fundamental theorems connecting polynomial division, roots, and evaluation:

**Factor Theorem**: A polynomial p(x) has (x - a) as a factor if and only if p(a) = 0.

  (X - a) | p(X) ⟺ p(a) = 0

**Remainder Theorem**: When a polynomial p(x) is divided by (x - a), the remainder is p(a).

  p(X) = (X - a) · q(X) + p(a)

Equivalently: p(X) mod (X - a) = p(a) as a constant polynomial.

## Approach
- **Foundation (from Mathlib):** We use `Polynomial.dvd_iff_isRoot` for the Factor Theorem
  and `Polynomial.modByMonic_X_sub_C_eq_C_eval` for the Remainder Theorem.
- **Key Insight:** The monic polynomial (X - a) divides p exactly when evaluating p at a
  yields zero. The remainder theorem follows from the division algorithm for polynomials.
- **Proof Techniques:** Polynomial division, root characterization, monic polynomials.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Polynomial.dvd_iff_isRoot` : (X - C a) ∣ p ↔ p.IsRoot a
- `Polynomial.modByMonic_X_sub_C_eq_C_eval` : p %ₘ (X - C a) = C(p.eval a)
- `Polynomial.X_sub_C_dvd_sub_C_eval` : (X - C a) ∣ (p - C(p.eval a))
- `Polynomial.monic_X_sub_C` : (X - C a) is monic

## Historical Note
The Factor Theorem appears in various forms throughout mathematical history. The modern
algebraic formulation emerged in the 17th-18th centuries alongside the development of
polynomial algebra. René Descartes (1637) and others used these ideas in the study of
polynomial equations. The theorem is fundamental to polynomial factorization and the
fundamental theorem of algebra.

The Remainder Theorem is closely related—it says that polynomial long division by a
linear term always yields a constant remainder equal to the polynomial's value at
the root of that linear term.

This is #89 on Wiedijk's list of 100 theorems.
-/

namespace FactorRemainderTheorem

open Polynomial

/-! ## The Factor Theorem

The Factor Theorem establishes a fundamental connection between polynomial roots
and polynomial divisibility. -/

/-- **Factor Theorem (Wiedijk #89)**

A polynomial p has (X - a) as a factor if and only if a is a root of p.

That is: (X - C a) divides p exactly when p.eval a = 0.

This theorem is fundamental to polynomial factorization. When we find that p(a) = 0,
we know immediately that (x - a) is a factor, and we can divide p by (x - a) to
reduce the degree. -/
theorem factor_theorem {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ p ↔ p.eval a = 0 :=
  dvd_iff_isRoot

/-- Alternative statement using IsRoot predicate -/
theorem factor_theorem' {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ p ↔ p.IsRoot a :=
  dvd_iff_isRoot

/-- If a is a root of p, then (X - C a) divides p -/
theorem factor_of_root {R : Type*} [CommRing R] (p : R[X]) (a : R) (h : p.eval a = 0) :
    (X - C a) ∣ p :=
  (factor_theorem p a).mpr h

/-- If (X - C a) divides p, then a is a root of p -/
theorem root_of_factor {R : Type*} [CommRing R] (p : R[X]) (a : R) (h : (X - C a) ∣ p) :
    p.eval a = 0 :=
  (factor_theorem p a).mp h

/-! ## The Remainder Theorem

The Remainder Theorem tells us precisely what the remainder is when dividing
a polynomial by a linear factor. -/

/-- **Remainder Theorem (Wiedijk #89)**

When a polynomial p is divided by (X - C a), the remainder is the constant
polynomial C(p.eval a).

This means: p(X) = (X - a) · q(X) + p(a)

where q(X) is the quotient polynomial.

The theorem provides a simple way to find remainders without performing
full polynomial division—just evaluate the polynomial at a! -/
theorem remainder_theorem {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    p %ₘ (X - C a) = C (p.eval a) :=
  modByMonic_X_sub_C_eq_C_eval p a

/-- The remainder theorem in terms of subtraction:
(X - C a) divides p - C(p.eval a) -/
theorem remainder_divides {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ (p - C (p.eval a)) := by
  rw [factor_theorem]
  simp [eval_sub, eval_C]

/-- Division algorithm form: p = (X - C a) * (p /ₘ (X - C a)) + C(p.eval a) -/
theorem division_algorithm {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    p = (X - C a) * (p /ₘ (X - C a)) + C (p.eval a) := by
  have h : (X - C a).Monic := monic_X_sub_C a
  conv_lhs => rw [← modByMonic_add_div p h]
  rw [remainder_theorem, add_comm]

/-! ## Connection Between the Two Theorems

The Factor and Remainder Theorems are intimately connected. The Factor Theorem
is really a special case of the Remainder Theorem: when the remainder is zero. -/

/-- The Factor Theorem as a corollary of the Remainder Theorem:
(X - C a) divides p iff the remainder is zero iff p.eval a = 0 -/
theorem factor_iff_zero_remainder {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (X - C a) ∣ p ↔ p %ₘ (X - C a) = 0 := by
  rw [remainder_theorem]
  constructor
  · intro h
    rw [factor_theorem] at h
    simp [h]
  · intro h
    rw [factor_theorem]
    rw [C_eq_zero] at h
    exact h

/-- When the remainder is zero, the polynomial factors exactly -/
theorem exact_division {R : Type*} [CommRing R] (p : R[X]) (a : R) (h : p.eval a = 0) :
    p = (X - C a) * (p /ₘ (X - C a)) := by
  have := division_algorithm p a
  simp only [h, map_zero, add_zero] at this
  exact this

/-! ## Practical Applications

These theorems have immediate practical uses in finding and verifying roots. -/

/-- Checking a root is easy: if p.eval a = 0, we have found a factor -/
theorem verify_root {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    p.eval a = 0 → ∃ q : R[X], p = (X - C a) * q := fun h =>
  ⟨p /ₘ (X - C a), exact_division p a h⟩

/-- A nonzero evaluation means (X - C a) is not a factor -/
theorem not_factor_of_nonzero_eval {R : Type*} [CommRing R] (p : R[X]) (a : R) (h : p.eval a ≠ 0) :
    ¬(X - C a) ∣ p := by
  rw [factor_theorem]
  exact h

/-! ## Properties of Monic Linear Polynomials

The polynomial (X - C a) has special properties that make these theorems work. -/

/-- (X - C a) is monic (leading coefficient is 1) -/
theorem linear_factor_monic {R : Type*} [CommRing R] (a : R) : (X - C a).Monic :=
  monic_X_sub_C a

/-- (X - C a) has degree 1 -/
theorem linear_factor_degree {R : Type*} [CommRing R] [Nontrivial R] (a : R) :
    (X - C a).degree = 1 :=
  degree_X_sub_C a

/-- The remainder when dividing by (X - C a) has degree < 1, i.e., is constant -/
theorem remainder_is_constant {R : Type*} [CommRing R] [Nontrivial R] (p : R[X]) (a : R) :
    (p %ₘ (X - C a)).degree < 1 := by
  have h := degree_modByMonic_lt p (monic_X_sub_C a)
  rwa [degree_X_sub_C] at h

/-! ## Examples over ℤ

Concrete examples demonstrating the theorems with integer polynomials. -/

/-- x² - 1 has (x - 1) as a factor since 1² - 1 = 0 -/
example : (X ^ 2 - 1 : ℤ[X]).eval 1 = 0 := by simp

/-- x² - 1 has (x + 1) = (x - (-1)) as a factor since (-1)² - 1 = 0 -/
example : (X ^ 2 - 1 : ℤ[X]).eval (-1) = 0 := by simp

/-- By Factor Theorem, (X - 1) divides X² - 1 -/
example : (X - C (1 : ℤ)) ∣ (X ^ 2 - 1) := by
  rw [factor_theorem]
  simp

/-- By Factor Theorem, (X + 1) divides X² - 1 -/
example : (X - C (-1 : ℤ)) ∣ (X ^ 2 - 1) := by
  rw [factor_theorem]
  simp

/-- x³ - 8 has (x - 2) as a factor since 2³ = 8 -/
example : (X ^ 3 - 8 : ℤ[X]).eval 2 = 0 := by simp

example : (X - C (2 : ℤ)) ∣ (X ^ 3 - 8) := by
  rw [factor_theorem]
  simp

/-- x² + 1 does NOT have (x - 1) as a factor over ℤ since 1² + 1 = 2 ≠ 0 -/
example : ¬((X - C (1 : ℤ)) ∣ (X ^ 2 + 1)) := by
  rw [factor_theorem]
  simp

/-! ## Examples: Remainder Calculation

Demonstrating the Remainder Theorem with concrete remainders. -/

/-- When dividing x² - 3x + 2 by (x - 3), remainder is 3² - 3·3 + 2 = 2 -/
example : (X ^ 2 - C 3 * X + C 2 : ℤ[X]).eval 3 = 2 := by simp

/-- When dividing x³ by (x - 1), remainder is 1³ = 1 -/
example : (X ^ 3 : ℤ[X]).eval 1 = 1 := by simp

/-- When dividing x⁴ - 2x² + 1 by (x - 2), remainder is 16 - 8 + 1 = 9 -/
example : (X ^ 4 - C 2 * X ^ 2 + C 1 : ℤ[X]).eval 2 = 9 := by simp

/-! ## Examples over ℚ

The theorems work over any commutative ring, including rationals. -/

/-- x² - 4 = (x-2)(x+2) has roots at ±2 -/
example : (X ^ 2 - C (4 : ℚ) : ℚ[X]).eval 2 = 0 := by
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  norm_num

example : (X ^ 2 - C (4 : ℚ) : ℚ[X]).eval (-2) = 0 := by
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  norm_num

/-- 2x² - 5x + 2 has root at x = 2 (since 8 - 10 + 2 = 0) -/
example : (C (2 : ℚ) * X ^ 2 - C 5 * X + C 2 : ℚ[X]).eval 2 = 0 := by
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  norm_num

/-- 2x² - 5x + 2 has root at x = 1/2 (since 1/2 - 5/2 + 2 = 0) -/
example : (C (2 : ℚ) * X ^ 2 - C 5 * X + C 2 : ℚ[X]).eval (1/2) = 0 := by
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  norm_num

#check factor_theorem
#check remainder_theorem
#check division_algorithm

end FactorRemainderTheorem
