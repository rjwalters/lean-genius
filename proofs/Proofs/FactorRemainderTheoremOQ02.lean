import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-
# Rational Root Theorem (Extension of Factor/Remainder Theorem)

## What This Proves
The **Rational Root Theorem**: if a polynomial p(x) ∈ ℤ[X] has a rational root r/s
(in lowest terms), then:
  - s divides the leading coefficient of p
  - r divides the constant term of p

As a corollary, the **Integral Root Theorem**: if p is monic, then all rational
roots are integers, and they divide the constant term.

## Historical Context
The Rational Root Theorem provides a finite list of candidates for rational roots
of integer polynomials. Combined with the Factor Theorem, this gives an algorithm
for factoring polynomials over ℚ: test all candidates p/q where p | a₀ and q | aₙ.

The theorem was known in various forms to medieval mathematicians. The modern
statement is often attributed to Descartes (1637) and Euler.

## Approach
All results follow from Mathlib's `num_dvd_of_is_root` and `den_dvd_of_is_root`
in `Mathlib.RingTheory.Polynomial.RationalRoot`, which prove the theorem for
any UFD with its fraction field. We specialize to ℤ and ℚ.
-/

namespace RationalRootTheorem

open Polynomial IsFractionRing

/-! ## The Rational Root Theorem for ℤ/ℚ -/

/-- **Rational Root Theorem, Part 1 (Numerator Divides Constant Term):**
If r ∈ ℚ is a root of p ∈ ℤ[X], then the numerator of r divides p's constant term.

Here `num ℤ r` is the numerator of r in lowest terms (from `IsFractionRing`). -/
theorem rational_root_numerator_dvd {p : ℤ[X]} {r : ℚ} (hr : aeval r p = 0) :
    num ℤ r ∣ p.coeff 0 :=
  num_dvd_of_is_root hr

/-- **Rational Root Theorem, Part 2 (Denominator Divides Leading Coefficient):**
If r ∈ ℚ is a root of p ∈ ℤ[X], then the denominator of r divides p's leading coefficient. -/
theorem rational_root_denominator_dvd {p : ℤ[X]} {r : ℚ} (hr : aeval r p = 0) :
    (den ℤ r : ℤ) ∣ p.leadingCoeff :=
  den_dvd_of_is_root hr

/-- **Integral Root Theorem (Monic Case):**
If p ∈ ℤ[X] is monic and r ∈ ℚ is a root of p, then r ∈ ℤ.

This is a direct consequence of the Rational Root Theorem: since the leading
coefficient is 1, the denominator must divide 1, so r is an integer. -/
theorem monic_rational_root_is_integer {p : ℤ[X]} (hp : p.Monic) {r : ℚ}
    (hr : aeval r p = 0) : IsInteger ℤ r :=
  isInteger_of_is_root_of_monic hp hr

/-- For monic polynomials, rational roots are integers that divide the constant term. -/
theorem monic_root_dvd_constant {p : ℤ[X]} (hp : p.Monic) {r : ℚ}
    (hr : aeval r p = 0) : ∃ n : ℤ, r = algebraMap ℤ ℚ n ∧ n ∣ p.coeff 0 :=
  exists_integer_of_is_root_of_monic hp hr

/-! ## Combining with the Factor Theorem -/

/-- If r = p/q (in lowest terms) is a root of f ∈ ℤ[X], then we can factor:
f(x) = (x - r) · g(x) over ℚ[X]. -/
theorem factor_of_rational_root {f : ℤ[X]} {r : ℚ} (hr : aeval r f = 0) :
    (X - C r) ∣ (f.map (algebraMap ℤ ℚ)) := by
  rw [dvd_iff_isRoot]
  simp [IsRoot, eval_map, ← aeval_def, hr]

/-! ## Contrapositive: Proving Irrationality

The Rational Root Theorem is often used in its contrapositive form to prove
that certain numbers are irrational: if no rational r/s satisfies the
divisibility conditions, then the polynomial has no rational roots. -/

/-- A monic polynomial with no integer divisors of its constant term as roots
has no rational roots at all. -/
theorem no_rational_root_of_no_integer_root {p : ℤ[X]} (hp : p.Monic)
    (h : ∀ n : ℤ, n ∣ p.coeff 0 → aeval (algebraMap ℤ ℚ n) p ≠ 0) :
    ∀ r : ℚ, aeval r p ≠ 0 := by
  intro r hr
  obtain ⟨n, hn_eq, hn_dvd⟩ := monic_root_dvd_constant hp hr
  exact h n hn_dvd (hn_eq ▸ hr)

/-! ## Connection to Polynomial Factorization

The Rational Root Theorem gives an algorithm for rational root finding:
1. List all divisors of the constant term (candidates for numerator)
2. List all divisors of the leading coefficient (candidates for denominator)
3. Test each candidate r = p/q using the Factor Theorem (evaluate p(r))
4. For each root found, factor out (x - r) using the Factor Theorem

For monic polynomials, this simplifies: just test integer divisors of the
constant term. Combined with polynomial long division, this gives a complete
factorization algorithm over ℚ. -/

end RationalRootTheorem
