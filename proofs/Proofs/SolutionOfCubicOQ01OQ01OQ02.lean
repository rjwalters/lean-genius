import Proofs.SolutionOfCubicOQ01OQ01
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# The Cubic Discriminant as the Resultant `Res(f, f')` (Solution of Cubic, OQ-01-OQ-01-OQ-02)

## What This Proves

The parent file `SolutionOfCubicOQ01OQ01` defines the **general cubic discriminant**

  `Δ(a,b,c,d) = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`

as a hand-written polynomial in the four coefficients, and proves it transforms correctly
under the Tschirnhaus shift. That entry closed with the open question:

  *"Derive the discriminant as the resultant `Res(f, f')` of the cubic and its derivative,
  matching the coefficient formula and generalizing the construction to higher degree."*

This file answers exactly that, using Mathlib's general resultant theory
(`Polynomial.resultant`, `Polynomial.discr`). For the genuine cubic
`f = a·X³ + b·X² + c·X + d` (`a ≠ 0`) we prove the two structural identities

  `f.discr = Δ(a,b,c,d)`                          (`cubic_discr_eq_generalDiscriminant`)
  `Res(f, f') = −a · Δ(a,b,c,d)`                  (`cubic_resultant_eq_neg_smul_discriminant`)

The first identifies the parent's ad-hoc polynomial with Mathlib's intrinsic, basis-free
discriminant (the determinant of the Sylvester matrix of `f` and `f'`, normalized by a sign).
The second is the classical relation `Res(f, f') = (−1)^{n(n−1)/2}·aₙ·Δ`, specialized to a
cubic where `(−1)^{3·2/2} = −1` and `aₙ = a`. As a consequence the **resultant of a cubic
with its derivative vanishes exactly when the cubic has a repeated root**
(`cubic_resultant_eq_zero_iff`), the eliminant characterization of the discriminant.

## Original Contributions
- `cubicPoly` — the cubic `a·X³ + b·X² + c·X + d` as an honest `Polynomial ℂ`, with its
  degree, leading coefficient, coefficient, and derivative computed
  (`cubicPoly_natDegree`, `cubicPoly_degree`, `cubicPoly_leadingCoeff`, `cubicPoly_coeff_*`,
  `cubicPoly_derivative`).
- `cubic_discr_eq_generalDiscriminant` — Mathlib's intrinsic `f.discr` equals the parent's
  `generalDiscriminant a b c d`; the bridge the open question asked for.
- `cubic_resultant_eq_neg_smul_discriminant` — the headline: `Res(f, f') = −a·Δ`, the
  resultant/discriminant relation for the cubic.
- `cubic_resultant_eq_zero_iff` / `cubic_resultant_eq_zero_iff_repeated_root` — the eliminant
  criterion: the resultant vanishes iff `Δ = 0`, i.e. iff two roots coincide (via the parent's
  `repeated_root_iff`).

## Proof Techniques
The coefficient and degree facts are `compute_degree` / `simp`. The discriminant bridge feeds
the computed coefficients into Mathlib's `Polynomial.discr_of_degree_eq_three` and closes with
`ring`. The resultant identity instantiates `Polynomial.resultant_deriv` at `natDegree = 3`,
where the sign `(−1)^{3·2/2}` collapses to `−1`. Everything is over `ℂ` (matching the parent)
and is `0`-axiom.
-/

namespace SolutionOfCubicOQ01OQ01OQ02

open Polynomial SolutionOfCubicOQ01OQ01

/-! ## Part 1: The cubic as a polynomial and its invariants

We realize `a·X³ + b·X² + c·X + d` as an element of `ℂ[X]` and record its coefficients,
degree, leading coefficient and derivative. -/

/-- The general cubic `a·X³ + b·X² + c·X + d` as a `Polynomial ℂ`. -/
noncomputable def cubicPoly (a b c d : ℂ) : ℂ[X] :=
  C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

@[simp] theorem cubicPoly_coeff_zero (a b c d : ℂ) : (cubicPoly a b c d).coeff 0 = d := by
  simp [cubicPoly, coeff_X_pow]

@[simp] theorem cubicPoly_coeff_one (a b c d : ℂ) : (cubicPoly a b c d).coeff 1 = c := by
  simp [cubicPoly, coeff_X_pow]

@[simp] theorem cubicPoly_coeff_two (a b c d : ℂ) : (cubicPoly a b c d).coeff 2 = b := by
  simp [cubicPoly, coeff_X_pow]

@[simp] theorem cubicPoly_coeff_three (a b c d : ℂ) : (cubicPoly a b c d).coeff 3 = a := by
  simp [cubicPoly, coeff_X_pow]

/-- For `a ≠ 0` the cubic has `natDegree = 3`. -/
theorem cubicPoly_natDegree (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).natDegree = 3 := by
  unfold cubicPoly
  compute_degree!

/-- For `a ≠ 0` the cubic has `degree = 3`. -/
theorem cubicPoly_degree (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).degree = 3 := by
  unfold cubicPoly
  compute_degree!

/-- The leading coefficient of the cubic is `a`. -/
theorem cubicPoly_leadingCoeff (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).leadingCoeff = a := by
  rw [leadingCoeff, cubicPoly_natDegree a b c d ha, cubicPoly_coeff_three]

/-- The derivative of the cubic is `3a·X² + 2b·X + c`. -/
theorem cubicPoly_derivative (a b c d : ℂ) :
    (cubicPoly a b c d).derivative = C (3 * a) * X ^ 2 + C (2 * b) * X + C c := by
  simp only [cubicPoly, derivative_add, derivative_mul, derivative_C, derivative_X_pow,
    derivative_X, zero_mul, add_zero, zero_add, mul_one]
  rw [C_mul, C_mul]
  ring

/-! ## Part 2: The discriminant bridge

Mathlib's intrinsic discriminant `f.discr` (the normalized Sylvester determinant of `f` and
`f'`) coincides with the parent's coefficient polynomial `generalDiscriminant`. -/

/-- **The discriminant bridge.** Mathlib's intrinsic `Polynomial.discr` of the cubic equals the
parent's general cubic discriminant `Δ(a,b,c,d) = 18abcd − 4b³d + b²c² − 4ac³ − 27a²d²`. This
identifies the parent's hand-written polynomial with the determinant of the Sylvester matrix of
`f` and `f'`, modulo the standard sign normalization. -/
theorem cubic_discr_eq_generalDiscriminant (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).discr = generalDiscriminant a b c d := by
  rw [discr_of_degree_eq_three (cubicPoly_degree a b c d ha), cubicPoly_coeff_zero,
    cubicPoly_coeff_one, cubicPoly_coeff_two, cubicPoly_coeff_three, generalDiscriminant]
  ring

/-! ## Part 3: The resultant identity

The resultant of the cubic with its derivative is `−a` times the discriminant — the classical
relation `Res(f, f') = (−1)^{n(n−1)/2}·aₙ·Δ` for `n = 3`. -/

/-- **The discriminant as a resultant.** For the genuine cubic `f = a·X³ + b·X² + c·X + d`
(`a ≠ 0`), the resultant of `f` with its derivative `f'` is

  `Res(f, f') = −a · Δ(a,b,c,d)`.

This is the eliminant construction of the discriminant: `Res(f, f')` is the determinant of the
`5 × 5` Sylvester matrix of `f` and `f'`, and it equals `(−1)^{3·2/2}·a·Δ = −a·Δ`. For the
depressed cubic (`a = 1, b = 0`) this recovers the textbook value `4p³ + 27q²`. -/
theorem cubic_resultant_eq_neg_smul_discriminant (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).resultant (cubicPoly a b c d).derivative 3 2
      = -a * generalDiscriminant a b c d := by
  have hpos : 0 < (cubicPoly a b c d).degree := by
    rw [cubicPoly_degree a b c d ha]; norm_num
  have hdeg : (cubicPoly a b c d).natDegree = 3 := cubicPoly_natDegree a b c d ha
  have key := resultant_deriv hpos
  rw [hdeg, cubicPoly_leadingCoeff a b c d ha,
    cubic_discr_eq_generalDiscriminant a b c d ha] at key
  norm_num at key
  rw [key]; ring

/-! ## Part 4: The eliminant criterion

The resultant of a cubic with its derivative vanishes iff the cubic has a repeated root. -/

/-- **The eliminant criterion (discriminant form).** `Res(f, f') = 0 ⟺ Δ = 0`. Since `a ≠ 0`,
the resultant vanishes exactly when the discriminant does. -/
theorem cubic_resultant_eq_zero_iff (a b c d : ℂ) (ha : a ≠ 0) :
    (cubicPoly a b c d).resultant (cubicPoly a b c d).derivative 3 2 = 0
      ↔ generalDiscriminant a b c d = 0 := by
  rw [cubic_resultant_eq_neg_smul_discriminant a b c d ha, mul_eq_zero, neg_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h ha
    · exact h
  · intro h; exact Or.inr h

/-- **The eliminant criterion (root form).** For a cubic given by Vieta data on roots
`x₁, x₂, x₃` with `a ≠ 0`, the resultant `Res(f, f')` vanishes iff two of the roots coincide.
This is the classical meaning of the discriminant as the eliminant of `f` and `f'`. -/
theorem cubic_resultant_eq_zero_iff_repeated_root (a x₁ x₂ x₃ b c d : ℂ) (ha : a ≠ 0)
    (hb : b = -a * (x₁ + x₂ + x₃))
    (hc : c = a * (x₁ * x₂ + x₁ * x₃ + x₂ * x₃))
    (hd : d = -a * (x₁ * x₂ * x₃)) :
    (cubicPoly a b c d).resultant (cubicPoly a b c d).derivative 3 2 = 0
      ↔ (x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃) := by
  rw [cubic_resultant_eq_zero_iff a b c d ha, repeated_root_iff a x₁ x₂ x₃ b c d ha hb hc hd]

/-! ## Part 5: Sanity checks -/

/-- For the depressed cubic `X³ + p·X + q` the resultant with its derivative is the textbook
`4p³ + 27q²` (the negative of the standard discriminant `−4p³ − 27q²`). -/
example (p q : ℂ) :
    (cubicPoly 1 0 p q).resultant (cubicPoly 1 0 p q).derivative 3 2 = 4 * p ^ 3 + 27 * q ^ 2 := by
  rw [cubic_resultant_eq_neg_smul_discriminant 1 0 p q one_ne_zero, generalDiscriminant]; ring

/-- A perfect cube `(X − 2)³ = X³ − 6X² + 12X − 8` has a triple root, so `Res(f, f') = 0`. -/
example : (cubicPoly 1 (-6) 12 (-8)).resultant (cubicPoly 1 (-6) 12 (-8)).derivative 3 2 = 0 := by
  rw [cubic_resultant_eq_zero_iff 1 (-6) 12 (-8) one_ne_zero, generalDiscriminant]; norm_num

end SolutionOfCubicOQ01OQ01OQ02

-- Summary of key results
#check SolutionOfCubicOQ01OQ01OQ02.cubic_discr_eq_generalDiscriminant
#check SolutionOfCubicOQ01OQ01OQ02.cubic_resultant_eq_neg_smul_discriminant
#check SolutionOfCubicOQ01OQ01OQ02.cubic_resultant_eq_zero_iff
#check SolutionOfCubicOQ01OQ01OQ02.cubic_resultant_eq_zero_iff_repeated_root
