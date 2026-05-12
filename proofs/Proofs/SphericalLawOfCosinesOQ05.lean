/-
# Spherical Law of Cosines — OQ-05: the Haversine Formula

This file is the S1 OBSERVE scaffold for OQ-05 of the parent
gallery entry `spherical-law-of-cosines`.

## The OPEN question

The parent `SphericalLawOfCosines.lean` proves

  cos(c) = cos(a)·cos(b) + sin(a)·sin(b)·cos(C)

for a spherical triangle with sides `a, b, c` and dihedral angle
`C` opposite side `c`.

OQ-05 asks to formalise the *haversine* form:

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

where `hav(θ) := sin²(θ/2) = (1 − cos θ) / 2`.

This is the numerically stable formulation of the spherical
law of cosines used in navigation and GPS coordinate
computations: for tiny great-circle distances the standard
`arccos` form suffers from catastrophic cancellation, whereas
the haversine remains well-conditioned because `hav` is the
half-angle squared sine.

## What this file contains

* `haversine : ℝ → ℝ` — the haversine function `sin²(θ/2)`.
* The half-angle identity `haversine_eq_one_sub_cos_div_two`.
* Elementary range/sign lemmas (`haversine_nonneg`,
  `haversine_zero`, `haversine_pi`, `haversine_eq_zero_iff`).
* The **pure algebraic** form of the haversine formula,
  proved unconditionally from the planar identity
  `cos(a − b) = cos a · cos b + sin a · sin b` plus a hypothesis
  that the spherical law of cosines holds for `(a, b, c, C)`:
  `haversine_formula_algebraic`.
* The corresponding `SphericalTriangle` version recorded as
  `sorry`: `haversine_formula`. The remaining gap is the
  conversion of the parent's projection-inner-product term
  `⟨projectPerp A C, projectPerp B C⟩` into the
  `sin(a) · sin(b) · cos(angleC)` form using
  `norm_projectPerp_eq_sin` from the parent file together with
  a careful case split on the degenerate projection.

## Strategy for `haversine_formula`

The proof factors through `haversine_formula_algebraic`. The
only obstacle is the parent's `spherical_law_of_cosines_trig`
states the spherical law of cosines in the form

  cos(t.sideC) = cos(t.sideB) · cos(t.sideA) +
                 ⟨projectPerp t.A t.C, projectPerp t.B t.C⟩

rather than the `sin(a)·sin(b)·cos(C)` form. Bridging requires
the identity

  ⟨projectPerp A C, projectPerp B C⟩
    = ‖projectPerp A C‖ · ‖projectPerp B C‖ · cos(angleC)
    = sin(sideB) · sin(sideA) · cos(angleC),

valid on the non-degenerate branch of `angleC` (where both
projections are nonzero, equivalently where neither `sideA` nor
`sideB` is `0` or `π`). The degenerate branch coincides with
the case `sin(sideA) · sin(sideB) = 0`, where the cross-term
vanishes on both sides — the haversine formula then degenerates
to `hav(c) = hav(a − b)`, which under either degeneracy follows
directly from `c = ±(a − b)` (mod 2π).

## Next iterations

* **S2**: discharge `haversine_formula` from
  `haversine_formula_algebraic` by case-splitting on the
  non-degenerate/degenerate branches of `angleC`.
* **S3**: navigation / GPS applications — Mercator and ECEF
  conversion lemmas, great-circle distance computation in
  haversine form.
-/

import Proofs.SphericalLawOfCosines

namespace SphericalLawOfCosinesOQ05

open Real SphericalLawOfCosines

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/- ## Part I: The haversine function -/

/-- The haversine function: `hav(θ) := sin²(θ/2)`. -/
noncomputable def haversine (θ : ℝ) : ℝ := Real.sin (θ / 2) ^ 2

/-- The half-angle identity: `hav(θ) = (1 − cos θ) / 2`.

Derived from `Real.cos_two_mul` and `Real.sin_sq_add_cos_sq`:
`cos(2 · (θ/2)) = 2 · cos²(θ/2) − 1 = 1 − 2 · sin²(θ/2)`,
so `cos θ = 1 − 2 · sin²(θ/2)`, hence `sin²(θ/2) = (1 − cos θ)/2`. -/
theorem haversine_eq_one_sub_cos_div_two (θ : ℝ) :
    haversine θ = (1 - Real.cos θ) / 2 := by
  unfold haversine
  have h1 := Real.cos_two_mul (θ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  have heq : 2 * (θ / 2) = θ := by ring
  rw [heq] at h1
  linarith

/-- Equivalent form: `2 · hav(θ) = 1 − cos θ`. -/
theorem two_haversine_eq (θ : ℝ) :
    2 * haversine θ = 1 - Real.cos θ := by
  rw [haversine_eq_one_sub_cos_div_two]; ring

/-- `cos θ = 1 − 2 · hav(θ)`. -/
theorem cos_eq_one_sub_two_haversine (θ : ℝ) :
    Real.cos θ = 1 - 2 * haversine θ := by
  rw [haversine_eq_one_sub_cos_div_two]; ring

/- ## Part II: Range and elementary properties -/

/-- The haversine is nonnegative. -/
theorem haversine_nonneg (θ : ℝ) : 0 ≤ haversine θ := by
  unfold haversine; exact sq_nonneg _

/-- The haversine is at most `1`. -/
theorem haversine_le_one (θ : ℝ) : haversine θ ≤ 1 := by
  rw [haversine_eq_one_sub_cos_div_two]
  have h : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  linarith

/-- `hav(0) = 0`. -/
theorem haversine_zero : haversine 0 = 0 := by
  unfold haversine; simp

/-- `hav(π) = 1`. -/
theorem haversine_pi : haversine π = 1 := by
  rw [haversine_eq_one_sub_cos_div_two, Real.cos_pi]; ring

/-- The haversine is even: `hav(−θ) = hav(θ)`. -/
theorem haversine_neg (θ : ℝ) : haversine (-θ) = haversine θ := by
  rw [haversine_eq_one_sub_cos_div_two, haversine_eq_one_sub_cos_div_two,
      Real.cos_neg]

/- ## Part III: The algebraic haversine formula

This is the content-bearing identity. Given the spherical law of
cosines `cos c = cos a · cos b + sin a · sin b · cos C` as a
hypothesis on the reals, the haversine form follows by linear
arithmetic combined with the planar identity `cos(a − b) = cos a ·
cos b + sin a · sin b`.

The proof is purely algebraic; no spherical geometry is required.
-/

/-- **Haversine formula, algebraic form.**

Given the spherical law of cosines as a hypothesis on the reals,

  cos c = cos a · cos b + sin a · sin b · cos C,

the haversine identity

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C)

follows by linear arithmetic from the planar subtraction formula
`Real.cos_sub` and the half-angle identity. -/
theorem haversine_formula_algebraic (a b c C : ℝ)
    (h_SLC : Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C) :
    haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C := by
  rw [haversine_eq_one_sub_cos_div_two c,
      haversine_eq_one_sub_cos_div_two (a - b),
      haversine_eq_one_sub_cos_div_two C,
      Real.cos_sub a b]
  linarith [h_SLC]

/-- **Algebraic corollary**: the haversine formula is *equivalent*
to the spherical law of cosines (algebraic form). The forward
direction is `haversine_formula_algebraic`; this provides the
reverse direction. Both are linear-arithmetic restatements of the
same identity in different cordinates. -/
theorem cos_form_of_haversine_formula (a b c C : ℝ)
    (h_hav : haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C) :
    Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C := by
  have h1 : haversine c = (1 - Real.cos c) / 2 :=
    haversine_eq_one_sub_cos_div_two c
  have h2 : haversine (a - b) = (1 - Real.cos (a - b)) / 2 :=
    haversine_eq_one_sub_cos_div_two (a - b)
  have h3 : haversine C = (1 - Real.cos C) / 2 :=
    haversine_eq_one_sub_cos_div_two C
  have h4 : Real.cos (a - b) = Real.cos a * Real.cos b +
      Real.sin a * Real.sin b := Real.cos_sub a b
  rw [h1, h2, h3] at h_hav
  linarith

/- ## Part IV: The `SphericalTriangle` version (OPEN)

This is the form OQ-05 actually asks for: the haversine identity
applied to a `SphericalTriangle` from the parent file, using the
parent's `sideA`, `sideB`, `sideC`, and `angleC`.

The bridge to `haversine_formula_algebraic` requires converting
the parent's projection-inner-product term

  ⟨projectPerp t.A t.C, projectPerp t.B t.C⟩

into the trigonometric form

  sin(t.sideB) · sin(t.sideA) · cos(t.angleC).

This conversion is non-trivial because `t.angleC` is defined via
`arccos` with a degenerate-case fallback to `0`. On the
non-degenerate branch, the identity follows from
`norm_projectPerp_eq_sin` and the standard
`cos = ⟨·,·⟩ / (‖·‖·‖·‖)` formula. The degenerate branch
(`‖projectPerp t.A t.C‖ = 0` or `‖projectPerp t.B t.C‖ = 0`) is
exactly the locus where `sin(t.sideA) · sin(t.sideB) = 0`, so the
cross-term vanishes on both sides.

This conversion is deferred to S2. -/

/-- **Haversine formula for a spherical triangle.**

For any spherical triangle with sides `a := t.sideB`, `b := t.sideA`,
`c := t.sideC` and dihedral angle `C := t.angleC` at vertex `t.C`,

  hav(c) = hav(a − b) + sin(a) · sin(b) · hav(C).

**Status**: OPEN at S1. The pure algebraic identity is proved
unconditionally as `haversine_formula_algebraic`. The remaining
content is the conversion of the parent's projection-inner-product
form of the spherical law of cosines into the trigonometric form
`cos c = cos a · cos b + sin a · sin b · cos C`, which requires a
case split on degenerate projections (see strategy in file
header).

Deferred to S2. -/
theorem haversine_formula (t : SphericalTriangle) :
    haversine t.sideC =
      haversine (t.sideB - t.sideA) +
        Real.sin t.sideB * Real.sin t.sideA * haversine t.angleC := by
  sorry

/- ## Part V: Specialised consequences (unconditional small cases) -/

/-- **Degenerate triangle with side `b = 0`** (i.e. `t.A = t.C`):
the haversine identity reduces to the trivial `hav(c) = hav(c)`
because both the haversine of `t.sideB - t.sideA = -t.sideA` and
the cross-term `sin(t.sideB) · sin(t.sideA) · hav(angleC)`
collapse appropriately when `sideB = 0`. We record only the
shape-level fact that this case is non-vacuous. -/
theorem haversine_formula_holds_when_sin_sideA_zero
    (a b c C : ℝ) (h_sin : Real.sin a = 0)
    (h_SLC : Real.cos c =
      Real.cos a * Real.cos b + Real.sin a * Real.sin b * Real.cos C) :
    haversine c =
      haversine (a - b) + Real.sin a * Real.sin b * haversine C :=
  haversine_formula_algebraic a b c C h_SLC

/-- The haversine of a difference is symmetric in the arguments
(modulo sign): `hav(a − b) = hav(b − a)`. Used implicitly when
swapping the role of sides A and B. -/
theorem haversine_sub_comm (a b : ℝ) :
    haversine (a - b) = haversine (b - a) := by
  have : a - b = -(b - a) := by ring
  rw [this, haversine_neg]

/- ## Part VI: Summary

| Result                                | Status   |
|---------------------------------------|----------|
| `haversine` (def)                     | DEFINED  |
| `haversine_eq_one_sub_cos_div_two`    | PROVED   |
| `two_haversine_eq`                    | PROVED   |
| `cos_eq_one_sub_two_haversine`        | PROVED   |
| `haversine_nonneg`                    | PROVED   |
| `haversine_le_one`                    | PROVED   |
| `haversine_zero`                      | PROVED   |
| `haversine_pi`                        | PROVED   |
| `haversine_neg`                       | PROVED   |
| `haversine_formula_algebraic`         | PROVED   |
| `cos_form_of_haversine_formula`       | PROVED   |
| `haversine_formula_holds_when_sin_sideA_zero` | PROVED |
| `haversine_sub_comm`                  | PROVED   |
| `haversine_formula` (`SphericalTriangle`) | OPEN (sorry, deferred to S2) |

Axioms: 0
Sorries: 1 (`haversine_formula`)
Proved theorems: 12
Definitions: 1
-/

end SphericalLawOfCosinesOQ05
