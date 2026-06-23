/-
# Spherical Law of Sines — OQ-03: the Four-Parts (Cotangent) Rule

This file is the S2 SCAFFOLD for OQ-03 of the parent gallery entry
`spherical-law-of-sines`.

## The OPEN question

For a spherical triangle with unit-vector vertices `A, B, C : Fin 3 → ℝ`,
arc-length sides
  a := arcLen B C,    b := arcLen A C,    c := arcLen A B,
and dihedral angles
  α := dihedralAngle A B C,    β := dihedralAngle B A C,
  γ := dihedralAngle C A B,
prove the cotangent four-parts formula in cleared-of-cotangents
**polynomial form**

  sin α · cos a · sin b
    = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ.

(Dividing through by `sin a · sin α` recovers the classical
`cot a · sin b = cos b · cos γ + sin γ · cot α`. We state the
polynomial form to avoid introducing a local `cot` and to side-step
the `sin a ≠ 0`, `sin α ≠ 0` non-degeneracy hypotheses until S4.)

## Status

* **S1 OBSERVE** (PR #18229, merged 2026-05-12): documented the
  formula, its place in the catalogue, and the proof strategy.
* **S2 SCAFFOLD** (this file, current PR): create the file with
  imports + helper lemmas + main theorem statement.  All
  computational content is marked `sorry` for S3 ACT.
* **S3 ACT** (planned): discharge the strategic
  `cotangent_rule_from_cosines` sorry by a direct two-applications-
  of-the-law-of-cosines algebraic substitution, then close
  `spherical_cotangent_rule_polynomial` and the
  `spherical_law_of_cosines_local` bridge.

## Proof strategy (Route A: derive from law of cosines)

The cotangent rule is a one-line corollary of two applications of
the spherical law of cosines:

  (1)  cos b = cos a · cos c + sin a · sin c · cos β,
  (2)  cos c = cos a · cos b + sin a · sin b · cos γ.

Substituting (2) into (1) and using the law of sines
`sin γ / sin c = sin α / sin a` (the parent's
`spherical_law_of_sines_all_sq` provides the squared form)
yields after algebraic manipulation:

  cos a · sin α · sin b
    = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ.

The strategic sorry `cotangent_rule_from_cosines` records this
algebra; it is closed by `linear_combination` in S3 ACT once both
applications of the law of cosines are in scope as hypotheses.

## Framework

The parent `SphericalLawOfSines.lean` is written in the
`Fin 3 → ℝ` cross-product framework (with `dot`, `normSq`, `arcLen`,
`IsUnit3`, `dihedralAngle`).  The sibling `SphericalLawOfCosines.lean`
uses `EuclideanSpace ℝ (Fin 3)` (with `IsUnitVec`, `arcLength`,
`@inner`).  To keep the new content in a single framework, we
state the law of cosines locally as
`spherical_law_of_cosines_local`, in the parent's framework.  The
S3 ACT discharge will prove it directly by `linear_combination`
from the parent's `lagrange_identity` (mirroring the approach taken
in `SphericalLawOfSines.lean`'s `sin_sq_dihedralAngle`), avoiding a
framework bridge.

## What this file contains

* Helper lemma `cos_arcLen` : for unit vectors `u, v`,
  `cos (arcLen u v) = dot u v`.  Strategic `sorry` to be closed by
  `Real.cos_arccos` + Cauchy–Schwarz from `lagrange_identity` in S3.
* Helper lemma `sin_arcLen_nonneg` : `0 ≤ sin (arcLen u v)`.  Strategic
  `sorry` to be closed by `Real.sin_nonneg_of_nonneg_of_le_pi` plus
  `Real.arccos_nonneg`, `Real.arccos_le_pi`.
* Helper lemma `cos_arcLen_eq_dot` : the inner-product form of the
  spherical law of cosines without the dihedral angle — purely
  expressing `cos a = ⟨A, B⟩` etc.  This is the trivial corollary
  of `cos_arcLen`.
* Strategic theorem `spherical_law_of_cosines_local` : the
  parent-framework version of the spherical law of cosines
  (`cos c = cos a · cos b + ⟨projPerp A C, projPerp B C⟩` in the
  general form; the trigonometric form follows in S3 by
  multiplying through with the `projPerp` norms).
* Main theorem `spherical_cotangent_rule_polynomial` : the boxed
  polynomial-form four-parts formula.  Strategic `sorry` to be
  closed in S3 by `linear_combination` over two applications of
  `spherical_law_of_cosines_local` plus the parent's
  `spherical_law_of_sines_all_sq`.

## References

* Smart, W. M., *Textbook on Spherical Astronomy* (1977), §3.7.
* Todhunter, I., *Spherical Trigonometry* (1886), §62.
* Bowditch, N., *The American Practical Navigator* (2002), §22.6.
-/

import Proofs.SphericalLawOfSines
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace SphericalLawOfSines

/-! ### Helper lemmas (S3 ACT will discharge) -/

/-- `cos (arcLen u v) = dot u v` for unit vectors `u, v`.

This is the unit-vector form of `Real.cos_arccos`; the hypothesis
`-1 ≤ dot u v ≤ 1` follows from the Cauchy–Schwarz inequality
applied to unit vectors, which can be extracted from the parent's
`lagrange_identity` and `normSq_cross_nonneg`.

**S3 ACT plan**: unfold `arcLen`; apply `Real.cos_arccos` with
the bounds `-1 ≤ dot u v` and `dot u v ≤ 1` obtained from
`(dot u v) ^ 2 ≤ normSq u · normSq v = 1`. -/
theorem cos_arcLen (u v : Fin 3 → ℝ) (hu : IsUnit3 u) (hv : IsUnit3 v) :
    Real.cos (arcLen u v) = dot u v := by
  unfold IsUnit3 at hu hv
  unfold arcLen
  have h_lag := lagrange_identity u v
  have h_nn := normSq_cross_nonneg u v
  have h_bound_sq : (dot u v) ^ 2 ≤ 1 := by
    have h : (dot u v) ^ 2 ≤ normSq u * normSq v := by linarith
    rw [hu, hv] at h; linarith
  have h_upper : dot u v ≤ 1 := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v - 1)]
  have h_lower : -1 ≤ dot u v := by
    nlinarith [h_bound_sq, sq_nonneg (dot u v + 1)]
  exact Real.cos_arccos h_lower h_upper

/-- `0 ≤ sin (arcLen u v)` for any pair `u, v : Fin 3 → ℝ`.

Since `arcLen u v = Real.arccos (dot u v)`, the value lies in `[0, π]`
unconditionally on the inputs, by `Real.arccos_nonneg` and
`Real.arccos_le_pi`.  Then `Real.sin_nonneg_of_nonneg_of_le_pi`
gives the result.

**S3 ACT plan**: unfold `arcLen` and apply
`Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _)
(Real.arccos_le_pi _)`. -/
theorem sin_arcLen_nonneg (u v : Fin 3 → ℝ) :
    0 ≤ Real.sin (arcLen u v) := by
  unfold arcLen
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- The inner-product (general) form of the **spherical law of
cosines** in the parent's `Fin 3 → ℝ` framework.

For unit vectors `A, B, C`, the inner product `dot A B` decomposes
as the diagonal term `dot A C · dot B C` plus the cross term
`dot (projPerp A C) (projPerp B C)`:

  ⟨A, B⟩ = ⟨A, C⟩ · ⟨B, C⟩ + ⟨projPerp A C, projPerp B C⟩.

This is the unit-`C` projection identity; specialised to unit
vectors it is exactly the spherical law of cosines with the
cosine of the dihedral angle absorbed into the inner product of
the projections.  The sibling `SphericalLawOfCosines.lean` proves
the corresponding statement in the `EuclideanSpace` framework
(`spherical_law_of_cosines_algebraic`, line 249).

**S3 ACT plan**: expand `projPerp` and the inner products, then
`linear_combination` over the unit-`C` hypothesis `normSq C = 1`. -/
theorem spherical_law_of_cosines_local (A B C : Fin 3 → ℝ) (hC : IsUnit3 C) :
    dot A B = dot A C * dot B C + dot (projPerp A C) (projPerp B C) := by
  have hC' : C 0 * C 0 + C 1 * C 1 + C 2 * C 2 = 1 := unit_sum C hC
  simp only [dot, projPerp, Fin.sum_univ_three]
  linear_combination -(A 0 * C 0 + A 1 * C 1 + A 2 * C 2) *
    (B 0 * C 0 + B 1 * C 1 + B 2 * C 2) * hC'

/-! ### Main statement: the four-parts (cotangent) rule -/

/-- **Four-parts / cotangent rule** for a spherical triangle, in
cleared-of-cotangents polynomial form.

For a spherical triangle on the unit sphere with vertices
`A, B, C : Fin 3 → ℝ`, arc-length sides

    a := arcLen B C,    b := arcLen A C,    c := arcLen A B,

and dihedral angles

    α := dihedralAngle A B C,    γ := dihedralAngle C A B,

the four consecutive elements `(a, α, b, γ)` satisfy

    sin α · cos a · sin b
      = sin a · sin α · cos b · cos γ + sin a · cos α · sin γ.

Dividing through by `sin a · sin α` (both nonzero on a
non-degenerate spherical triangle) recovers the classical
`cot a · sin b = cos b · cos γ + sin γ · cot α`.

**Status**: Strategic `sorry`.  S3 ACT discharges by applying
`spherical_law_of_cosines_local` twice (once on side `b`, once on
side `c`), substituting, and using
`spherical_law_of_sines_all_sq` to identify the resulting
`sin γ / sin c` ratio with `sin α / sin a`.

**Proof outline** (records the algebra for S3):

1.  Apply `spherical_law_of_cosines_local` to `(A, B, C)`:
    `dot A B = dot A C · dot B C + dot (projPerp A C) (projPerp B C)`.
    Using `cos_arcLen` and the trigonometric expansion of the
    dihedral-angle inner product (which the parent's
    `sin_sq_dihedralAngle` provides up to sign), this rewrites as

      cos c = cos a · cos b + sin a · sin b · cos γ.  (∗)

2.  Apply `spherical_law_of_cosines_local` to `(B, C, A)`:

      cos a = cos b · cos c + sin b · sin c · cos α.  (∗∗)

3.  Substitute (∗) into (∗∗) to eliminate `cos c`:

      cos a = cos b · (cos a · cos b + sin a · sin b · cos γ)
                + sin b · sin c · cos α,

    that is,

      cos a · (1 - cos² b) = sin a · sin b · cos b · cos γ
                            + sin b · sin c · cos α.

    Since `sin² b = 1 - cos² b`, this is

      cos a · sin² b = sin a · sin b · cos b · cos γ
                        + sin b · sin c · cos α,

    and dividing by `sin b` (non-degenerate),

      cos a · sin b = sin a · cos b · cos γ + sin c · cos α.  (†)

4.  Apply the law of sines `sin γ · sin a = sin α · sin c`
    (rearranged from the parent's `spherical_law_of_sines_all_sq`)
    to express `sin c = sin γ · sin a / sin α`, substitute into (†),
    and multiply through by `sin α`:

      cos a · sin b · sin α
        = sin a · sin α · cos b · cos γ + sin γ · sin a · cos α,

    which is the boxed polynomial form.

5.  No `sin a ≠ 0`, `sin α ≠ 0` hypotheses are needed for the
    polynomial form (both sides reduce to `0 = 0` in the
    degenerate cases).  The classical form requires non-degeneracy
    and is deferred to S4. -/
theorem spherical_cotangent_rule_polynomial
    (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    Real.sin (dihedralAngle A B C) * Real.cos (arcLen B C)
        * Real.sin (arcLen A C)
      = Real.sin (arcLen B C) * Real.sin (dihedralAngle A B C)
          * Real.cos (arcLen A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (arcLen B C) * Real.cos (dihedralAngle A B C)
          * Real.sin (dihedralAngle C A B) := by
  sorry

/-! ### Summary

| Result                                                            | Status |
|-------------------------------------------------------------------|--------|
| `cos_arcLen`: cos(arcLen u v) = dot u v for unit u, v             | proved |
| `sin_arcLen_nonneg`: 0 ≤ sin(arcLen u v)                          | proved |
| `spherical_law_of_cosines_local` (general inner-product form)     | proved |
| `spherical_cotangent_rule_polynomial` (main theorem)              | sorry  |

Sorries: 1 (strategic — `spherical_cotangent_rule_polynomial` deferred to S3b ACT)
Axioms:  0
-/

end SphericalLawOfSines
