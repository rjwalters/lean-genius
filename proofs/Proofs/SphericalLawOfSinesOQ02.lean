/-
# Spherical Law of Sines — OQ-02: the Dual Spherical Law of Cosines

This file proves OQ-02 of the parent gallery entry
`spherical-law-of-sines`.

## The question

For a spherical triangle with unit-vector vertices `A, B, C : Fin 3 → ℝ`,
arc-length sides

    a := arcLen B C,    b := arcLen A C,    c := arcLen A B,

and dihedral (interior) angles

    α := dihedralAngle A B C,    β := dihedralAngle B A C,
    γ := dihedralAngle C A B,

prove the **dual spherical law of cosines** for the angle `γ` opposite side `c`:

    cos γ = - cos α · cos β + sin α · sin β · cos c.

This complements the *standard* spherical law of cosines (`cos c = cos a · cos b
+ sin a · sin b · cos γ`, available locally as `spherical_law_of_cosines_local`
in the sibling OQ-03 file) and the law of sines.  Together they close the
classical spherical-trigonometry suite: a side from the other two sides and an
angle, *and* an angle from the other two angles and a side.

## Proof strategy (no polar triangle)

The textbook route applies the standard law of cosines to the polar (dual)
triangle.  We avoid building the polar triangle and instead reuse the two
unconditional product identities from OQ-03:

    cos (dih A B C) · sin c · sin b = ⟨projPerp B A, projPerp C A⟩     (cos form)
    sin (dih A B C) · sin c · sin b = |det[A,B,C]|                      (sin form)

Writing `p = ⟨A,B⟩ = cos c`, `q = ⟨A,C⟩ = cos b`, `r = ⟨B,C⟩ = cos a`, the inner
products of the perpendicular projections evaluate (via the local law of
cosines) to

    ⟨projPerp B A, projPerp C A⟩ = r − p·q,
    ⟨projPerp A B, projPerp C B⟩ = q − p·r,
    ⟨projPerp A C, projPerp B C⟩ = p − q·r,

while `sin²c = 1 − p²` and `det[A,B,C]² = 1 − p² − q² − r² + 2pqr` (the Gram
determinant of three unit vectors).  Multiplying the target identity through by
`sin a · sin b · sin²c` and substituting these product identities reduces it to
the purely algebraic **cleared identity**

    (p − q·r)(1 − p²) = −(r − p·q)(q − p·r) + det² · p,                 (K)

which is a polynomial identity in `p, q, r` (proved by `ring` after the Gram
substitution).  Cancelling the non-zero factor `sin a · sin b · sin²c` (a
proper spherical triangle has `sin a, sin b, sin c ≠ 0`) recovers the honest
`cos γ = …` form.  No square roots survive: the two `sin`-form factors combine
as `|det| · |det| = det²`.

The two sibling angle laws (for `α` and `β`) follow from the main statement by
relabelling the vertices, using `dihedralAngle_comm_last`.

## Framework

Everything is stated in the parent's `Fin 3 → ℝ` cross-product framework
(`dot`, `normSq`, `arcLen`, `IsUnit3`, `tripleProduct`, `dihedralAngle`),
reusing the OQ-03 helpers `cos_arcLen`, `spherical_law_of_cosines_local`,
`cos_dihedralAngle_mul`, `sin_dihedralAngle_mul`.

## References

* Todhunter, I., *Spherical Trigonometry* (1886), §§37–40 (polar triangle and
  the dual law of cosines).
* Smart, W. M., *Textbook on Spherical Astronomy* (1977), §1.7.
* Van Brummelen, G., *Heavenly Mathematics* (2013), Ch. 4.
-/

import Proofs.SphericalLawOfSinesOQ03
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

namespace SphericalLawOfSines

/-! ### The Gram determinant of three vectors -/

/-- **Cauchy–Binet / Gram identity** for the scalar triple product (no unit
hypotheses).  `det[A,B,C]² = det` of the Gram matrix `(⟨·,·⟩)`:

    det² = |A|²|B|²|C|² + 2⟨A,B⟩⟨B,C⟩⟨A,C⟩
              − |A|²⟨B,C⟩² − |B|²⟨A,C⟩² − |C|²⟨A,B⟩².

A pure polynomial identity, closed by `ring` after unfolding. -/
theorem tripleProduct_sq_eq (A B C : Fin 3 → ℝ) :
    tripleProduct A B C ^ 2 =
      normSq A * normSq B * normSq C
        + 2 * dot A B * dot B C * dot A C
        - normSq A * dot B C ^ 2
        - normSq B * dot A C ^ 2
        - normSq C * dot A B ^ 2 := by
  simp [tripleProduct, normSq, dot, crossProduct, Fin.sum_univ_three]
  ring

/-- Gram identity specialised to **unit** vectors: the diagonal terms collapse to
`1`, giving `det² = 1 − p² − q² − r² + 2pqr` with `p = ⟨A,B⟩`, `q = ⟨A,C⟩`,
`r = ⟨B,C⟩`. -/
theorem tripleProduct_sq_unit (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    tripleProduct A B C ^ 2 =
      1 - dot A B ^ 2 - dot A C ^ 2 - dot B C ^ 2
        + 2 * dot A B * dot A C * dot B C := by
  have hA' : normSq A = 1 := hA
  have hB' : normSq B = 1 := hB
  have hC' : normSq C = 1 := hC
  rw [tripleProduct_sq_eq A B C, hA', hB', hC']; ring

/-! ### The algebraic core: the cleared dual law of cosines -/

/-- **Cleared (polynomial) form of the dual law of cosines.**

With `p = ⟨A,B⟩ = cos c`, `q = ⟨A,C⟩ = cos b`, `r = ⟨B,C⟩ = cos a`,

    (p − q·r)(1 − p²) = −(r − p·q)(q − p·r) + det[A,B,C]² · p.

This holds for all unit vectors (no non-degeneracy needed); it is the identity
`K` obtained by clearing `sin a · sin b · sin²c` from the honest dual law.  The
proof is `ring` once the Gram determinant `det²` is expanded. -/
theorem dual_law_of_cosines_polynomial (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C) :
    (dot A B - dot A C * dot B C) * (1 - dot A B ^ 2)
      = -((dot B C - dot A B * dot A C) * (dot A C - dot A B * dot B C))
        + tripleProduct A B C ^ 2 * dot A B := by
  rw [tripleProduct_sq_unit A B C hA hB hC]; ring

/-! ### The dual spherical law of cosines -/

/-- **Dual spherical law of cosines** for the angle `γ = dihedralAngle C A B`
opposite the side `c = arcLen A B`.

For a non-degenerate spherical triangle on the unit sphere with unit-vector
vertices `A, B, C` (so `sin a, sin b, sin c ≠ 0`),

    cos γ = - cos α · cos β + sin α · sin β · cos c,

where `α = dihedralAngle A B C`, `β = dihedralAngle B A C` are the other two
interior angles and `c = arcLen A B`.

The proof multiplies through by `sin a · sin b · sin²c`, replaces the
`cos`/`sin` of the dihedral angles by their unconditional product identities
(`cos_dihedralAngle_mul`, `sin_dihedralAngle_mul`) and the inner products of the
perpendicular projections by the local law of cosines, and reduces to the
algebraic identity `dual_law_of_cosines_polynomial`; the common non-zero factor
is then cancelled. -/
theorem dual_spherical_law_of_cosines (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (ha : Real.sin (arcLen B C) ≠ 0)
    (hb : Real.sin (arcLen A C) ≠ 0)
    (hc : Real.sin (arcLen A B) ≠ 0) :
    Real.cos (dihedralAngle C A B) =
      - Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C)
        + Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C)
          * Real.cos (arcLen A B) := by
  -- Inner products of perpendicular projections, via the local law of cosines.
  have hPA : dot (projPerp B A) (projPerp C A) = dot B C - dot A B * dot A C := by
    have h := spherical_law_of_cosines_local B C A hA
    rw [dot_comm B A, dot_comm C A] at h; linarith
  have hPB : dot (projPerp A B) (projPerp C B) = dot A C - dot A B * dot B C := by
    have h := spherical_law_of_cosines_local A C B hB
    rw [dot_comm C B] at h; linarith
  have hPC : dot (projPerp A C) (projPerp B C) = dot A B - dot A C * dot B C := by
    have h := spherical_law_of_cosines_local A B C hC
    linarith
  -- Product (cleared) forms of the three dihedral cosines.
  have hca_p : Real.cos (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)
      = dot B C - dot A B * dot A C := by
    rw [cos_dihedralAngle_mul A B C hA hB hC]; exact hPA
  have hcb_p : Real.cos (dihedralAngle B A C) * Real.sin (arcLen A B) * Real.sin (arcLen B C)
      = dot A C - dot A B * dot B C := by
    rw [show Real.sin (arcLen A B) = Real.sin (arcLen B A) from by rw [arcLen_comm A B],
        cos_dihedralAngle_mul B A C hB hA hC]; exact hPB
  have hcg_p : Real.cos (dihedralAngle C A B) * Real.sin (arcLen A C) * Real.sin (arcLen B C)
      = dot A B - dot A C * dot B C := by
    rw [show Real.sin (arcLen A C) = Real.sin (arcLen C A) from by rw [arcLen_comm A C],
        show Real.sin (arcLen B C) = Real.sin (arcLen C B) from by rw [arcLen_comm B C],
        cos_dihedralAngle_mul C A B hC hA hB]; exact hPC
  -- Product (cleared) forms of the two relevant dihedral sines.
  have hsα_p : Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)
      = Real.sqrt (tripleProduct A B C ^ 2) := sin_dihedralAngle_mul A B C hA hB hC
  have hsβ_p : Real.sin (dihedralAngle B A C) * Real.sin (arcLen A B) * Real.sin (arcLen B C)
      = Real.sqrt (tripleProduct A B C ^ 2) := by
    rw [show Real.sin (arcLen A B) = Real.sin (arcLen B A) from by rw [arcLen_comm A B],
        sin_dihedralAngle_mul B A C hB hA hC, ← tripleProduct_sq_swap A B C]
  -- `|det| · |det| = det²`.
  have hSS : Real.sqrt (tripleProduct A B C ^ 2) * Real.sqrt (tripleProduct A B C ^ 2)
      = tripleProduct A B C ^ 2 := Real.mul_self_sqrt (sq_nonneg _)
  -- `sin²c = 1 − cos²c`.
  have hB' : normSq B = 1 := hB
  have hsc2 : Real.sin (arcLen A B) ^ 2 = 1 - dot A B ^ 2 := by
    rw [sin_sq_arcLen A B hA hB, normSq_projPerp B A hA, hB', dot_comm B A]
  -- `cos c = ⟨A,B⟩`.
  have hcc : Real.cos (arcLen A B) = dot A B := cos_arcLen A B hA hB
  -- The non-zero factor we cancel.
  have hD : Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero 2 hc)
  -- Three "multiply-out" lemmas collecting the cleared products.
  have e1 : Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
        * Real.cos (dihedralAngle C A B)
      = (dot A B - dot A C * dot B C) * Real.sin (arcLen A B) ^ 2 := by
    linear_combination (Real.sin (arcLen A B) ^ 2) * hcg_p
  have e2 : Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
        * (Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C))
      = (dot B C - dot A B * dot A C) * (dot A C - dot A B * dot B C) := by
    linear_combination (dot A C - dot A B * dot B C) * hca_p
      + (Real.cos (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)) * hcb_p
  have e3 : Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
        * (Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C))
      = tripleProduct A B C ^ 2 := by
    linear_combination Real.sqrt (tripleProduct A B C ^ 2) * hsα_p
      + (Real.sin (dihedralAngle A B C) * Real.sin (arcLen A B) * Real.sin (arcLen A C)) * hsβ_p
      + hSS
  -- The cleared identity, then cancel the common factor.
  have key : Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
        * Real.cos (dihedralAngle C A B)
      = Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
        * (- Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C)
           + Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C)
             * Real.cos (arcLen A B)) := by
    calc Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
          * Real.cos (dihedralAngle C A B)
        = (dot A B - dot A C * dot B C) * Real.sin (arcLen A B) ^ 2 := e1
      _ = -((dot B C - dot A B * dot A C) * (dot A C - dot A B * dot B C))
            + tripleProduct A B C ^ 2 * dot A B := by
          rw [hsc2]; exact dual_law_of_cosines_polynomial A B C hA hB hC
      _ = -(Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
              * (Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C)))
            + (Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
              * (Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C))) * dot A B := by
          rw [e2, e3]
      _ = Real.sin (arcLen B C) * Real.sin (arcLen A C) * Real.sin (arcLen A B) ^ 2
            * (- Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle B A C)
               + Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle B A C)
                 * Real.cos (arcLen A B)) := by
          rw [hcc]; ring
  exact mul_left_cancel₀ hD key

/-- **Dual spherical law of cosines** for the angle `α = dihedralAngle A B C`
opposite the side `a = arcLen B C`:

    cos α = - cos β · cos γ + sin β · sin γ · cos a,

with `β = dihedralAngle B A C`, `γ = dihedralAngle C A B`.  Obtained from the
main statement by relabelling `(A, B, C) ↦ (B, C, A)`. -/
theorem dual_spherical_law_of_cosines_A (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (ha : Real.sin (arcLen B C) ≠ 0)
    (hb : Real.sin (arcLen A C) ≠ 0)
    (hc : Real.sin (arcLen A B) ≠ 0) :
    Real.cos (dihedralAngle A B C) =
      - Real.cos (dihedralAngle B A C) * Real.cos (dihedralAngle C A B)
        + Real.sin (dihedralAngle B A C) * Real.sin (dihedralAngle C A B)
          * Real.cos (arcLen B C) := by
  have h := dual_spherical_law_of_cosines B C A hB hC hA
    (by rwa [arcLen_comm C A]) (by rwa [arcLen_comm B A]) ha
  rw [dihedralAngle_comm_last B C A, dihedralAngle_comm_last C B A] at h
  exact h

/-- **Dual spherical law of cosines** for the angle `β = dihedralAngle B A C`
opposite the side `b = arcLen A C`:

    cos β = - cos α · cos γ + sin α · sin γ · cos b,

with `α = dihedralAngle A B C`, `γ = dihedralAngle C A B`.  Obtained from the
main statement by relabelling `(A, B, C) ↦ (A, C, B)`. -/
theorem dual_spherical_law_of_cosines_B (A B C : Fin 3 → ℝ)
    (hA : IsUnit3 A) (hB : IsUnit3 B) (hC : IsUnit3 C)
    (ha : Real.sin (arcLen B C) ≠ 0)
    (hb : Real.sin (arcLen A C) ≠ 0)
    (hc : Real.sin (arcLen A B) ≠ 0) :
    Real.cos (dihedralAngle B A C) =
      - Real.cos (dihedralAngle A B C) * Real.cos (dihedralAngle C A B)
        + Real.sin (dihedralAngle A B C) * Real.sin (dihedralAngle C A B)
          * Real.cos (arcLen A C) := by
  have h := dual_spherical_law_of_cosines A C B hA hC hB
    (by rwa [arcLen_comm C B]) hc hb
  rw [dihedralAngle_comm_last A C B] at h
  exact h

/-! ### Summary

| Result                                                              | Status |
|---------------------------------------------------------------------|--------|
| `tripleProduct_sq_eq`  (general Gram/Cauchy–Binet identity)         | proved |
| `tripleProduct_sq_unit`  (Gram for unit vectors)                    | proved |
| `dual_law_of_cosines_polynomial`  (cleared algebraic identity K)    | proved |
| `dual_spherical_law_of_cosines`  (angle γ; main theorem)            | proved |
| `dual_spherical_law_of_cosines_A`  (angle α)                        | proved |
| `dual_spherical_law_of_cosines_B`  (angle β)                        | proved |

Sorries: 0
Axioms:  0 (beyond Lean's foundational propext/Classical.choice/Quot.sound)
-/

end SphericalLawOfSines
