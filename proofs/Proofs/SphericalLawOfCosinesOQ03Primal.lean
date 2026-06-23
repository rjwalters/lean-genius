/-
Spherical Law of Cosines — primal trig completion (OQ-03 side work)

The parent file `Proofs.SphericalLawOfCosines` defines the dihedral angle
`SphericalTriangle.angleC` (Part IV) and proves the *algebraic* law of cosines

  cos c = cos a · cos b + ⟨proj⊥(A,C), proj⊥(B,C)⟩

(`spherical_law_of_cosines_algebraic` / `spherical_law_of_cosines_trig`,
SphericalLawOfCosines.lean:249,262). It stops at the inner product of the two
perpendicular projections and never identifies it with `sin a · sin b · cos C`,
so the textbook headline form

  cos c = cos a · cos b + sin a · sin b · cos C

is not actually closed in the parent — even though `angleC` is defined there.

This file closes that gap for the non-degenerate case, reusing only parent
lemmas plus standard Mathlib inner-product facts (Cauchy–Schwarz, `cos_arccos`).
It is the primal counterpart of the *dual* law in
`Proofs.SphericalLawOfCosinesOQ03` (this OQ): both are needed for a complete
treatment of the spherical cosine laws.

Verified numerically over 3·10⁵ random unit-vector triangles
(`research/problems/spherical-law-of-cosines-oq-03/verify_primal_completion.py`,
max error ≤ 6.2·10⁻¹⁶; Cauchy–Schwarz precondition `|⟨projA,projB⟩| ≤
‖projA‖·‖projB‖` holds exactly).

Build status: PENDING (authored during a Docker + Aristotle backend outage).
Left UNREGISTERED (not added to `Proofs.lean`) so it cannot affect the gallery
aggregate build until a backend can machine-check it.
-/

import Mathlib
import Proofs.SphericalLawOfCosines

open Real
open scoped RealInnerProductSpace

namespace SphericalLawOfCosinesOQ03Primal

open SphericalLawOfCosines

/-- For a non-degenerate spherical triangle (both perpendicular projections
nonzero), the cosine of the dihedral angle `C` is the normalized inner product
of the projections. This is just unfolding `angleC` and applying `cos_arccos`,
whose `[-1,1]` precondition is Cauchy–Schwarz. -/
theorem cos_angleC_eq (t : SphericalTriangle)
    (hA : ‖projectPerp t.A t.C‖ ≠ 0) (hB : ‖projectPerp t.B t.C‖ ≠ 0) :
    Real.cos t.angleC
      = (@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C))
          / (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖) := by
  have hden : 0 < ‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖ :=
    mul_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA))
            (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB))
  -- Cauchy–Schwarz: the normalized inner product lies in [-1, 1].
  have hcs : |(@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C))|
      ≤ ‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖ :=
    abs_real_inner_le_norm _ _
  have habs : |(@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C))
      / (‖projectPerp t.A t.C‖ * ‖projectPerp t.B t.C‖)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden]
    exact (div_le_one hden).mpr hcs
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  simp only [SphericalTriangle.angleC]
  rw [dif_neg (by push_neg; exact ⟨hA, hB⟩)]
  exact Real.cos_arccos hlo hhi

/-- The inner product of the perpendicular projections equals
`sin a · sin b · cos C`. This is the identity the parent file leaves implicit;
it follows by clearing the denominator in `cos_angleC_eq` using
`‖proj⊥(B,C)‖ = sin a` and `‖proj⊥(A,C)‖ = sin b`. -/
theorem inner_proj_eq_sin_mul_sin_mul_cos (t : SphericalTriangle)
    (hA : ‖projectPerp t.A t.C‖ ≠ 0) (hB : ‖projectPerp t.B t.C‖ ≠ 0) :
    (@inner ℝ Vec3 _ (projectPerp t.A t.C) (projectPerp t.B t.C))
      = Real.sin t.sideA * Real.sin t.sideB * Real.cos t.angleC := by
  -- sideA = arc(B,C), sideB = arc(A,C); their sines are the projection norms.
  have hsA : Real.sin t.sideA = ‖projectPerp t.B t.C‖ :=
    (norm_projectPerp_eq_sin t.B t.C t.hB t.hC).symm
  have hsB : Real.sin t.sideB = ‖projectPerp t.A t.C‖ :=
    (norm_projectPerp_eq_sin t.A t.C t.hA t.hC).symm
  rw [hsA, hsB, cos_angleC_eq t hA hB]
  field_simp

/-- **Spherical law of cosines, complete trig form** (non-degenerate case).

For a spherical triangle with arc-length sides `a = sideA`, `b = sideB`,
`c = sideC` and dihedral angle `C = angleC` opposite side `c`:

  cos c = cos a · cos b + sin a · sin b · cos C.

This is the parent's `spherical_law_of_cosines_trig` with the projection inner
product replaced by `sin a · sin b · cos C`, finally matching the headline
statement in the parent file's module docstring. -/
theorem spherical_law_of_cosines_trig_complete (t : SphericalTriangle)
    (hA : ‖projectPerp t.A t.C‖ ≠ 0) (hB : ‖projectPerp t.B t.C‖ ≠ 0) :
    Real.cos t.sideC
      = Real.cos t.sideA * Real.cos t.sideB
        + Real.sin t.sideA * Real.sin t.sideB * Real.cos t.angleC := by
  rw [spherical_law_of_cosines_trig t, inner_proj_eq_sin_mul_sin_mul_cos t hA hB]
  ring

end SphericalLawOfCosinesOQ03Primal
