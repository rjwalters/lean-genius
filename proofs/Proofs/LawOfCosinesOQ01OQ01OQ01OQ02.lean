/-
  Spherical Law of Sines, angle-over-side form — DIRECT from Gram symmetry
  (law-of-cosines-oq-01-oq-01-oq-01-oq-02)

  Open Question from law-of-cosines-oq-01-oq-01-oq-01 (Spherical Law of Sines):
  "Derive the angle-over-side form directly without going through the side-over-angle
  form, as an exercise in the symmetry of the Gram determinant."

  ## Answer

  The angle-over-side ratio identity

    sin(A)/sin(a) = sin(B)/sin(b) = sin(C)/sin(c)

  is obtained *directly* from the three cyclic Gram-determinant identities

    sin²(A)·sin²(b)·sin²(c) = G,   sin²(B)·sin²(a)·sin²(c) = G,   sin²(C)·sin²(a)·sin²(b) = G,

  where G = 1 - cos²a - cos²b - cos²c + 2·cos(a)·cos(b)·cos(c) is the (vertex-symmetric)
  Gram determinant of the perpendicular projections. Equating any two of the three
  identities and cancelling the *shared* side-sine immediately yields the corresponding
  cross-product `sin(angle)·sin(opposite side) = ...`, hence the ratio equality after a
  single `div_eq_div_iff` inversion.

  ## What is new here (vs. law-of-cosines-oq-01-oq-01-oq-01)

  The parent file derives the angle-over-side form *algebraically from the side-over-angle
  RATIO form* `spherical_law_of_sines_all` (which is itself built by a vertex permutation
  for its third ratio). This file instead:

  * completes the cyclic family of symmetric Gram identities with the previously-missing
    third member `sinC_sq_times_ab` (sin²(C)·sin²(a)·sin²(b) = G), built from the
    angle-C law of cosines `cos_C_mul`, mirroring the existing `sinA_sq_times_bc` /
    `sinB_sq_times_ac`;
  * reads the angle-over-side cross-products straight off the *symmetry* of the Gram
    determinant — the A/C relation from `sinC_sq_times_ab` and the B/C relation by
    transitivity — *without* ever forming the side-over-angle ratio form and *without*
    the permutation detour used for the third ratio there.

  ## Axiom count: 0
  ## Sorry count: 0
-/

import Proofs.LawOfCosinesOQ01OQ02
import Proofs.LawOfCosinesOQ01OQ01

open SphericalLawOfCosines Real

-- Extend the LawOfCosinesOQ01OQ02 namespace to reuse `gramDet`, the symmetric identities
-- `sinA_sq_times_bc` / `sinB_sq_times_ac`, the multiplicative law of sines, and the
-- angle-sine nonnegativity lemmas without qualification.
namespace LawOfCosinesOQ01OQ02

/-- sin(angleC) ≥ 0 since angleC ∈ [0, π] (mirrors `sin_angleA_nonneg`/`sin_angleB_nonneg`). -/
lemma sin_angleC_nonneg (t : SphericalTriangle) : 0 ≤ Real.sin t.angleC := by
  simp only [SphericalTriangle.angleC]
  split_ifs
  · simp
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)

/-- **Third symmetric Gram identity**: sin²(C)·sin²(a)·sin²(b) = gramDet.

    The cyclic completion of `sinA_sq_times_bc` and `sinB_sq_times_ac`. Follows by
    substituting the angle-C law of cosines `cos(C) = (cos c - cos a·cos b)/(sin a·sin b)`
    (from `cos_C_mul`) into `sin²(C) = 1 - cos²(C)` and clearing denominators against the
    expanded Gram determinant. -/
lemma sinC_sq_times_ab (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) :
    Real.sin t.angleC ^ 2 * (Real.sin t.sideA ^ 2 * Real.sin t.sideB ^ 2) =
    gramDet t := by
  have hcC : Real.cos t.angleC =
      (Real.cos t.sideC - Real.cos t.sideA * Real.cos t.sideB) /
      (Real.sin t.sideA * Real.sin t.sideB) := by
    rw [eq_div_iff (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb))]
    linear_combination DualSphericalLawOfCosines.cos_C_mul t ha hb
  have hsin_sq : Real.sin t.angleC ^ 2 = 1 - Real.cos t.angleC ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t.angleC]
  rw [hsin_sq, hcC, gramDet_expand]
  have hab : Real.sin t.sideA * Real.sin t.sideB ≠ 0 :=
    mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
  field_simp
  simp only [Real.sin_sq]
  ring

/-- **Angle-over-side cross-product, A/C** (direct from Gram symmetry):
    sin(a)·sin(C) = sin(c)·sin(A).

    Equate `sinA_sq_times_bc` (sin²A·sin²b·sin²c = G) and `sinC_sq_times_ab`
    (sin²C·sin²a·sin²b = G), cancel the shared `sin²(b) > 0` to get
    sin²A·sin²c = sin²C·sin²a, then take positive square roots (both products are
    nonnegative). Mirrors `spherical_law_of_sines_mul` for the A/C vertex pair. -/
theorem sines_mul_AC (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC) :
    Real.sin t.sideA * Real.sin t.angleC =
    Real.sin t.sideC * Real.sin t.angleA := by
  have hA_nn := sin_angleA_nonneg t
  have hC_nn := sin_angleC_nonneg t
  have hA := sinA_sq_times_bc t hb hc
  have hC := sinC_sq_times_ab t ha hb
  -- Cancel sin²b to get sin²A·sin²c = sin²C·sin²a
  have h_sq_eq : Real.sin t.angleA ^ 2 * Real.sin t.sideC ^ 2 =
      Real.sin t.angleC ^ 2 * Real.sin t.sideA ^ 2 := by
    have hb_pos : 0 < Real.sin t.sideB ^ 2 := pow_pos hb 2
    nlinarith
  -- sin(A)·sin(c) = sin(C)·sin(a) from squared equality + nonnegativity
  nlinarith [sq_nonneg (Real.sin t.angleA * Real.sin t.sideC - Real.sin t.angleC * Real.sin t.sideA),
             sq_nonneg (Real.sin t.angleA * Real.sin t.sideC + Real.sin t.angleC * Real.sin t.sideA),
             mul_nonneg hA_nn hc.le, mul_nonneg hC_nn ha.le]

/-- **Spherical Law of Sines (angle-over-side form), derived directly from the symmetry
    of the Gram determinant.**

      sin(A)/sin(a) = sin(B)/sin(b)   ∧   sin(A)/sin(a) = sin(C)/sin(c).

    The A/B equality uses the symmetric multiplicative law of sines
    `spherical_law_of_sines_mul` (proved in `law-of-cosines-oq-01-oq-02` from
    `sinA_sq_times_bc`/`sinB_sq_times_ac`); the A/C equality uses `sines_mul_AC` above.
    Neither cross-product is read off the side-over-angle ratio form
    `spherical_law_of_sines_all`. -/
theorem spherical_law_of_sines_angle_over_side_direct (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA) (hB : 0 < Real.sin t.angleB) (hC : 0 < Real.sin t.angleC) :
    Real.sin t.angleA / Real.sin t.sideA = Real.sin t.angleB / Real.sin t.sideB ∧
    Real.sin t.angleA / Real.sin t.sideA = Real.sin t.angleC / Real.sin t.sideC := by
  refine ⟨?_, ?_⟩
  · -- A/a = B/b  ⟺  sin(A)·sin(b) = sin(B)·sin(a)
    rw [div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)]
    linear_combination -(spherical_law_of_sines_mul t ha hb hc)
  · -- A/a = C/c  ⟺  sin(A)·sin(c) = sin(C)·sin(a)
    rw [div_eq_div_iff (ne_of_gt ha) (ne_of_gt hc)]
    linear_combination -(sines_mul_AC t ha hb hc)

/-- The B/b = C/c part of the angle-over-side law, by transitivity. -/
theorem spherical_law_of_sines_BC_angle_over_side_direct (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA) (hB : 0 < Real.sin t.angleB) (hC : 0 < Real.sin t.angleC) :
    Real.sin t.angleB / Real.sin t.sideB = Real.sin t.angleC / Real.sin t.sideC := by
  obtain ⟨h1, h2⟩ := spherical_law_of_sines_angle_over_side_direct t ha hb hc hA hB hC
  exact h1.symm.trans h2

end LawOfCosinesOQ01OQ02
