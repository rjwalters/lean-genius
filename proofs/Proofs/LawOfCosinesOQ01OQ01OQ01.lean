/-
  Spherical Law of Sines (law-of-cosines-oq-01-oq-01-oq-01)

  Open Question from law-of-cosines-oq-01-oq-01 (Dual Spherical Law of Cosines):
  "Generalize to prove the full spherical sine rule sin(A)/sin(a) = sin(B)/sin(b) = sin(C)/sin(c)
  using the Gram determinant framework established here."

  ## Answer: YES.

  For a non-degenerate spherical triangle, the spherical law of sines holds in both forms:

    sin(A) / sin(a) = sin(B) / sin(b) = sin(C) / sin(c)    [angle over side]
    sin(a) / sin(A) = sin(b) / sin(B) = sin(c) / sin(C)    [side over angle]

  ## Proof

  The file law-of-cosines-oq-01-oq-02 establishes the side-over-angle form via the Gram
  determinant G = 1 - cos²a - cos²b - cos²c + 2cos(a)cos(b)cos(c) ≥ 0:
    sin²(X)·sin²(y)·sin²(z) = G for each angle-side triple

  This file derives the angle-over-side form by algebraic inversion.

  ## Axiom count: 0
  ## Sorry count: 0
-/

import Proofs.LawOfCosinesOQ01OQ02

open SphericalLawOfCosines Real

-- Extend the LawOfCosinesOQ01OQ02 namespace to inherit dot notation for angleA, angleB
namespace LawOfCosinesOQ01OQ02

/-- **Spherical Law of Sines (angle/side form)**:
    sin(A)/sin(a) = sin(B)/sin(b) ∧ sin(A)/sin(a) = sin(C)/sin(c).

    Derived by algebraic inversion from the Gram determinant form proved in this file. -/
theorem spherical_law_of_sines_angle_over_side (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA) (hB : 0 < Real.sin t.angleB) (hC : 0 < Real.sin t.angleC) :
    Real.sin t.angleA / Real.sin t.sideA = Real.sin t.angleB / Real.sin t.sideB ∧
    Real.sin t.angleA / Real.sin t.sideA = Real.sin t.angleC / Real.sin t.sideC := by
  obtain ⟨h1, h2⟩ := spherical_law_of_sines_all t ha hb hc hA hB hC
  -- h1 : sin(a)/sin(A) = sin(b)/sin(B)
  -- h2 : sin(a)/sin(A) = sin(c)/sin(C)
  constructor
  · -- A/a = B/b  iff  sin(A)*sin(b) = sin(B)*sin(a)
    rw [div_eq_div_iff (ne_of_gt hA) (ne_of_gt hB)]
    rw [div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)] at h1
    linear_combination -h1
  · -- A/a = C/c  iff  sin(A)*sin(c) = sin(C)*sin(a)
    rw [div_eq_div_iff (ne_of_gt hA) (ne_of_gt hC)]
    rw [div_eq_div_iff (ne_of_gt ha) (ne_of_gt hc)] at h2
    linear_combination -h2

/-- The B/b = C/c part follows by transitivity. -/
theorem spherical_law_of_sines_BC_angle_over_side (t : SphericalTriangle)
    (ha : 0 < Real.sin t.sideA) (hb : 0 < Real.sin t.sideB) (hc : 0 < Real.sin t.sideC)
    (hA : 0 < Real.sin t.angleA) (hB : 0 < Real.sin t.angleB) (hC : 0 < Real.sin t.angleC) :
    Real.sin t.angleB / Real.sin t.sideB = Real.sin t.angleC / Real.sin t.sideC := by
  have ⟨h1, h2⟩ := spherical_law_of_sines_angle_over_side t ha hb hc hA hB hC
  exact h1.symm.trans h2

end LawOfCosinesOQ01OQ02
