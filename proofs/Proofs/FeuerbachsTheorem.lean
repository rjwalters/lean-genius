import Proofs.FeuerbachsTheoremOQ01

/-
# Feuerbach's Theorem - Complete Assembly

Feuerbach's Theorem (Wiedijk's #29): The nine-point circle of a triangle is tangent to
the incircle and all three excircles.

This file assembles the complete theorem from:
- **FeuerbachsTheoremDefs.lean**: Definitions, nine-point circle infrastructure, numerical verification
- **FeuerbachsTheoremOQ01.lean**: Proofs of all four Feuerbach distance relations via coordinate computation

## Status: FULLY PROVED (0 axioms, 0 sorries)
All four Feuerbach distance relations are proved by direct coordinate computation.
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheorem

open FeuerbachsTheoremOQ01

-- ============================================================
-- PART 7: Feuerbach's Theorem - Key Distance Relations (PROVED)
-- ============================================================

/-- **Key Distance Relation for Feuerbach's Theorem**

    The distance from the nine-point center N to the incenter I equals |R/2 - r|
    where R is the circumradius and r is the inradius.

    This is the core relation that establishes internal tangency with the incircle.
    Proved by direct coordinate computation in FeuerbachsTheoremOQ01. -/
theorem feuerbach_incircle_distance (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius) :=
  feuerbach_incircle_distance_proved T

/-- The distance from nine-point center to excenter I_a equals R/2 + r_a.
    Proved by direct coordinate computation. -/
theorem feuerbach_excircle_a_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_a = T.ninePointRadius + T.exradius_a :=
  feuerbach_excircle_a_distance_proved T

/-- The distance from nine-point center to excenter I_b equals R/2 + r_b.
    Proved by direct coordinate computation. -/
theorem feuerbach_excircle_b_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_b = T.ninePointRadius + T.exradius_b :=
  feuerbach_excircle_b_distance_proved T

/-- The distance from nine-point center to excenter I_c equals R/2 + r_c.
    Proved by direct coordinate computation. -/
theorem feuerbach_excircle_c_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_c = T.ninePointRadius + T.exradius_c :=
  feuerbach_excircle_c_distance_proved T

-- ============================================================
-- PART 9: Feuerbach's Theorem - Main Results
-- ============================================================

/-- **Feuerbach's Theorem, Part 1: Incircle Tangency**

    The nine-point circle is internally tangent to the incircle.

    **Proof sketch:**
    1. The nine-point center N is at distance |R/2 - r| from the incenter I
       (by `feuerbach_incircle_distance`)
    2. The nine-point radius is R/2, the inradius is r
    3. Distance between centers = |r₁ - r₂| ⟹ internal tangency

    The tangent point is called the Feuerbach point. -/
theorem feuerbach_incircle_tangent (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius) :=
  feuerbach_incircle_distance T

/-- **Feuerbach's Theorem, Part 2: Excircle A Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex A. -/
theorem feuerbach_excircle_a_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_a T.ninePointRadius T.exradius_a :=
  feuerbach_excircle_a_distance T

/-- **Feuerbach's Theorem, Part 2b: Excircle B Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex B. -/
theorem feuerbach_excircle_b_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_b T.ninePointRadius T.exradius_b :=
  feuerbach_excircle_b_distance T

/-- **Feuerbach's Theorem, Part 2c: Excircle C Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex C. -/
theorem feuerbach_excircle_c_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_c T.ninePointRadius T.exradius_c :=
  feuerbach_excircle_c_distance T

-- ============================================================
-- PART 10: The Complete Feuerbach's Theorem
-- ============================================================

/-- **Feuerbach's Theorem** (Wiedijk #29)

    The nine-point circle of any triangle is:
    1. Internally tangent to the incircle (distance = |R/2 - r|)
    2. Externally tangent to all three excircles (distance = R/2 + r_i)

    This remarkable theorem was discovered by Karl Wilhelm Feuerbach in 1822.
    The tangent point with the incircle is known as the Feuerbach point.

    FULLY PROVED: All four distance relations established by coordinate computation. -/
theorem feuerbachs_theorem (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius) ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_a T.ninePointRadius T.exradius_a ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_b T.ninePointRadius T.exradius_b ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_c T.ninePointRadius T.exradius_c :=
  ⟨feuerbach_incircle_tangent T,
   feuerbach_excircle_a_tangent T,
   feuerbach_excircle_b_tangent T,
   feuerbach_excircle_c_tangent T⟩

-- ============================================================
-- PART 11: Special Case - Equilateral Triangle
-- ============================================================

/-- For an equilateral triangle with side s, R = 2r (circumradius = 2 × inradius).
    Proved by coordinate computation in FeuerbachsTheoremOQ01. -/
theorem equilateral_R_eq_2r (s : ℝ) (hs : s > 0) :
    let T : Triangle := {
      A := (0, 0)
      B := (s, 0)
      C := (s/2, s * Real.sqrt 3 / 2)
      nondegenerate := by
        intro heq
        have : s * (s * Real.sqrt 3 / 2) > 0 := by positivity
        nlinarith
    }
    T.circumradius = 2 * T.inradius :=
  equilateral_R_eq_2r_proved s hs

/-- For an equilateral triangle, the circumradius R = 2r where r is the inradius.
    This means R/2 = r, so the nine-point circle has the same radius as the incircle. -/
theorem equilateral_circumradius_inradius_relation (s : ℝ) (hs : s > 0) :
    let T : Triangle := {
      A := (0, 0)
      B := (s, 0)
      C := (s/2, s * Real.sqrt 3 / 2)
      nondegenerate := by
        intro heq
        have : s * (s * Real.sqrt 3 / 2) > 0 := by positivity
        nlinarith
    }
    T.circumradius = 2 * T.inradius := equilateral_R_eq_2r s hs

-- Export main results
#check @feuerbachs_theorem
#check @feuerbach_incircle_tangent
#check @feuerbach_excircle_a_tangent
#check @ninePointRadius_eq_half_circumradius
#check @euler_line_relation

end FeuerbachsTheorem

end
