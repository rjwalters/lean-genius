/-
  Aristotle targets for Feuerbach's Theorem OQ-01
  Routine supporting lemmas for automated proof search.
  See FeuerbachsTheoremOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open Feuerbach distance axioms
  - Known results likely provable from Mathlib
  - Clean theorem statements with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ01Aristotle

open Real FeuerbachsTheorem

-- ============================================================
-- CIRCUMCENTER EQUIDISTANCE
-- ============================================================

/-- The circumcenter is equidistant from all three vertices (B).
    dist2(O, B) = dist2(O, A) = R -/
theorem circumcenter_equidist_B (T : Triangle) :
    dist2 T.circumcenter T.B = dist2 T.circumcenter T.A := by sorry

/-- The circumcenter is equidistant from all three vertices (C).
    dist2(O, C) = dist2(O, A) = R -/
theorem circumcenter_equidist_C (T : Triangle) :
    dist2 T.circumcenter T.C = dist2 T.circumcenter T.A := by sorry

-- ============================================================
-- SIDE LENGTH POSITIVITY
-- ============================================================

/-- Side a = |BC| > 0 for nondegenerate triangles. -/
theorem side_a_pos (T : Triangle) : T.side_a > 0 := by sorry

/-- Side b = |CA| > 0 for nondegenerate triangles. -/
theorem side_b_pos (T : Triangle) : T.side_b > 0 := by sorry

/-- Side c = |AB| > 0 for nondegenerate triangles. -/
theorem side_c_pos (T : Triangle) : T.side_c > 0 := by sorry

-- ============================================================
-- SQUARED SIDE LENGTHS
-- ============================================================

/-- side_a² equals the sum of squared coordinate differences. -/
theorem side_a_sq (T : Triangle) :
    T.side_a ^ 2 = (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 := by
  simp only [Triangle.side_a]; exact sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- side_b² equals the sum of squared coordinate differences. -/
theorem side_b_sq (T : Triangle) :
    T.side_b ^ 2 = (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 := by
  simp only [Triangle.side_b]; exact sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- side_c² equals the sum of squared coordinate differences. -/
theorem side_c_sq (T : Triangle) :
    T.side_c ^ 2 = (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 := by
  simp only [Triangle.side_c]; exact sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

-- ============================================================
-- DIST2 PROPERTIES
-- ============================================================

/-- dist2 is symmetric. -/
theorem dist2_comm (P Q : Point) : dist2 P Q = dist2 Q P := by
  simp only [dist2]; congr 1; ring

/-- dist2(P, P) = 0 -/
theorem dist2_self (P : Point) : dist2 P P = 0 := by
  simp [dist2]

/-- dist2 is nonneg. -/
theorem dist2_nonneg_gen (P Q : Point) : 0 ≤ dist2 P Q :=
  sqrt_nonneg _

-- ============================================================
-- CIRCUMRADIUS POSITIVITY
-- ============================================================

/-- The circumradius R > 0 for nondegenerate triangles. -/
theorem circumradius_pos (T : Triangle) : T.circumradius > 0 := by sorry

/-- The nine-point radius R/2 > 0 for nondegenerate triangles. -/
theorem ninePointRadius_pos (T : Triangle) : T.ninePointRadius > 0 := by
  simp only [Triangle.ninePointRadius]; exact div_pos (circumradius_pos T) (by norm_num)

-- ============================================================
-- ORTHOCENTER RELATION
-- ============================================================

/-- H = A + B + C - 2O (orthocenter via circumcenter). -/
theorem orthocenter_formula (T : Triangle) :
    T.orthocenter = (T.A.1 + T.B.1 + T.C.1 - 2 * T.circumcenter.1,
                     T.A.2 + T.B.2 + T.C.2 - 2 * T.circumcenter.2) := by
  simp [Triangle.orthocenter]

-- ============================================================
-- NINE-POINT CENTER PROPERTIES
-- ============================================================

/-- N = (O + H) / 2 -/
theorem ninePointCenter_midpoint (T : Triangle) :
    T.ninePointCenter = pointMidpoint T.circumcenter T.orthocenter := by
  simp [Triangle.ninePointCenter, pointMidpoint, Triangle.orthocenter]
  constructor <;> ring

/-- N_x = (A_x + B_x + C_x) / 2 - O_x / 2.
    Actually N = (O + H)/2 = (O + A+B+C-2O)/2 = (A+B+C-O)/2
    so N_x = (A_x + B_x + C_x - O_x) / 2 -/
theorem ninePointCenter_coords (T : Triangle) :
    T.ninePointCenter.1 = (T.A.1 + T.B.1 + T.C.1 - T.circumcenter.1) / 2 ∧
    T.ninePointCenter.2 = (T.A.2 + T.B.2 + T.C.2 - T.circumcenter.2) / 2 := by
  simp [Triangle.ninePointCenter, pointMidpoint, Triangle.orthocenter]
  constructor <;> ring

end FeuerbachsTheoremOQ01Aristotle

end
