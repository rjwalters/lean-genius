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
import Proofs.FeuerbachsTheorem

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ01Aristotle

open Real FeuerbachsTheorem

-- ============================================================
-- CIRCUMCENTER EQUIDISTANCE
-- ============================================================

-- Helper: the perpendicular bisector condition for AB
private lemma perp_bisector_AB (T : Triangle) :
    (T.B.1 - T.A.1) * (T.B.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.B.2 - T.A.2) * (T.B.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := by intro h; apply T.nondegenerate; nlinarith
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]; field_simp [hd_ne]; ring

-- Helper: the perpendicular bisector condition for AC
private lemma perp_bisector_AC (T : Triangle) :
    (T.C.1 - T.A.1) * (T.C.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.C.2 - T.A.2) * (T.C.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := by intro h; apply T.nondegenerate; nlinarith
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]; field_simp [hd_ne]; ring

-- Helper: two nonneg reals with equal squares are equal
private lemma eq_of_sq_eq_nonneg' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with hab | hab
  · linarith
  · linarith

/-- The circumcenter is equidistant from all three vertices (B).
    dist2(O, B) = dist2(O, A) = R -/
theorem circumcenter_equidist_B (T : Triangle) :
    dist2 T.circumcenter T.B = dist2 T.circumcenter T.A := by
  apply eq_of_sq_eq_nonneg' (by unfold dist2; exact Real.sqrt_nonneg _)
    (by unfold dist2; exact Real.sqrt_nonneg _)
  unfold dist2
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have h := perp_bisector_AB T
  nlinarith [sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.B.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- The circumcenter is equidistant from all three vertices (C).
    dist2(O, C) = dist2(O, A) = R -/
theorem circumcenter_equidist_C (T : Triangle) :
    dist2 T.circumcenter T.C = dist2 T.circumcenter T.A := by
  apply eq_of_sq_eq_nonneg' (by unfold dist2; exact Real.sqrt_nonneg _)
    (by unfold dist2; exact Real.sqrt_nonneg _)
  unfold dist2
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have h := perp_bisector_AC T
  nlinarith [sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.C.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

-- ============================================================
-- SIDE LENGTH POSITIVITY
-- ============================================================

/-- Side a = |BC| > 0 for nondegenerate triangles. -/
theorem side_a_pos (T : Triangle) : T.side_a > 0 := by
  unfold Triangle.side_a
  apply Real.sqrt_pos_of_pos
  by_contra h; push_neg at h
  have hx : T.C.1 = T.B.1 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  have hy : T.C.2 = T.B.2 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  exact T.nondegenerate (by rw [hx, hy]; ring)

/-- Side b = |CA| > 0 for nondegenerate triangles. -/
theorem side_b_pos (T : Triangle) : T.side_b > 0 := by
  unfold Triangle.side_b
  apply Real.sqrt_pos_of_pos
  by_contra h; push_neg at h
  have hx : T.A.1 = T.C.1 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  have hy : T.A.2 = T.C.2 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  exact T.nondegenerate (by rw [hx, hy]; ring)

/-- Side c = |AB| > 0 for nondegenerate triangles. -/
theorem side_c_pos (T : Triangle) : T.side_c > 0 := by
  unfold Triangle.side_c
  apply Real.sqrt_pos_of_pos
  by_contra h; push_neg at h
  have hx : T.B.1 = T.A.1 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  have hy : T.B.2 = T.A.2 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  exact T.nondegenerate (by rw [hx, hy]; ring)

-- ============================================================
-- SQUARED SIDE LENGTHS
-- ============================================================

/-- side_a² equals the sum of squared coordinate differences. -/
theorem side_a_sq (T : Triangle) :
    T.side_a ^ 2 = (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 := by
  unfold Triangle.side_a
  rw [Real.sq_sqrt (by positivity)]

/-- side_b² equals the sum of squared coordinate differences. -/
theorem side_b_sq (T : Triangle) :
    T.side_b ^ 2 = (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 := by
  unfold Triangle.side_b
  rw [Real.sq_sqrt (by positivity)]

/-- side_c² equals the sum of squared coordinate differences. -/
theorem side_c_sq (T : Triangle) :
    T.side_c ^ 2 = (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 := by
  unfold Triangle.side_c
  rw [Real.sq_sqrt (by positivity)]

-- ============================================================
-- DIST2 PROPERTIES
-- ============================================================

/-- dist2 is symmetric. -/
theorem dist2_comm (P Q : Point) : dist2 P Q = dist2 Q P := by
  unfold dist2
  congr 1
  nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2 - P.2),
             sq_nonneg (P.1 - Q.1), sq_nonneg (P.2 - Q.2)]

/-- dist2(P, P) = 0 -/
theorem dist2_self (P : Point) : dist2 P P = 0 := by
  unfold dist2; simp [sub_self]

/-- dist2 is nonneg. -/
theorem dist2_nonneg_gen (P Q : Point) : 0 ≤ dist2 P Q := by
  unfold dist2; exact Real.sqrt_nonneg _

-- ============================================================
-- CIRCUMRADIUS POSITIVITY
-- ============================================================

/-- The circumradius R > 0 for nondegenerate triangles. -/
theorem circumradius_pos (T : Triangle) : T.circumradius > 0 := by
  unfold Triangle.circumradius dist2
  apply Real.sqrt_pos_of_pos
  have h := perp_bisector_AB T
  by_contra hle; push_neg at hle
  have hx : T.circumcenter.1 = T.A.1 := by
    nlinarith [sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]
  have hy : T.circumcenter.2 = T.A.2 := by
    nlinarith [sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]
  -- Substitute O = A into perpendicular bisector: (B-A)^2 = 0
  rw [hx, hy] at h
  have hbx : T.B.1 = T.A.1 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  have hby : T.B.2 = T.A.2 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  exact T.nondegenerate (by rw [hbx, hby]; ring)

/-- The nine-point radius R/2 > 0 for nondegenerate triangles. -/
theorem ninePointRadius_pos (T : Triangle) : T.ninePointRadius > 0 := by
  unfold Triangle.ninePointRadius
  exact div_pos (circumradius_pos T) (by norm_num)

-- ============================================================
-- ORTHOCENTER RELATION
-- ============================================================

/-- H = A + B + C - 2O (orthocenter via circumcenter). -/
theorem orthocenter_formula (T : Triangle) :
    T.orthocenter = (T.A.1 + T.B.1 + T.C.1 - 2 * T.circumcenter.1,
                     T.A.2 + T.B.2 + T.C.2 - 2 * T.circumcenter.2) := by
  unfold Triangle.orthocenter
  exact Prod.ext (by ring) (by ring)

-- ============================================================
-- NINE-POINT CENTER PROPERTIES
-- ============================================================

/-- N = (O + H) / 2 -/
theorem ninePointCenter_midpoint (T : Triangle) :
    T.ninePointCenter = pointMidpoint T.circumcenter T.orthocenter := by
  unfold Triangle.ninePointCenter pointMidpoint
  exact Prod.ext (by ring) (by ring)

/-- N_x = (A_x + B_x + C_x - O_x) / 2, N_y = (A_y + B_y + C_y - O_y) / 2 -/
theorem ninePointCenter_coords (T : Triangle) :
    T.ninePointCenter.1 = (T.A.1 + T.B.1 + T.C.1 - T.circumcenter.1) / 2 ∧
    T.ninePointCenter.2 = (T.A.2 + T.B.2 + T.C.2 - T.circumcenter.2) / 2 := by
  unfold Triangle.ninePointCenter pointMidpoint Triangle.orthocenter
  exact ⟨by dsimp; ring, by dsimp; ring⟩

end FeuerbachsTheoremOQ01Aristotle

end
