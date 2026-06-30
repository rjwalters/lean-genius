/-
  Feuerbach's Theorem DefsOQ02OQ01OQ01OQ01OQ01:
  The excentral triangle has circumradius 2R and circumcenter 2O − I.

  ## The Open Question

  The sibling file `FeuerbachsTheoremDefsOQ02OQ01OQ01` proves the *affine*
  relation among the four classical tritangent centres — the incentre I and the
  three excentres I_a, I_b, I_c — namely that the circumcentre O is their
  centroid,

      I + I_a + I_b + I_c = 4·O.

  That entry's first open question asks to prove *directly* the classical fact it
  only cites: that **the excentral triangle I_a I_b I_c has circumradius 2R**,
  twice the circumradius of the original triangle ABC, completing the
  orthocentric-system picture whose nine-point centre the centroid identity
  locates at O.  This file answers it.

  ## What This File Proves

  For an arbitrary non-degenerate triangle T, write O for the circumcentre, I for
  the incentre, and define the **excentral circumcentre**

      O' := 2·O − I        (`Triangle.excentralCircumcenter`).

  ### The circumradius of the excentral triangle is 2R
  `excentral_dist_a_sq`, `excentral_dist_b_sq`, `excentral_dist_c_sq` :
      dist²(O', I_a) = dist²(O', I_b) = dist²(O', I_c) = 4·R².
  Since one single point O' is equidistant (distance² = 4R²) from all three
  excentres, O' is the circumcentre of the excentral triangle and its
  circumradius is 2R.

  `excentral_circumradius_a/b/c` and `excentral_circumradius_eq_two_R` :
      dist(O', I_a) = dist(O', I_b) = dist(O', I_c) = 2·R   (the square-root form).

  ### The nine-point relation
  `circumcenter_is_excentral_ninePointCenter` :  O is the midpoint of I and O',
      O = ½(I + O').
  Together with `O' = 2O − I` being the excentral circumcentre and I the
  orthocentre of the excentral triangle, this is exactly the statement that O is
  the nine-point centre of the excentral triangle (whose nine-point circle is
  therefore the circumcircle of ABC, of radius R = ½·2R).

  ### Worked example
  `triangle_345_excentral_circumradius` :  for the 3-4-5 triangle, O = (3/2,2),
  I = (1,1), so O' = (2,3); and indeed dist²(O', I_a) = dist²(O', I_b) =
  dist²(O', I_c) = 25 = 4·(5/2)² = 4R², with I_a=(6,6), I_b=(−3,3), I_c=(2,−2).

  ## Method

  The clean algebraic heart is that  I_a + I − 2O,  cleared over the common
  denominator p_a·p_s = (−a+b+c)(a+b+c), is the O-shifted weighted vector
      2·[ −a²·(A−O) + b(b+c)·(B−O) + c(b+c)·(C−O) ].
  These weights w = (−a², b(b+c), c(b+c)) have the two miraculous properties
      w_a + w_b + w_c = p_a·p_s        and        w_a w_b c² + w_b w_c a² + w_c w_a b² = 0,
  both pure `ring` identities in the free side lengths.  Feeding them into the
  reusable master identity
      |w_a(A−O)+w_b(B−O)+w_c(C−O)|² = R²(w_a+w_b+w_c)² − (w_a w_b c²+w_b w_c a²+w_c w_a b²)
  collapses the right-hand side to exactly R²·(p_a p_s)², so
      dist²(O', I_a)·(p_a p_s)² = 4·R²·(p_a p_s)²,
  and cancelling the (nonzero) factor gives dist²(O', I_a) = 4R².  The b- and
  c-excentres are identical after the cyclic weight change
  (a(a+c), −b², c(a+c)) and (a(a+b), b(a+b), −c²).

  The squared-side, area- and side-positivity, strict-triangle-inequality
  (needed to keep p_a, p_b, p_c nonzero) and circumcentre-equidistance lemmas,
  and the master weighted-norm identity, are reproved locally, as the parent
  declares them `private`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachExcentralCircumradius

open FeuerbachsTheorem
open scoped Real

/-- The **excentral circumcentre** O' = 2·O − I, the reflection of the incentre
    in the circumcentre.  We prove it is the circumcentre of the excentral
    triangle I_a I_b I_c, at distance 2R from each excentre. -/
def _root_.FeuerbachsTheorem.Triangle.excentralCircumcenter (T : Triangle) : Point :=
  (2 * T.circumcenter.1 - T.incenter.1, 2 * T.circumcenter.2 - T.incenter.2)

-- ============================================================
-- PART 1: Circumcentre equidistance (parent's are private)
-- ============================================================

/-- Squared distance is non-negative. -/
private lemma dist2_sq_nonneg (P Q : Point) : 0 ≤ dist2_sq P Q := by
  unfold dist2_sq; positivity

set_option maxHeartbeats 6400000 in
/-- Perpendicular bisector of AB passes through the circumcentre (linear in O). -/
private lemma pb_AB (T : Triangle) :
    (T.B.1 - T.A.1) * (T.B.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.B.2 - T.A.2) * (T.B.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]
  field_simp [hd_ne]
  ring

set_option maxHeartbeats 6400000 in
/-- Perpendicular bisector of AC passes through the circumcentre. -/
private lemma pb_AC (T : Triangle) :
    (T.C.1 - T.A.1) * (T.C.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.C.2 - T.A.2) * (T.C.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]
  field_simp [hd_ne]
  ring

/-- |B − O|² = |A − O|² : circumcentre equidistant from A and B. -/
private lemma equidist_B (T : Triangle) :
    (T.B.1 - T.circumcenter.1) ^ 2 + (T.B.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := pb_AB T
  nlinarith [h, sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.B.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- |C − O|² = |A − O|² : circumcentre equidistant from A and C. -/
private lemma equidist_C (T : Triangle) :
    (T.C.1 - T.circumcenter.1) ^ 2 + (T.C.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := pb_AC T
  nlinarith [h, sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.C.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

-- ============================================================
-- PART 2: Side lengths (squared values and positivity)
-- ============================================================

private lemma side_a_sq (T : Triangle) :
    T.side_a ^ 2 = (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 := by
  unfold Triangle.side_a; rw [Real.sq_sqrt (by positivity)]

private lemma side_b_sq (T : Triangle) :
    T.side_b ^ 2 = (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 := by
  unfold Triangle.side_b; rw [Real.sq_sqrt (by positivity)]

private lemma side_c_sq (T : Triangle) :
    T.side_c ^ 2 = (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 := by
  unfold Triangle.side_c; rw [Real.sq_sqrt (by positivity)]

private lemma side_a_nonneg (T : Triangle) : 0 ≤ T.side_a := Real.sqrt_nonneg _
private lemma side_b_nonneg (T : Triangle) : 0 ≤ T.side_b := Real.sqrt_nonneg _
private lemma side_c_nonneg (T : Triangle) : 0 ≤ T.side_c := Real.sqrt_nonneg _

/-- The triangle area is positive (non-degeneracy). -/
private lemma area_pos (T : Triangle) : 0 < T.area := by
  unfold Triangle.area
  have hne := T.nondegenerate
  have h : 0 < |(T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)| :=
    abs_pos.mpr hne
  linarith

private lemma side_a_pos (T : Triangle) : 0 < T.side_a := by
  have hne := T.nondegenerate
  have h : 0 < (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 := by
    by_contra h
    push_neg at h
    have h0 : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 = 0 := le_antisymm h (by positivity)
    have hx : T.C.1 - T.B.1 = 0 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
    have hy : T.C.2 - T.B.2 = 0 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
    apply hne; linear_combination (T.B.1 - T.A.1) * hy - (T.B.2 - T.A.2) * hx
  unfold Triangle.side_a; exact Real.sqrt_pos.mpr h

private lemma side_b_pos (T : Triangle) : 0 < T.side_b := by
  have hne := T.nondegenerate
  have h : 0 < (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 := by
    by_contra h
    push_neg at h
    have h0 : (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 = 0 := le_antisymm h (by positivity)
    have hx : T.A.1 - T.C.1 = 0 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
    have hy : T.A.2 - T.C.2 = 0 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
    apply hne; linear_combination (T.B.2 - T.A.2) * hx - (T.B.1 - T.A.1) * hy
  unfold Triangle.side_b; exact Real.sqrt_pos.mpr h

private lemma side_c_pos (T : Triangle) : 0 < T.side_c := by
  have hne := T.nondegenerate
  have h : 0 < (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 := by
    by_contra h
    push_neg at h
    have h0 : (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 = 0 := le_antisymm h (by positivity)
    have hx : T.B.1 - T.A.1 = 0 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
    have hy : T.B.2 - T.A.2 = 0 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
    apply hne; linear_combination (T.C.2 - T.A.2) * hx - (T.C.1 - T.A.1) * hy
  unfold Triangle.side_c; exact Real.sqrt_pos.mpr h

private lemma perimeter_pos (T : Triangle) : 0 < T.side_a + T.side_b + T.side_c := by
  have := side_a_pos T; have := side_b_pos T; have := side_c_pos T; linarith

-- ============================================================
-- PART 3: The strict triangle inequality  a < b + c
-- ============================================================

set_option maxHeartbeats 1600000 in
private lemma strict_tri_ineq_a (T : Triangle) :
    T.side_a < T.side_b + T.side_c := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hapos := side_a_pos T
  have hbpos := side_b_pos T
  have hcpos := side_c_pos T
  set D := (T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2) with hDdef
  set P := (T.A.1 - T.C.1) * (T.B.1 - T.A.1) + (T.A.2 - T.C.2) * (T.B.2 - T.A.2) with hPdef
  have hDne : D ≠ 0 := T.nondegenerate
  have hD2 : 0 < D ^ 2 := by
    rcases hDne.lt_or_gt with h | h
    · nlinarith [h]
    · nlinarith [h]
  have hexp : T.side_a ^ 2 = T.side_b ^ 2 + T.side_c ^ 2 + 2 * P := by
    rw [ha, hb, hc, hPdef]; ring
  have hlag : T.side_b ^ 2 * T.side_c ^ 2 - P ^ 2 = D ^ 2 := by
    rw [hb, hc, hPdef, hDdef]; ring
  have hP2 : P ^ 2 < (T.side_b * T.side_c) ^ 2 := by nlinarith [hlag, hD2]
  have hbc : 0 < T.side_b * T.side_c := mul_pos hbpos hcpos
  have hPlt : P < T.side_b * T.side_c := by nlinarith [hP2, hbc]
  have hsum_pos : 0 < T.side_b + T.side_c := by linarith
  have hasq : T.side_a ^ 2 < (T.side_b + T.side_c) ^ 2 := by nlinarith [hexp, hPlt]
  nlinarith [hasq, hapos, hsum_pos]

set_option maxHeartbeats 1600000 in
private lemma strict_tri_ineq_b (T : Triangle) :
    T.side_b < T.side_a + T.side_c := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hapos := side_a_pos T
  have hbpos := side_b_pos T
  have hcpos := side_c_pos T
  set D := (T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2) with hDdef
  set P := (T.C.1 - T.B.1) * (T.B.1 - T.A.1) + (T.C.2 - T.B.2) * (T.B.2 - T.A.2) with hPdef
  have hDne : D ≠ 0 := T.nondegenerate
  have hD2 : 0 < D ^ 2 := by
    rcases hDne.lt_or_gt with h | h
    · nlinarith [h]
    · nlinarith [h]
  have hexp : T.side_b ^ 2 = T.side_a ^ 2 + T.side_c ^ 2 + 2 * P := by
    rw [ha, hb, hc, hPdef]; ring
  have hlag : T.side_a ^ 2 * T.side_c ^ 2 - P ^ 2 = D ^ 2 := by
    rw [ha, hc, hPdef, hDdef]; ring
  have hP2 : P ^ 2 < (T.side_a * T.side_c) ^ 2 := by nlinarith [hlag, hD2]
  have hac : 0 < T.side_a * T.side_c := mul_pos hapos hcpos
  have hPlt : P < T.side_a * T.side_c := by nlinarith [hP2, hac]
  have hsum_pos : 0 < T.side_a + T.side_c := by linarith
  have hbsq : T.side_b ^ 2 < (T.side_a + T.side_c) ^ 2 := by nlinarith [hexp, hPlt]
  nlinarith [hbsq, hbpos, hsum_pos]

set_option maxHeartbeats 1600000 in
private lemma strict_tri_ineq_c (T : Triangle) :
    T.side_c < T.side_a + T.side_b := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hapos := side_a_pos T
  have hbpos := side_b_pos T
  have hcpos := side_c_pos T
  set D := (T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2) with hDdef
  set P := (T.C.1 - T.A.1) * (T.B.1 - T.C.1) + (T.C.2 - T.A.2) * (T.B.2 - T.C.2) with hPdef
  have hDne : D ≠ 0 := T.nondegenerate
  have hD2 : 0 < D ^ 2 := by
    rcases hDne.lt_or_gt with h | h
    · nlinarith [h]
    · nlinarith [h]
  have hexp : T.side_c ^ 2 = T.side_a ^ 2 + T.side_b ^ 2 + 2 * P := by
    rw [ha, hb, hc, hPdef]; ring
  have hlag : T.side_a ^ 2 * T.side_b ^ 2 - P ^ 2 = D ^ 2 := by
    rw [ha, hb, hPdef, hDdef]; ring
  have hP2 : P ^ 2 < (T.side_a * T.side_b) ^ 2 := by nlinarith [hlag, hD2]
  have hab : 0 < T.side_a * T.side_b := mul_pos hapos hbpos
  have hPlt : P < T.side_a * T.side_b := by nlinarith [hP2, hab]
  have hsum_pos : 0 < T.side_a + T.side_b := by linarith
  have hcsq : T.side_c ^ 2 < (T.side_a + T.side_b) ^ 2 := by nlinarith [hexp, hPlt]
  nlinarith [hcsq, hcpos, hsum_pos]

/-- Excentre denominators are strictly positive. -/
private lemma pa_pos (T : Triangle) : 0 < -T.side_a + T.side_b + T.side_c := by
  have := strict_tri_ineq_a T; linarith

private lemma pb_pos (T : Triangle) : 0 < T.side_a - T.side_b + T.side_c := by
  have := strict_tri_ineq_b T; linarith

private lemma pc_pos (T : Triangle) : 0 < T.side_a + T.side_b - T.side_c := by
  have := strict_tri_ineq_c T; linarith

-- ============================================================
-- PART 4: The reusable weighted-norm identity
-- ============================================================

/-- Master algebraic identity.  With O the circumcentre and R² = |A − O|², the
    weighted vector  w_a(A−O) + w_b(B−O) + w_c(C−O)  has squared length
        R²·(w_a+w_b+w_c)² − (w_a w_b c² + w_b w_c a² + w_c w_a b²). -/
private lemma weighted_norm_sq_gen (T : Triangle) (wa wb wc : ℝ) :
    (wa * (T.A.1 - T.circumcenter.1) + wb * (T.B.1 - T.circumcenter.1)
        + wc * (T.C.1 - T.circumcenter.1)) ^ 2 +
    (wa * (T.A.2 - T.circumcenter.2) + wb * (T.B.2 - T.circumcenter.2)
        + wc * (T.C.2 - T.circumcenter.2)) ^ 2 =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
        * (wa + wb + wc) ^ 2
    - (wa * wb * T.side_c ^ 2 + wb * wc * T.side_a ^ 2 + wc * wa * T.side_b ^ 2) := by
  set O := T.circumcenter
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have e1 : (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 = R2 := rfl
  have e2 : (T.B.1 - O.1) ^ 2 + (T.B.2 - O.2) ^ 2 = R2 := by rw [hR2]; exact equidist_B T
  have e3 : (T.C.1 - O.1) ^ 2 + (T.C.2 - O.2) ^ 2 = R2 := by rw [hR2]; exact equidist_C T
  have dotAB : (T.A.1 - O.1) * (T.B.1 - O.1) + (T.A.2 - O.2) * (T.B.2 - O.2)
      = R2 - T.side_c ^ 2 / 2 := by
    have hc := side_c_sq T
    linear_combination (1 / 2) * e1 + (1 / 2) * e2 + (1 / 2) * hc
  have dotBC : (T.B.1 - O.1) * (T.C.1 - O.1) + (T.B.2 - O.2) * (T.C.2 - O.2)
      = R2 - T.side_a ^ 2 / 2 := by
    have ha := side_a_sq T
    linear_combination (1 / 2) * e2 + (1 / 2) * e3 + (1 / 2) * ha
  have dotCA : (T.C.1 - O.1) * (T.A.1 - O.1) + (T.C.2 - O.2) * (T.A.2 - O.2)
      = R2 - T.side_b ^ 2 / 2 := by
    have hb := side_b_sq T
    linear_combination (1 / 2) * e3 + (1 / 2) * e1 + (1 / 2) * hb
  linear_combination
    wa ^ 2 * e1 + wb ^ 2 * e2 + wc ^ 2 * e3
    + 2 * wa * wb * dotAB + 2 * wb * wc * dotBC + 2 * wc * wa * dotCA

/-- R² = |A − O|² (circumradius squared, dropping the square root). -/
private lemma circumradius_sq (T : Triangle) :
    T.circumradius ^ 2 = (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity)]

private lemma circumradius_nonneg (T : Triangle) : 0 ≤ T.circumradius := by
  unfold Triangle.circumradius dist2; exact Real.sqrt_nonneg _

-- ============================================================
-- PART 5: The excentral circumradius  dist²(O', I_x) = 4R²
-- ============================================================

/-- **The excentral circumradius, excentre a.**  The reflection O' = 2O − I of
    the incentre in the circumcentre is at squared distance 4R² from the
    A-excentre. -/
theorem excentral_dist_a_sq (T : Triangle) :
    dist2_sq T.excentralCircumcenter T.excenter_a = 4 * T.circumradius ^ 2 := by
  rw [circumradius_sq]
  unfold Triangle.excentralCircumcenter
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hpa : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hk : ((-T.side_a + T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hpa hP)
  -- clear denominators:  dist²·(p_a·p_s)² = 4·|weighted vector|²
  have hI : dist2_sq (2 * O.1 - T.incenter.1, 2 * O.2 - T.incenter.2) T.excenter_a
        * ((-T.side_a + T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2
      = 4 * (((-T.side_a ^ 2) * (T.A.1 - O.1)
                + (T.side_b * (T.side_b + T.side_c)) * (T.B.1 - O.1)
                + (T.side_c * (T.side_b + T.side_c)) * (T.C.1 - O.1)) ^ 2
            + ((-T.side_a ^ 2) * (T.A.2 - O.2)
                + (T.side_b * (T.side_b + T.side_c)) * (T.B.2 - O.2)
                + (T.side_c * (T.side_b + T.side_c)) * (T.C.2 - O.2)) ^ 2) := by
    unfold dist2_sq Triangle.excenter_a Triangle.incenter
    dsimp only
    field_simp
    ring
  have hmaster := weighted_norm_sq_gen T (-T.side_a ^ 2)
    (T.side_b * (T.side_b + T.side_c)) (T.side_c * (T.side_b + T.side_c))
  rw [← hO, ← hR2] at hmaster
  have hcombine :
      ((-T.side_a ^ 2) * (T.A.1 - O.1)
            + (T.side_b * (T.side_b + T.side_c)) * (T.B.1 - O.1)
            + (T.side_c * (T.side_b + T.side_c)) * (T.C.1 - O.1)) ^ 2
        + ((-T.side_a ^ 2) * (T.A.2 - O.2)
            + (T.side_b * (T.side_b + T.side_c)) * (T.B.2 - O.2)
            + (T.side_c * (T.side_b + T.side_c)) * (T.C.2 - O.2)) ^ 2
      = R2 * ((-T.side_a + T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 := by
    rw [hmaster]; ring
  apply mul_right_cancel₀ hk
  rw [hI, hcombine]; ring

/-- **The excentral circumradius, excentre b.** -/
theorem excentral_dist_b_sq (T : Triangle) :
    dist2_sq T.excentralCircumcenter T.excenter_b = 4 * T.circumradius ^ 2 := by
  rw [circumradius_sq]
  unfold Triangle.excentralCircumcenter
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hpb : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hk : ((T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hpb hP)
  have hI : dist2_sq (2 * O.1 - T.incenter.1, 2 * O.2 - T.incenter.2) T.excenter_b
        * ((T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2
      = 4 * (((T.side_a * (T.side_a + T.side_c)) * (T.A.1 - O.1)
                + (-T.side_b ^ 2) * (T.B.1 - O.1)
                + (T.side_c * (T.side_a + T.side_c)) * (T.C.1 - O.1)) ^ 2
            + ((T.side_a * (T.side_a + T.side_c)) * (T.A.2 - O.2)
                + (-T.side_b ^ 2) * (T.B.2 - O.2)
                + (T.side_c * (T.side_a + T.side_c)) * (T.C.2 - O.2)) ^ 2) := by
    unfold dist2_sq Triangle.excenter_b Triangle.incenter
    dsimp only
    field_simp
    ring
  have hmaster := weighted_norm_sq_gen T (T.side_a * (T.side_a + T.side_c))
    (-T.side_b ^ 2) (T.side_c * (T.side_a + T.side_c))
  rw [← hO, ← hR2] at hmaster
  have hcombine :
      ((T.side_a * (T.side_a + T.side_c)) * (T.A.1 - O.1)
            + (-T.side_b ^ 2) * (T.B.1 - O.1)
            + (T.side_c * (T.side_a + T.side_c)) * (T.C.1 - O.1)) ^ 2
        + ((T.side_a * (T.side_a + T.side_c)) * (T.A.2 - O.2)
            + (-T.side_b ^ 2) * (T.B.2 - O.2)
            + (T.side_c * (T.side_a + T.side_c)) * (T.C.2 - O.2)) ^ 2
      = R2 * ((T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 := by
    rw [hmaster]; ring
  apply mul_right_cancel₀ hk
  rw [hI, hcombine]; ring

/-- **The excentral circumradius, excentre c.** -/
theorem excentral_dist_c_sq (T : Triangle) :
    dist2_sq T.excentralCircumcenter T.excenter_c = 4 * T.circumradius ^ 2 := by
  rw [circumradius_sq]
  unfold Triangle.excentralCircumcenter
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hpc : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hk : ((T.side_a + T.side_b - T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hpc hP)
  have hI : dist2_sq (2 * O.1 - T.incenter.1, 2 * O.2 - T.incenter.2) T.excenter_c
        * ((T.side_a + T.side_b - T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2
      = 4 * (((T.side_a * (T.side_a + T.side_b)) * (T.A.1 - O.1)
                + (T.side_b * (T.side_a + T.side_b)) * (T.B.1 - O.1)
                + (-T.side_c ^ 2) * (T.C.1 - O.1)) ^ 2
            + ((T.side_a * (T.side_a + T.side_b)) * (T.A.2 - O.2)
                + (T.side_b * (T.side_a + T.side_b)) * (T.B.2 - O.2)
                + (-T.side_c ^ 2) * (T.C.2 - O.2)) ^ 2) := by
    unfold dist2_sq Triangle.excenter_c Triangle.incenter
    dsimp only
    field_simp
    ring
  have hmaster := weighted_norm_sq_gen T (T.side_a * (T.side_a + T.side_b))
    (T.side_b * (T.side_a + T.side_b)) (-T.side_c ^ 2)
  rw [← hO, ← hR2] at hmaster
  have hcombine :
      ((T.side_a * (T.side_a + T.side_b)) * (T.A.1 - O.1)
            + (T.side_b * (T.side_a + T.side_b)) * (T.B.1 - O.1)
            + (-T.side_c ^ 2) * (T.C.1 - O.1)) ^ 2
        + ((T.side_a * (T.side_a + T.side_b)) * (T.A.2 - O.2)
            + (T.side_b * (T.side_a + T.side_b)) * (T.B.2 - O.2)
            + (-T.side_c ^ 2) * (T.C.2 - O.2)) ^ 2
      = R2 * ((T.side_a + T.side_b - T.side_c) * (T.side_a + T.side_b + T.side_c)) ^ 2 := by
    rw [hmaster]; ring
  apply mul_right_cancel₀ hk
  rw [hI, hcombine]; ring

-- ============================================================
-- PART 6: The square-root form  dist(O', I_x) = 2R
-- ============================================================

/-- **Excentral circumradius (distance form), excentre a:** dist(O', I_a) = 2R. -/
theorem excentral_circumradius_a (T : Triangle) :
    dist2 T.excentralCircumcenter T.excenter_a = 2 * T.circumradius := by
  have h := excentral_dist_a_sq T
  have hR := circumradius_nonneg T
  rw [show dist2 T.excentralCircumcenter T.excenter_a
        = Real.sqrt (dist2_sq T.excentralCircumcenter T.excenter_a) from rfl,
      h, show (4 : ℝ) * T.circumradius ^ 2 = (2 * T.circumradius) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

/-- **Excentral circumradius (distance form), excentre b:** dist(O', I_b) = 2R. -/
theorem excentral_circumradius_b (T : Triangle) :
    dist2 T.excentralCircumcenter T.excenter_b = 2 * T.circumradius := by
  have h := excentral_dist_b_sq T
  have hR := circumradius_nonneg T
  rw [show dist2 T.excentralCircumcenter T.excenter_b
        = Real.sqrt (dist2_sq T.excentralCircumcenter T.excenter_b) from rfl,
      h, show (4 : ℝ) * T.circumradius ^ 2 = (2 * T.circumradius) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

/-- **Excentral circumradius (distance form), excentre c:** dist(O', I_c) = 2R. -/
theorem excentral_circumradius_c (T : Triangle) :
    dist2 T.excentralCircumcenter T.excenter_c = 2 * T.circumradius := by
  have h := excentral_dist_c_sq T
  have hR := circumradius_nonneg T
  rw [show dist2 T.excentralCircumcenter T.excenter_c
        = Real.sqrt (dist2_sq T.excentralCircumcenter T.excenter_c) from rfl,
      h, show (4 : ℝ) * T.circumradius ^ 2 = (2 * T.circumradius) ^ 2 by ring,
      Real.sqrt_sq (by linarith)]

/-- **The excentral triangle has circumradius 2R.**  The point O' = 2O − I is
    equidistant — at distance exactly 2R — from all three excentres, hence is the
    circumcentre of the excentral triangle I_a I_b I_c, whose circumradius is
    therefore twice that of ABC. -/
theorem excentral_circumradius_eq_two_R (T : Triangle) :
    dist2 T.excentralCircumcenter T.excenter_a = 2 * T.circumradius ∧
    dist2 T.excentralCircumcenter T.excenter_b = 2 * T.circumradius ∧
    dist2 T.excentralCircumcenter T.excenter_c = 2 * T.circumradius :=
  ⟨excentral_circumradius_a T, excentral_circumradius_b T, excentral_circumradius_c T⟩

-- ============================================================
-- PART 7: The nine-point relation  O = ½(I + O')
-- ============================================================

/-- **O is the nine-point centre of the excentral triangle.**  The circumcentre
    is the midpoint of the incentre I (the orthocentre of the excentral triangle)
    and the excentral circumcentre O' — the defining relation of the nine-point
    centre.  Hence the nine-point circle of I_a I_b I_c is the circumcircle of
    ABC (its radius R is half the excentral circumradius 2R). -/
theorem circumcenter_is_excentral_ninePointCenter (T : Triangle) :
    T.circumcenter.1 = (T.incenter.1 + T.excentralCircumcenter.1) / 2 ∧
    T.circumcenter.2 = (T.incenter.2 + T.excentralCircumcenter.2) / 2 := by
  unfold Triangle.excentralCircumcenter
  refine ⟨?_, ?_⟩ <;> · dsimp only; ring

-- ============================================================
-- PART 8: Worked example — the 3-4-5 right triangle
-- ============================================================

/-- **Excentral circumradius for the 3-4-5 triangle.**  With O = (3/2,2),
    I = (1,1), the excentral circumcentre is O' = (2,3), and its squared
    distance to each excentre is 25 = 4·(5/2)² = 4R². -/
theorem triangle_345_excentral_circumradius :
    dist2_sq triangle_345.excentralCircumcenter triangle_345.excenter_a = 25 ∧
    dist2_sq triangle_345.excentralCircumcenter triangle_345.excenter_b = 25 ∧
    dist2_sq triangle_345.excentralCircumcenter triangle_345.excenter_c = 25 := by
  have ha := excentral_dist_a_sq triangle_345
  have hb := excentral_dist_b_sq triangle_345
  have hc := excentral_dist_c_sq triangle_345
  rw [triangle_345_circumradius] at ha hb hc
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]; norm_num
  · rw [hb]; norm_num
  · rw [hc]; norm_num

end FeuerbachExcentralCircumradius
