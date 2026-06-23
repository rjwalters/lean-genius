/-
  Feuerbach's Theorem DefsOQ02OQ01OQ01OQ01OQ01OQ01:
  The incentre is the orthocentre of the excentral triangle
  (the four tritangent centres form an orthocentric system).

  ## The Open Question

  The sibling file `FeuerbachsTheoremDefsOQ02OQ01OQ01OQ01OQ01` proves that the
  reflection O' = 2·O − I of the incentre in the circumcentre is the circumcentre
  of the excentral triangle I_a I_b I_c, at distance 2R from each excentre, and
  that O is the midpoint of I and O'.  That last fact *only makes sense* — it is
  the nine-point relation — once one knows the missing ingredient that file's
  narrative repeatedly *asserts but never proves*: that **the incentre I is the
  orthocentre of the excentral triangle**.  This file supplies that proof.

  ## What This File Proves

  For an arbitrary non-degenerate triangle T with incentre I and excentres
  I_a, I_b, I_c, the three internal angle bisectors of ABC — the lines I I_a,
  I I_b, I I_c — are the three **altitudes** of the excentral triangle:

  `incenter_altitude_perp_a` :  ⟨I_a − I, I_c − I_b⟩ = 0
  `incenter_altitude_perp_b` :  ⟨I_b − I, I_c − I_a⟩ = 0
  `incenter_altitude_perp_c` :  ⟨I_c − I, I_b − I_a⟩ = 0

  Each says the line through the incentre I and one excentre is perpendicular to
  the opposite side of the excentral triangle.  Since all three altitudes pass
  through the single point I, they concur there:

  `incenter_is_excentral_orthocenter` bundles the three — exactly the statement
  that **I is the orthocentre of I_a I_b I_c**.

  Equivalently the four points {I, I_a, I_b, I_c} form an **orthocentric system**:
  the three pairs of opposite connectors
      {I, I_a} ⟂ {I_b, I_c},   {I, I_b} ⟂ {I_a, I_c},   {I, I_c} ⟂ {I_a, I_b}
  are mutually perpendicular, so each of the four points is the orthocentre of the
  triangle formed by the other three.  Combined with the sibling's results — O' =
  2O − I is the excentral circumcentre (circumradius 2R) and O = ½(I + O') is the
  excentral nine-point centre — this completes the orthocentric-system picture:
  the nine-point circle of the excentral triangle is the circumcircle of ABC.

  ### Worked example
  `triangle_345_orthocentric_system` :  for the 3-4-5 triangle, I = (1,1),
  I_a = (6,6), I_b = (−3,3), I_c = (2,−2); and indeed
      ⟨I_a−I, I_c−I_b⟩ = ⟨5,5⟩·⟨5,−5⟩ = 0,
      ⟨I_b−I, I_c−I_a⟩ = ⟨−4,2⟩·⟨−4,−8⟩ = 0,
      ⟨I_c−I, I_b−I_a⟩ = ⟨1,−3⟩·⟨−9,−3⟩ = 0.

  ## Method

  The heart is a one-line vector identity.  Writing the excentre-minus-incentre
  difference over its common denominator,
      I_a − I  =  2a·[ b·(B−A) + c·(C−A) ] / ((−a+b+c)(a+b+c)),
  while the opposite excentral side, over its common denominator, is
      I_c − I_b  =  2a·[ b·(B−A) − c·(C−A) ] / ((a+b−c)(a−b+c)).
  With u := b·(B−A) and v := c·(C−A) these are proportional to u+v and u−v, so
      ⟨I_a − I, I_c − I_b⟩  ∝  ⟨u+v, u−v⟩  =  |u|² − |v|²
        =  b²·|B−A|²  −  c²·|C−A|²  =  b²c² − c²b²  =  0,
  using only the *definitions* |B−A|² = c² and |C−A|² = b².  No deeper triangle
  geometry is needed: perpendicularity of an internal bisector to the opposite
  external-bisector chord is forced by the side-length weights alone.  The b- and
  c-altitudes are the cyclic images.

  Concretely each statement is proved by clearing the four tritangent-centre
  denominators (`field_simp; ring`, a pure rational identity) to land on
      4a²·( b²·|B−A|² − c²·|C−A|² ),
  then substituting the squared-side definitions (`linear_combination`) to get 0,
  and finally cancelling the nonzero denominator product.

  The squared-side, positivity and strict-triangle-inequality lemmas (needed to
  keep the excentre denominators nonzero) are reproved locally, as the parent
  files declare them `private`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachExcentralOrthocenter

open FeuerbachsTheorem
open scoped Real

-- ============================================================
-- PART 1: Squared side lengths and positivity (parent's are private)
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
-- PART 2: The strict triangle inequality  a < b + c
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
-- PART 3: The three altitudes of the excentral triangle pass through I
-- ============================================================

set_option maxHeartbeats 4000000 in
/-- **The A-altitude of the excentral triangle passes through I.**  The line
    I I_a (the internal bisector from A) is perpendicular to the opposite side
    I_b I_c of the excentral triangle:  ⟨I_a − I, I_c − I_b⟩ = 0. -/
theorem incenter_altitude_perp_a (T : Triangle) :
    (T.excenter_a.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_b.1)
      + (T.excenter_a.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_b.2) = 0 := by
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hpa : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hpb : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hpc : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hD : ((-T.side_a + T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a + T.side_b - T.side_c) * (T.side_a - T.side_b + T.side_c)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpa hP) (mul_ne_zero hpc hpb)
  have hclear :
      ((T.excenter_a.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_b.1)
        + (T.excenter_a.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_b.2))
        * (((-T.side_a + T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a + T.side_b - T.side_c) * (T.side_a - T.side_b + T.side_c)))
      = 4 * T.side_a ^ 2 *
          (T.side_b ^ 2 * ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)
            - T.side_c ^ 2 * ((T.C.1 - T.A.1) ^ 2 + (T.C.2 - T.A.2) ^ 2)) := by
    unfold Triangle.incenter Triangle.excenter_a Triangle.excenter_b Triangle.excenter_c
    dsimp only
    field_simp
    ring
  have hzero : 4 * T.side_a ^ 2 *
      (T.side_b ^ 2 * ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)
        - T.side_c ^ 2 * ((T.C.1 - T.A.1) ^ 2 + (T.C.2 - T.A.2) ^ 2)) = 0 := by
    linear_combination (-4 * T.side_a ^ 2 * T.side_b ^ 2) * hc
      + (4 * T.side_a ^ 2 * T.side_c ^ 2) * hb
  have hprod := hclear.trans hzero
  exact (mul_eq_zero.mp hprod).resolve_right hD

set_option maxHeartbeats 4000000 in
/-- **The B-altitude of the excentral triangle passes through I.**  The line
    I I_b is perpendicular to the opposite side I_a I_c:  ⟨I_b − I, I_c − I_a⟩ = 0. -/
theorem incenter_altitude_perp_b (T : Triangle) :
    (T.excenter_b.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_a.1)
      + (T.excenter_b.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_a.2) = 0 := by
  have ha := side_a_sq T
  have hc := side_c_sq T
  have hpa : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hpb : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hpc : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hD : ((T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a + T.side_b - T.side_c) * (-T.side_a + T.side_b + T.side_c)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpb hP) (mul_ne_zero hpc hpa)
  have hclear :
      ((T.excenter_b.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_a.1)
        + (T.excenter_b.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_a.2))
        * (((T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a + T.side_b - T.side_c) * (-T.side_a + T.side_b + T.side_c)))
      = 4 * T.side_b ^ 2 *
          (T.side_a ^ 2 * ((T.A.1 - T.B.1) ^ 2 + (T.A.2 - T.B.2) ^ 2)
            - T.side_c ^ 2 * ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)) := by
    unfold Triangle.incenter Triangle.excenter_a Triangle.excenter_b Triangle.excenter_c
    dsimp only
    field_simp
    ring
  have hzero : 4 * T.side_b ^ 2 *
      (T.side_a ^ 2 * ((T.A.1 - T.B.1) ^ 2 + (T.A.2 - T.B.2) ^ 2)
        - T.side_c ^ 2 * ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)) = 0 := by
    linear_combination (-4 * T.side_a ^ 2 * T.side_b ^ 2) * hc
      + (4 * T.side_b ^ 2 * T.side_c ^ 2) * ha
  have hprod := hclear.trans hzero
  exact (mul_eq_zero.mp hprod).resolve_right hD

set_option maxHeartbeats 4000000 in
/-- **The C-altitude of the excentral triangle passes through I.**  The line
    I I_c is perpendicular to the opposite side I_a I_b:  ⟨I_c − I, I_b − I_a⟩ = 0. -/
theorem incenter_altitude_perp_c (T : Triangle) :
    (T.excenter_c.1 - T.incenter.1) * (T.excenter_b.1 - T.excenter_a.1)
      + (T.excenter_c.2 - T.incenter.2) * (T.excenter_b.2 - T.excenter_a.2) = 0 := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hpa : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  have hP : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hpb : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hpc : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hD : ((T.side_a + T.side_b - T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a - T.side_b + T.side_c) * (-T.side_a + T.side_b + T.side_c)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hpc hP) (mul_ne_zero hpb hpa)
  have hclear :
      ((T.excenter_c.1 - T.incenter.1) * (T.excenter_b.1 - T.excenter_a.1)
        + (T.excenter_c.2 - T.incenter.2) * (T.excenter_b.2 - T.excenter_a.2))
        * (((T.side_a + T.side_b - T.side_c) * (T.side_a + T.side_b + T.side_c))
            * ((T.side_a - T.side_b + T.side_c) * (-T.side_a + T.side_b + T.side_c)))
      = 4 * T.side_c ^ 2 *
          (T.side_a ^ 2 * ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)
            - T.side_b ^ 2 * ((T.B.1 - T.C.1) ^ 2 + (T.B.2 - T.C.2) ^ 2)) := by
    unfold Triangle.incenter Triangle.excenter_a Triangle.excenter_b Triangle.excenter_c
    dsimp only
    field_simp
    ring
  have hzero : 4 * T.side_c ^ 2 *
      (T.side_a ^ 2 * ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)
        - T.side_b ^ 2 * ((T.B.1 - T.C.1) ^ 2 + (T.B.2 - T.C.2) ^ 2)) = 0 := by
    linear_combination (-4 * T.side_a ^ 2 * T.side_c ^ 2) * hb
      + (4 * T.side_b ^ 2 * T.side_c ^ 2) * ha
  have hprod := hclear.trans hzero
  exact (mul_eq_zero.mp hprod).resolve_right hD

-- ============================================================
-- PART 4: I is the orthocentre of the excentral triangle
-- ============================================================

/-- **The incentre is the orthocentre of the excentral triangle.**  All three
    altitudes of I_a I_b I_c — each the perpendicular from a vertex to the
    opposite side — pass through the single point I, so they concur there.  This
    is exactly the statement that I is the orthocentre of the excentral triangle,
    and that {I, I_a, I_b, I_c} is an orthocentric system. -/
theorem incenter_is_excentral_orthocenter (T : Triangle) :
    (T.excenter_a.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_b.1)
      + (T.excenter_a.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_b.2) = 0 ∧
    (T.excenter_b.1 - T.incenter.1) * (T.excenter_c.1 - T.excenter_a.1)
      + (T.excenter_b.2 - T.incenter.2) * (T.excenter_c.2 - T.excenter_a.2) = 0 ∧
    (T.excenter_c.1 - T.incenter.1) * (T.excenter_b.1 - T.excenter_a.1)
      + (T.excenter_c.2 - T.incenter.2) * (T.excenter_b.2 - T.excenter_a.2) = 0 :=
  ⟨incenter_altitude_perp_a T, incenter_altitude_perp_b T, incenter_altitude_perp_c T⟩

-- ============================================================
-- PART 5: Worked example — the 3-4-5 right triangle
-- ============================================================

/-- A-excentre of the 3-4-5 triangle is (6, 6). -/
theorem triangle_345_excenter_a : triangle_345.excenter_a = (6, 6) := by
  unfold Triangle.excenter_a
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- B-excentre of the 3-4-5 triangle is (−3, 3). -/
theorem triangle_345_excenter_b : triangle_345.excenter_b = (-3, 3) := by
  unfold Triangle.excenter_b
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- C-excentre of the 3-4-5 triangle is (2, −2). -/
theorem triangle_345_excenter_c : triangle_345.excenter_c = (2, -2) := by
  unfold Triangle.excenter_c
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- **Orthocentric system verified for the 3-4-5 triangle.**  With I = (1,1),
    I_a = (6,6), I_b = (−3,3), I_c = (2,−2), the three pairs of opposite
    connectors are mutually perpendicular, so I is the orthocentre of I_a I_b I_c. -/
theorem triangle_345_orthocentric_system :
    (triangle_345.excenter_a.1 - triangle_345.incenter.1)
        * (triangle_345.excenter_c.1 - triangle_345.excenter_b.1)
      + (triangle_345.excenter_a.2 - triangle_345.incenter.2)
        * (triangle_345.excenter_c.2 - triangle_345.excenter_b.2) = 0 ∧
    (triangle_345.excenter_b.1 - triangle_345.incenter.1)
        * (triangle_345.excenter_c.1 - triangle_345.excenter_a.1)
      + (triangle_345.excenter_b.2 - triangle_345.incenter.2)
        * (triangle_345.excenter_c.2 - triangle_345.excenter_a.2) = 0 ∧
    (triangle_345.excenter_c.1 - triangle_345.incenter.1)
        * (triangle_345.excenter_b.1 - triangle_345.excenter_a.1)
      + (triangle_345.excenter_c.2 - triangle_345.incenter.2)
        * (triangle_345.excenter_b.2 - triangle_345.excenter_a.2) = 0 := by
  rw [triangle_345_incenter, triangle_345_excenter_a, triangle_345_excenter_b,
      triangle_345_excenter_c]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

end FeuerbachExcentralOrthocenter
