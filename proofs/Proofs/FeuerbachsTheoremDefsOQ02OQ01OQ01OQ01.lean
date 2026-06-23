/-
  Feuerbach's Theorem DefsOQ02OQ01OQ01OQ01:
  The tritangent-centre centroid is the circumcentre   I + I_a + I_b + I_c = 4·O

  ## The Open Question

  The sibling file `FeuerbachsTheoremDefsOQ02OQ01OQ01` proves the *metric*
  relation among the four classical tritangent centres — the incentre I and the
  three excentres I_a, I_b, I_c — measured from the circumcentre O:

      OI² + OI_a² + OI_b² + OI_c² = 12·R²              (square-distance sum).

  That identity is about *distances*.  A natural structural companion asks for
  the *affine* relation: where does the centroid of the four tritangent centres
  sit?  The answer is the cleanest possible —

      I + I_a + I_b + I_c = 4·O,

  i.e. the circumcentre O is the centroid (arithmetic mean) of the four
  tritangent centres, **for every triangle**.

  ## Why this is the affine companion of the 12R² law

  The two facts are two halves of one picture.  Write G for the centroid of the
  four centres.  Leibniz's identity gives, for any point P,

      Σ PX² = 4·PG² + Σ GX²        (X ranging over I, I_a, I_b, I_c).

  Taking P = O, the present theorem says G = O, so the first term vanishes and
  the 12R² law is exactly Σ OX² = Σ GX² = 12R².  The square-distance sum is the
  moment of inertia of the four centres about their own centroid — and that
  centroid is O.

  Equivalently: {I, I_a, I_b, I_c} is an orthocentric system (I is the
  orthocentre of the excentral triangle I_a I_b I_c), whose common nine-point
  centre is the centroid of the four points.  The statement I+I_a+I_b+I_c = 4O
  is precisely the classical fact that **the circumcircle of ABC is the
  nine-point circle of the excentral triangle** (so the nine-point centre of
  I_a I_b I_c is O and the excentral circumradius is 2R).

  ## What This File Proves

  For an arbitrary non-degenerate triangle T:

  ### The main identity (both coordinates)
  `tritangent_centroid_x`,  `tritangent_centroid_y` :
      I.x + I_a.x + I_b.x + I_c.x = 4·O.x   and the y-analogue.

  ### Point form
  `circumcenter_eq_tritangent_centroid` :  O = ((Σx)/4, (Σy)/4).

  ### Worked example
  `triangle_345_tritangent_centroid` :  for the 3-4-5 triangle the four centres
  are I=(1,1), I_a=(6,6), I_b=(−3,3), I_c=(2,−2), summing to (6,8) = 4·(3/2,2)
  = 4·O.

  ## Method

  Both centres and the circumcentre are written in coordinates.  The proof rests
  on three algebraic identities:

  * `tritangent_mul_heron_x/y` :  the tritangent coordinate sum, multiplied by
    the Heron product p_s·p_a·p_b·p_c, equals 4·N, where N is the standard
    *circumcentre barycentric numerator*
        N_x = a²(b²+c²−a²)·A.x + b²(c²+a²−b²)·B.x + c²(a²+b²−c²)·C.x.
    This is an identity in the *free* side lengths a,b,c (the reciprocal
    denominators telescope), so it is pure `ring`.
  * `circ_bary_x/y` :  N = (circumcentre numerator)·d, a pure coordinate `ring`
    identity expressing that O has barycentric coordinates (a²(b²+c²−a²) : … : …).
  * `sixteen_area_sq` :  16·Area² = d², where d is the circumcentre determinant.
    Combined with Heron (16·Area² = p_s·p_a·p_b·p_c) this gives
    p_s·p_a·p_b·p_c = d², the bridge between the two numerators.

  The squared-side and strict-triangle-inequality lemmas (needed to know the
  excentre denominators p_a,p_b,p_c are nonzero) are reproved locally, as the
  sibling declares them `private`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachTritangentCentroid

open FeuerbachsTheorem

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
-- PART 2: Strict triangle inequalities (force the excentre denominators > 0)
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

private lemma pa_pos (T : Triangle) : 0 < -T.side_a + T.side_b + T.side_c := by
  have := strict_tri_ineq_a T; linarith

private lemma pb_pos (T : Triangle) : 0 < T.side_a - T.side_b + T.side_c := by
  have := strict_tri_ineq_b T; linarith

private lemma pc_pos (T : Triangle) : 0 < T.side_a + T.side_b - T.side_c := by
  have := strict_tri_ineq_c T; linarith

-- ============================================================
-- PART 3: The circumcentre barycentric numerator N and the Heron product
-- ============================================================

/-- The Heron product `p_s · p_a · p_b · p_c`. -/
private def prodP (T : Triangle) : ℝ :=
  (T.side_a + T.side_b + T.side_c) * (-T.side_a + T.side_b + T.side_c)
    * (T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b - T.side_c)

private lemma prodP_pos (T : Triangle) : 0 < prodP T := by
  unfold prodP
  exact mul_pos (mul_pos (mul_pos (perimeter_pos T) (pa_pos T)) (pb_pos T)) (pc_pos T)

/-- The x-component of the circumcentre barycentric numerator:
    `N_x = a²(b²+c²−a²)·A.x + b²(c²+a²−b²)·B.x + c²(a²+b²−c²)·C.x`. -/
private def num_x (T : Triangle) : ℝ :=
  T.side_a ^ 2 * (T.side_b ^ 2 + T.side_c ^ 2 - T.side_a ^ 2) * T.A.1
    + T.side_b ^ 2 * (T.side_c ^ 2 + T.side_a ^ 2 - T.side_b ^ 2) * T.B.1
    + T.side_c ^ 2 * (T.side_a ^ 2 + T.side_b ^ 2 - T.side_c ^ 2) * T.C.1

private def num_y (T : Triangle) : ℝ :=
  T.side_a ^ 2 * (T.side_b ^ 2 + T.side_c ^ 2 - T.side_a ^ 2) * T.A.2
    + T.side_b ^ 2 * (T.side_c ^ 2 + T.side_a ^ 2 - T.side_b ^ 2) * T.B.2
    + T.side_c ^ 2 * (T.side_a ^ 2 + T.side_b ^ 2 - T.side_c ^ 2) * T.C.2

/-- **Heron in determinant form.**  `16·Area² = d²`, where
    `d = 2·((A.x−C.x)(B.y−C.y) − (B.x−C.x)(A.y−C.y))` is the circumcentre
    determinant.  Both sides equal four times the squared signed area. -/
private lemma sixteen_area_sq (T : Triangle) :
    16 * T.area ^ 2 =
      (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))) ^ 2 := by
  unfold Triangle.area
  rw [div_pow, sq_abs]
  ring

/-- Heron's identity `16·Area² = p_s·p_a·p_b·p_c` (proved from the shoelace area
    and the coordinate squared side lengths). -/
private lemma heron (T : Triangle) : 16 * T.area ^ 2 = prodP T := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hsq :
      prodP T
      = 2 * (T.side_a ^ 2) * (T.side_b ^ 2) + 2 * (T.side_b ^ 2) * (T.side_c ^ 2)
        + 2 * (T.side_c ^ 2) * (T.side_a ^ 2)
        - (T.side_a ^ 2) ^ 2 - (T.side_b ^ 2) ^ 2 - (T.side_c ^ 2) ^ 2 := by
    unfold prodP; ring
  rw [hsq, ha, hb, hc]
  unfold Triangle.area
  have habs := sq_abs ((T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2))
  rw [div_pow, habs]
  ring

/-- The Heron product equals the squared circumcentre determinant. -/
private lemma prodP_eq_d_sq (T : Triangle) :
    prodP T =
      (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))) ^ 2 := by
  have h1 := heron T
  have h2 := sixteen_area_sq T
  linarith

/-- **The circumcentre is barycentric** in the x-coordinate:
    `(circumcentre x-numerator)·d = N_x`.  A pure coordinate identity. -/
private lemma circ_bary_x (T : Triangle) :
    ((T.A.1 ^ 2 + T.A.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.B.2 - T.C.2) -
        (T.B.1 ^ 2 + T.B.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.A.2 - T.C.2))
      * (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2)))
    = num_x T := by
  unfold num_x
  rw [side_a_sq, side_b_sq, side_c_sq]
  ring

/-- **The circumcentre is barycentric** in the y-coordinate. -/
private lemma circ_bary_y (T : Triangle) :
    ((T.B.1 ^ 2 + T.B.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.A.1 - T.C.1) -
        (T.A.1 ^ 2 + T.A.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.B.1 - T.C.1))
      * (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2)))
    = num_y T := by
  unfold num_y
  rw [side_a_sq, side_b_sq, side_c_sq]
  ring

-- ============================================================
-- PART 4: The tritangent telescoping identity
-- ============================================================

set_option maxHeartbeats 1600000 in
/-- **The tritangent telescoping identity** (x-coordinate).  The sum of the four
    tritangent x-coordinates, cleared by the Heron product, equals `4·N_x`.  The
    reciprocal denominators telescope, so this is an identity in the *free* side
    lengths a, b, c — pure `ring` after clearing the four fractions. -/
private lemma tritangent_mul_heron_x (T : Triangle) :
    (T.incenter.1 + T.excenter_a.1 + T.excenter_b.1 + T.excenter_c.1) * prodP T
      = 4 * num_x T := by
  have hps := (perimeter_pos T).ne'
  have hpa := (pa_pos T).ne'
  have hpb := (pb_pos T).ne'
  have hpc := (pc_pos T).ne'
  unfold Triangle.incenter Triangle.excenter_a Triangle.excenter_b Triangle.excenter_c prodP num_x
  dsimp only
  field_simp
  ring

set_option maxHeartbeats 1600000 in
/-- **The tritangent telescoping identity** (y-coordinate). -/
private lemma tritangent_mul_heron_y (T : Triangle) :
    (T.incenter.2 + T.excenter_a.2 + T.excenter_b.2 + T.excenter_c.2) * prodP T
      = 4 * num_y T := by
  have hps := (perimeter_pos T).ne'
  have hpa := (pa_pos T).ne'
  have hpb := (pb_pos T).ne'
  have hpc := (pc_pos T).ne'
  unfold Triangle.incenter Triangle.excenter_a Triangle.excenter_b Triangle.excenter_c prodP num_y
  dsimp only
  field_simp
  ring

-- ============================================================
-- PART 5: The main identity   I + I_a + I_b + I_c = 4·O
-- ============================================================

/-- **The tritangent-centroid identity (x-coordinate).**  The sum of the
    x-coordinates of the incentre and the three excentres equals four times the
    circumcentre's x-coordinate. -/
theorem tritangent_centroid_x (T : Triangle) :
    T.incenter.1 + T.excenter_a.1 + T.excenter_b.1 + T.excenter_c.1
      = 4 * T.circumcenter.1 := by
  have hd_ne := circumcenter_denom_ne_zero T
  have hO1 : T.circumcenter.1 =
      ((T.A.1 ^ 2 + T.A.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.B.2 - T.C.2) -
          (T.B.1 ^ 2 + T.B.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.A.2 - T.C.2)) /
        (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))) := by
    unfold Triangle.circumcenter; dsimp
  have e1 : (T.incenter.1 + T.excenter_a.1 + T.excenter_b.1 + T.excenter_c.1) * prodP T
      = 4 * num_x T := tritangent_mul_heron_x T
  have e2 : (4 * T.circumcenter.1) * prodP T = 4 * num_x T := by
    rw [prodP_eq_d_sq T, hO1, ← circ_bary_x T]
    field_simp
  exact mul_right_cancel₀ (prodP_pos T).ne' (e1.trans e2.symm)

/-- **The tritangent-centroid identity (y-coordinate).** -/
theorem tritangent_centroid_y (T : Triangle) :
    T.incenter.2 + T.excenter_a.2 + T.excenter_b.2 + T.excenter_c.2
      = 4 * T.circumcenter.2 := by
  have hd_ne := circumcenter_denom_ne_zero T
  have hO2 : T.circumcenter.2 =
      ((T.B.1 ^ 2 + T.B.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.A.1 - T.C.1) -
          (T.A.1 ^ 2 + T.A.2 ^ 2 - T.C.1 ^ 2 - T.C.2 ^ 2) * (T.B.1 - T.C.1)) /
        (2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))) := by
    unfold Triangle.circumcenter; dsimp
  have e1 : (T.incenter.2 + T.excenter_a.2 + T.excenter_b.2 + T.excenter_c.2) * prodP T
      = 4 * num_y T := tritangent_mul_heron_y T
  have e2 : (4 * T.circumcenter.2) * prodP T = 4 * num_y T := by
    rw [prodP_eq_d_sq T, hO2, ← circ_bary_y T]
    field_simp
  exact mul_right_cancel₀ (prodP_pos T).ne' (e1.trans e2.symm)

/-- **The circumcentre is the centroid of the four tritangent centres.**
    `O = ((I.x+I_a.x+I_b.x+I_c.x)/4, (I.y+I_a.y+I_b.y+I_c.y)/4)`.  Equivalently the
    circumcircle of ABC is the nine-point circle of the excentral triangle. -/
theorem circumcenter_eq_tritangent_centroid (T : Triangle) :
    T.circumcenter =
      ((T.incenter.1 + T.excenter_a.1 + T.excenter_b.1 + T.excenter_c.1) / 4,
       (T.incenter.2 + T.excenter_a.2 + T.excenter_b.2 + T.excenter_c.2) / 4) := by
  apply Prod.ext
  · rw [tritangent_centroid_x T]; ring
  · rw [tritangent_centroid_y T]; ring

-- ============================================================
-- PART 6: Worked example — the 3-4-5 right triangle
-- ============================================================

private lemma t345_excenter_a : triangle_345.excenter_a = (6, 6) := by
  unfold Triangle.excenter_a
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; dsimp
  exact Prod.ext (by norm_num) (by norm_num)

private lemma t345_excenter_b : triangle_345.excenter_b = (-3, 3) := by
  unfold Triangle.excenter_b
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; dsimp
  exact Prod.ext (by norm_num) (by norm_num)

private lemma t345_excenter_c : triangle_345.excenter_c = (2, -2) := by
  unfold Triangle.excenter_c
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; dsimp
  exact Prod.ext (by norm_num) (by norm_num)

/-- **Tritangent centroid for the 3-4-5 triangle.**  The incentre (1,1) and the
    three excentres (6,6), (−3,3), (2,−2) sum to (6,8) = 4·(3/2,2) = 4·O. -/
theorem triangle_345_tritangent_centroid :
    (triangle_345.incenter.1 + triangle_345.excenter_a.1
        + triangle_345.excenter_b.1 + triangle_345.excenter_c.1
      = 4 * triangle_345.circumcenter.1)
    ∧ (triangle_345.incenter.2 + triangle_345.excenter_a.2
        + triangle_345.excenter_b.2 + triangle_345.excenter_c.2
      = 4 * triangle_345.circumcenter.2) := by
  rw [triangle_345_incenter, t345_excenter_a, t345_excenter_b, t345_excenter_c,
      triangle_345_circumcenter]
  constructor <;> norm_num

end FeuerbachTritangentCentroid
