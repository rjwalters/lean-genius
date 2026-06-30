/-
  Feuerbach's Theorem DefsOQ02OQ01OQ01:
  The circumcentre–to–centre square-distance sum   OI² + OI_a² + OI_b² + OI_c² = 12R²

  ## The Open Question

  The sibling files prove Euler's two metric relations of 1765:

      OI²   = R² − 2·R·r          (incentre,   `FeuerbachsTheoremDefsOQ02`)
      OI_a² = R² + 2·R·r_a        (excentres,  `FeuerbachsTheoremDefsOQ02OQ01`)

  Both express a *single* circumcentre–centre distance.  A natural structural
  question is what happens when the four classical tritangent centres — the
  incentre I and the three excentres I_a, I_b, I_c — are taken **together**.
  Adding the four Euler formulas,

      OI² + OI_a² + OI_b² + OI_c²
        = 4R² + 2R·(r_a + r_b + r_c − r),

  so the whole sum collapses as soon as one knows the classical exradius
  identity  r_a + r_b + r_c − r = 4R.  The result is the remarkably clean

      OI² + OI_a² + OI_b² + OI_c² = 12R²,

  independent of the shape of the triangle.

  ## What This File Proves

  For an arbitrary non-degenerate triangle T:

  ### Heron's identity (the genuinely new ingredient)
  `heron` :  16·Area² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c).  Proved from the
  shoelace area and the squared side lengths — a degree-4 coordinate identity.
  It is what converts the reciprocal sum 1/p_a + 1/p_b + 1/p_c − 1/p_s
  (with p_a = −a+b+c, …, p_s = a+b+c) into the circumradius.

  ### The main identity
  `sum_OI_sq_eq_twelve_R_sq` :
      dist²(O,I) + dist²(O,I_a) + dist²(O,I_b) + dist²(O,I_c) = 12·R².

  ### The classical exradius identity
  `sum_exradii_sub_inradius_eq_four_R` :  r_a + r_b + r_c − r = 4R.

  ### Example
  `triangle_345_sum_OI_sq` :  for the 3-4-5 triangle the four squared distances
  are 5/4, 145/4, 85/4, 65/4, summing to 75 = 12·(5/2)².

  The four Euler formulas (`euler_OI_formula`, `euler_OI_a/b/c_formula`) and the
  law-of-sines bridge `four_R_area_eq_abc` are reused from the sibling files; the
  strict triangle inequalities (which force the excentre denominators p_a,p_b,p_c
  to be positive so the reciprocal sum can be cleared) are reproved locally since
  the parent declares them `private`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefsOQ02OQ01

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachSumOISq

open FeuerbachsTheorem
open FeuerbachEulerOI
open FeuerbachExcenterEuler
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
-- PART 3: Heron's identity   16·Area² = (a+b+c)(−a+b+c)(a−b+c)(a+b−c)
-- ============================================================

/-- **Heron's identity** in the form 16·Area² = p_s·p_a·p_b·p_c, where
    p_s = a+b+c and p_a = −a+b+c, p_b = a−b+c, p_c = a+b−c.  Proved from the
    shoelace area and the coordinate expressions for the squared side lengths. -/
private lemma heron (T : Triangle) :
    16 * T.area ^ 2 =
      (T.side_a + T.side_b + T.side_c) * (-T.side_a + T.side_b + T.side_c)
        * (T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b - T.side_c) := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hsq :
      (T.side_a + T.side_b + T.side_c) * (-T.side_a + T.side_b + T.side_c)
        * (T.side_a - T.side_b + T.side_c) * (T.side_a + T.side_b - T.side_c)
      = 2 * (T.side_a ^ 2) * (T.side_b ^ 2) + 2 * (T.side_b ^ 2) * (T.side_c ^ 2)
        + 2 * (T.side_c ^ 2) * (T.side_a ^ 2)
        - (T.side_a ^ 2) ^ 2 - (T.side_b ^ 2) ^ 2 - (T.side_c ^ 2) ^ 2 := by
    ring
  rw [hsq, ha, hb, hc]
  unfold Triangle.area
  have habs := sq_abs ((T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2))
  rw [div_pow, habs]
  ring

-- ============================================================
-- PART 4: The key reciprocal identity   2R(r_a+r_b+r_c−r) = 8R²
-- ============================================================

/-- The reciprocal sum cleared by Heron:
      2R·r_a + 2R·r_b + 2R·r_c − 2R·r = 8R². -/
private lemma key (T : Triangle) :
    2 * T.circumradius * T.exradius_a + 2 * T.circumradius * T.exradius_b
      + 2 * T.circumradius * T.exradius_c - 2 * T.circumradius * T.inradius
    = 8 * T.circumradius ^ 2 := by
  have hpa := pa_pos T
  have hpb := pb_pos T
  have hpc := pc_pos T
  have hps := perimeter_pos T
  have hFRA := four_R_area_eq_abc T
  have hHeron := heron T
  rw [two_R_ra_eq, two_R_rb_eq, two_R_rc_eq, two_R_r_eq]
  rw [div_add_div _ _ (ne_of_gt hpa) (ne_of_gt hpb),
      div_add_div _ _ (mul_ne_zero (ne_of_gt hpa) (ne_of_gt hpb)) (ne_of_gt hpc),
      div_sub_div _ _ (mul_ne_zero (mul_ne_zero (ne_of_gt hpa) (ne_of_gt hpb)) (ne_of_gt hpc))
        (ne_of_gt hps),
      div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hpa) (ne_of_gt hpb))
        (ne_of_gt hpc)) (ne_of_gt hps))]
  linear_combination
    (-8 * (T.side_a * T.side_b * T.side_c + 4 * T.circumradius * T.area)) * hFRA
    + (8 * T.circumradius ^ 2) * hHeron

-- ============================================================
-- PART 5: The main identity   OI² + OI_a² + OI_b² + OI_c² = 12R²
-- ============================================================

/-- **The circumcentre–centre square-distance sum.**  The sum of the squared
    distances from the circumcentre to the incentre and the three excentres is
    `12R²`, independent of the shape of the triangle.  Equivalent to the four
    Euler formulas together with the exradius identity r_a+r_b+r_c−r = 4R. -/
theorem sum_OI_sq_eq_twelve_R_sq (T : Triangle) :
    dist2_sq T.circumcenter T.incenter
      + dist2_sq T.circumcenter T.excenter_a
      + dist2_sq T.circumcenter T.excenter_b
      + dist2_sq T.circumcenter T.excenter_c
    = 12 * T.circumradius ^ 2 := by
  rw [euler_OI_formula, euler_OI_a_formula, euler_OI_b_formula, euler_OI_c_formula]
  linear_combination key T

-- ============================================================
-- PART 6: The classical exradius identity   r_a + r_b + r_c − r = 4R
-- ============================================================

/-- **The exradius identity** (a classical companion of Euler's formula):
    the three exradii exceed the inradius by exactly four circumradii,
    r_a + r_b + r_c − r = 4R. -/
theorem sum_exradii_sub_inradius_eq_four_R (T : Triangle) :
    T.exradius_a + T.exradius_b + T.exradius_c - T.inradius = 4 * T.circumradius := by
  have hR : 0 < T.circumradius := by
    have hF := four_R_area_eq_abc T
    have hA := area_pos T
    have habc : 0 < T.side_a * T.side_b * T.side_c :=
      mul_pos (mul_pos (side_a_pos T) (side_b_pos T)) (side_c_pos T)
    nlinarith [hF, hA, habc]
  have h2R : (0 : ℝ) < 2 * T.circumradius := by linarith
  have hkey :
      2 * T.circumradius * (T.exradius_a + T.exradius_b + T.exradius_c - T.inradius)
        = 2 * T.circumradius * (4 * T.circumradius) := by
    linear_combination key T
  exact mul_left_cancel₀ (ne_of_gt h2R) hkey

-- ============================================================
-- PART 7: Worked example — the 3-4-5 right triangle
-- ============================================================

/-- For the 3-4-5 triangle the four squared distances sum to 75 = 12·(5/2)². -/
theorem triangle_345_sum_OI_sq :
    dist2_sq triangle_345.circumcenter triangle_345.incenter
      + dist2_sq triangle_345.circumcenter triangle_345.excenter_a
      + dist2_sq triangle_345.circumcenter triangle_345.excenter_b
      + dist2_sq triangle_345.circumcenter triangle_345.excenter_c
    = 75 := by
  rw [sum_OI_sq_eq_twelve_R_sq, triangle_345_circumradius]
  norm_num

end FeuerbachSumOISq
