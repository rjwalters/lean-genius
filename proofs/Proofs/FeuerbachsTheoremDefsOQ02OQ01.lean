/-
  Feuerbach's Theorem DefsOQ02OQ01:
  Euler's Circumcenter–Excenter Formula   OI_a² = R² + 2·R·r_a

  ## The Open Question

  The sibling file `FeuerbachsTheoremDefsOQ02` proves **Euler's 1765 formula**
  relating the circumcentre O and the *incentre* I:

      OI² = R² − 2·R·r          (and hence R ≥ 2r, Euler's inequality).

  Euler's *other* metric relation of the same vintage concerns the three
  **excentres** I_a, I_b, I_c (centres of the escribed circles).  For the
  excentre opposite A one has the sign-flipped companion

      OI_a² = R² + 2·R·r_a,

  where r_a is the corresponding exradius.  Unlike the incentre case the
  right-hand side is the *sum* R² + 2Rr_a, so it never vanishes: the
  circumcentre always lies strictly outside every excircle's centre region, in
  fact OI_a > R for every triangle.

  ## What This File Proves

  For an arbitrary non-degenerate triangle T (working purely in coordinates):

  ### A reusable weighted-norm identity
  `weighted_norm_sq_gen` :  for any real weights w_a,w_b,w_c, with O the
  circumcentre and R² = |A−O|²,
      |w_a(A−O)+w_b(B−O)+w_c(C−O)|²
        = R²·(w_a+w_b+w_c)² − (w_a w_b c² + w_b w_c a² + w_c w_a b²).
  Specialising the weights to (−a,b,c), (a,−b,c), (a,b,−c) yields the three
  excentres (and to (a,b,c) the incentre, recovering the sibling file).

  ### The strict triangle inequality (the genuinely new ingredient)
  `strict_tri_ineq_a` :  a < b + c, with the two companions for b and c.
  These force the excentre denominators p_a = −a+b+c, p_b, p_c to be **positive**
  — the incentre proof never needed this because its denominator is a+b+c.
  The proof is the 2-D Lagrange/Cauchy–Schwarz identity
      b²c² − ⟨A−C,B−A⟩² = (nondegeneracy determinant)² > 0.

  ### The affine core and Euler's excentre formula
  `OI_a_sq_eq_R2_add` :  dist²(O, I_a) = R² + abc/(−a+b+c).
  `two_R_ra_eq`       :  2·R·r_a = abc/(−a+b+c).
  `euler_OI_a_formula` :  dist²(O, I_a) = R² + 2·R·r_a   (and b, c versions).

  ### Strict consequence
  `circumradius_lt_OI_a` :  R < OI_a  (the circumcentre is farther from every
  excentre than the circumradius).

  ### Example
  `triangle_345_OI_a_sq` :  for the 3-4-5 triangle, dist²(O, I_a) = 145/4
  (and indeed R² + 2Rr_a = (5/2)² + 2·(5/2)·6 = 145/4, with I_a = (6,6),
  r_a = 6).

  The heavy law-of-sines bridge `4·R·Area = abc` is reused from the sibling
  file `FeuerbachsTheoremDefsOQ02`; everything else is developed here.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefsOQ02

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachExcenterEuler

open FeuerbachsTheorem
open scoped Real

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

-- ============================================================
-- PART 3: The strict triangle inequality  a < b + c
-- ============================================================

set_option maxHeartbeats 1600000 in
/-- **Strict triangle inequality, side a.**  For a non-degenerate triangle the
    Euclidean side lengths satisfy a < b + c.  This is the new ingredient that
    the incentre proof never needed: it forces the excentre denominator
    p_a = −a + b + c to be strictly positive.

    Proof via the 2-D Lagrange identity
        b²c² − ⟨A−C, B−A⟩² = (nondegeneracy determinant)² > 0,
    so the dot product ⟨A−C,B−A⟩ is strictly below bc, whence a² < (b+c)². -/
private lemma strict_tri_ineq_a (T : Triangle) :
    T.side_a < T.side_b + T.side_c := by
  have ha := side_a_sq T
  have hb := side_b_sq T
  have hc := side_c_sq T
  have hapos := side_a_pos T
  have hbpos := side_b_pos T
  have hcpos := side_c_pos T
  -- nondegeneracy determinant and the inner product
  set D := (T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2) with hDdef
  set P := (T.A.1 - T.C.1) * (T.B.1 - T.A.1) + (T.A.2 - T.C.2) * (T.B.2 - T.A.2) with hPdef
  have hDne : D ≠ 0 := T.nondegenerate
  have hD2 : 0 < D ^ 2 := by
    rcases hDne.lt_or_gt with h | h
    · nlinarith [h]
    · nlinarith [h]
  -- law of cosines (squared) and Lagrange identity
  have hexp : T.side_a ^ 2 = T.side_b ^ 2 + T.side_c ^ 2 + 2 * P := by
    rw [ha, hb, hc, hPdef]; ring
  have hlag : T.side_b ^ 2 * T.side_c ^ 2 - P ^ 2 = D ^ 2 := by
    rw [hb, hc, hPdef, hDdef]; ring
  -- strict Cauchy–Schwarz: P² < (bc)²
  have hP2 : P ^ 2 < (T.side_b * T.side_c) ^ 2 := by nlinarith [hlag, hD2]
  -- hence P < bc
  have hbc : 0 < T.side_b * T.side_c := mul_pos hbpos hcpos
  have hPlt : P < T.side_b * T.side_c := by nlinarith [hP2, hbc]
  -- a² < (b+c)²
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
  -- law of cosines at B:  b² = a² + c² + 2⟨C−B, B−A⟩
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
  -- law of cosines at C:  c² = a² + b² + 2⟨C−A, B−C⟩
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
        R²·(w_a+w_b+w_c)² − (w_a w_b c² + w_b w_c a² + w_c w_a b²).
    Specialising the weights selects the incentre (a,b,c) or any excentre. -/
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

-- ============================================================
-- PART 5: The affine core   OI_a² = R² + abc/(−a+b+c)
-- ============================================================

/-- The affine core of Euler's excentre formula:
    dist²(O, I_a) = R² + abc/(−a+b+c), with no square roots involved. -/
theorem OI_a_sq_eq_R2_add (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_a =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
      + T.side_a * T.side_b * T.side_c / (-T.side_a + T.side_b + T.side_c) := by
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hp : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  -- excentre coordinates over the common denominator
  have hI : dist2_sq O T.excenter_a * (-T.side_a + T.side_b + T.side_c) ^ 2 =
      ((-T.side_a) * (T.A.1 - O.1) + T.side_b * (T.B.1 - O.1) + T.side_c * (T.C.1 - O.1)) ^ 2 +
      ((-T.side_a) * (T.A.2 - O.2) + T.side_b * (T.B.2 - O.2) + T.side_c * (T.C.2 - O.2)) ^ 2 := by
    unfold dist2_sq Triangle.excenter_a
    dsimp only
    field_simp [hp]
    ring
  have hmaster := weighted_norm_sq_gen T (-T.side_a) T.side_b T.side_c
  rw [← hO, ← hR2] at hmaster
  -- combine: dist²·p² = R2·p² + abc·p
  have hcombine : dist2_sq O T.excenter_a * (-T.side_a + T.side_b + T.side_c) ^ 2 =
      R2 * (-T.side_a + T.side_b + T.side_c) ^ 2
        + T.side_a * T.side_b * T.side_c * (-T.side_a + T.side_b + T.side_c) := by
    rw [hI]; linear_combination hmaster
  -- cancel one factor of p
  have hkey : dist2_sq O T.excenter_a * (-T.side_a + T.side_b + T.side_c) =
      R2 * (-T.side_a + T.side_b + T.side_c) + T.side_a * T.side_b * T.side_c := by
    apply mul_right_cancel₀ hp
    linear_combination hcombine
  field_simp [hp]
  linear_combination hkey

-- ============================================================
-- PART 6: Bridge   2·R·r_a = abc/(−a+b+c)   and Euler's formula
-- ============================================================

/-- R² = |A − O|² (circumradius squared, dropping the square root). -/
private lemma circumradius_sq (T : Triangle) :
    T.circumradius ^ 2 = (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity)]

/-- Circumradius is positive (cheaply, from the reused law of sines). -/
private lemma circumradius_pos (T : Triangle) : 0 < T.circumradius := by
  have h := FeuerbachEulerOI.four_R_area_eq_abc T
  have hA := area_pos T
  have habc : 0 < T.side_a * T.side_b * T.side_c :=
    mul_pos (mul_pos (side_a_pos T) (side_b_pos T)) (side_c_pos T)
  by_contra hR
  push_neg at hR
  have hle : 4 * T.circumradius * T.area ≤ 0 := by nlinarith [hA, hR]
  linarith [h, habc, hle]

/-- The exradius opposite A is positive. -/
private lemma exradius_a_pos (T : Triangle) : 0 < T.exradius_a := by
  unfold Triangle.exradius_a Triangle.semiperimeter
  apply div_pos (area_pos T)
  have hp := pa_pos T; linarith

/-- 2·R·r_a = abc/(−a+b+c). -/
theorem two_R_ra_eq (T : Triangle) :
    2 * T.circumradius * T.exradius_a =
    T.side_a * T.side_b * T.side_c / (-T.side_a + T.side_b + T.side_c) := by
  have hp : -T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (pa_pos T)
  have hr : T.exradius_a = 2 * T.area / (-T.side_a + T.side_b + T.side_c) := by
    unfold Triangle.exradius_a Triangle.semiperimeter
    have hp2 : (T.side_a + T.side_b + T.side_c) / 2 - T.side_a
        = (-T.side_a + T.side_b + T.side_c) / 2 := by ring
    rw [hp2, div_div_eq_mul_div]
    ring
  rw [hr]
  rw [show 2 * T.circumradius * (2 * T.area / (-T.side_a + T.side_b + T.side_c))
        = (4 * T.circumradius * T.area) / (-T.side_a + T.side_b + T.side_c) from by ring]
  rw [FeuerbachEulerOI.four_R_area_eq_abc]

/-- **Euler's circumcentre–excentre formula** (opposite A):
    the squared distance between the circumcentre and the A-excentre is
    R² + 2·R·r_a. -/
theorem euler_OI_a_formula (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_a =
    T.circumradius ^ 2 + 2 * T.circumradius * T.exradius_a := by
  rw [OI_a_sq_eq_R2_add T, two_R_ra_eq T, circumradius_sq T]

-- ============================================================
-- PART 7: The b- and c-excentre formulas (by the same machinery)
-- ============================================================

/-- Affine core for the B-excentre:  dist²(O, I_b) = R² + abc/(a−b+c). -/
theorem OI_b_sq_eq_R2_add (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_b =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
      + T.side_a * T.side_b * T.side_c / (T.side_a - T.side_b + T.side_c) := by
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hp : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hI : dist2_sq O T.excenter_b * (T.side_a - T.side_b + T.side_c) ^ 2 =
      (T.side_a * (T.A.1 - O.1) + (-T.side_b) * (T.B.1 - O.1) + T.side_c * (T.C.1 - O.1)) ^ 2 +
      (T.side_a * (T.A.2 - O.2) + (-T.side_b) * (T.B.2 - O.2) + T.side_c * (T.C.2 - O.2)) ^ 2 := by
    unfold dist2_sq Triangle.excenter_b
    dsimp only
    field_simp [hp]
    ring
  have hmaster := weighted_norm_sq_gen T T.side_a (-T.side_b) T.side_c
  rw [← hO, ← hR2] at hmaster
  have hcombine : dist2_sq O T.excenter_b * (T.side_a - T.side_b + T.side_c) ^ 2 =
      R2 * (T.side_a - T.side_b + T.side_c) ^ 2
        + T.side_a * T.side_b * T.side_c * (T.side_a - T.side_b + T.side_c) := by
    rw [hI]; linear_combination hmaster
  have hkey : dist2_sq O T.excenter_b * (T.side_a - T.side_b + T.side_c) =
      R2 * (T.side_a - T.side_b + T.side_c) + T.side_a * T.side_b * T.side_c := by
    apply mul_right_cancel₀ hp
    linear_combination hcombine
  field_simp [hp]
  linear_combination hkey

/-- Affine core for the C-excentre:  dist²(O, I_c) = R² + abc/(a+b−c). -/
theorem OI_c_sq_eq_R2_add (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_c =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
      + T.side_a * T.side_b * T.side_c / (T.side_a + T.side_b - T.side_c) := by
  set O := T.circumcenter with hO
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  have hp : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hI : dist2_sq O T.excenter_c * (T.side_a + T.side_b - T.side_c) ^ 2 =
      (T.side_a * (T.A.1 - O.1) + T.side_b * (T.B.1 - O.1) + (-T.side_c) * (T.C.1 - O.1)) ^ 2 +
      (T.side_a * (T.A.2 - O.2) + T.side_b * (T.B.2 - O.2) + (-T.side_c) * (T.C.2 - O.2)) ^ 2 := by
    unfold dist2_sq Triangle.excenter_c
    dsimp only
    field_simp [hp]
    ring
  have hmaster := weighted_norm_sq_gen T T.side_a T.side_b (-T.side_c)
  rw [← hO, ← hR2] at hmaster
  have hcombine : dist2_sq O T.excenter_c * (T.side_a + T.side_b - T.side_c) ^ 2 =
      R2 * (T.side_a + T.side_b - T.side_c) ^ 2
        + T.side_a * T.side_b * T.side_c * (T.side_a + T.side_b - T.side_c) := by
    rw [hI]; linear_combination hmaster
  have hkey : dist2_sq O T.excenter_c * (T.side_a + T.side_b - T.side_c) =
      R2 * (T.side_a + T.side_b - T.side_c) + T.side_a * T.side_b * T.side_c := by
    apply mul_right_cancel₀ hp
    linear_combination hcombine
  field_simp [hp]
  linear_combination hkey

private lemma exradius_b_pos (T : Triangle) : 0 < T.exradius_b := by
  unfold Triangle.exradius_b Triangle.semiperimeter
  apply div_pos (area_pos T)
  have hp := pb_pos T; linarith

private lemma exradius_c_pos (T : Triangle) : 0 < T.exradius_c := by
  unfold Triangle.exradius_c Triangle.semiperimeter
  apply div_pos (area_pos T)
  have hp := pc_pos T; linarith

theorem two_R_rb_eq (T : Triangle) :
    2 * T.circumradius * T.exradius_b =
    T.side_a * T.side_b * T.side_c / (T.side_a - T.side_b + T.side_c) := by
  have hp : T.side_a - T.side_b + T.side_c ≠ 0 := ne_of_gt (pb_pos T)
  have hr : T.exradius_b = 2 * T.area / (T.side_a - T.side_b + T.side_c) := by
    unfold Triangle.exradius_b Triangle.semiperimeter
    have hp2 : (T.side_a + T.side_b + T.side_c) / 2 - T.side_b
        = (T.side_a - T.side_b + T.side_c) / 2 := by ring
    rw [hp2, div_div_eq_mul_div]
    ring
  rw [hr]
  rw [show 2 * T.circumradius * (2 * T.area / (T.side_a - T.side_b + T.side_c))
        = (4 * T.circumradius * T.area) / (T.side_a - T.side_b + T.side_c) from by ring]
  rw [FeuerbachEulerOI.four_R_area_eq_abc]

theorem two_R_rc_eq (T : Triangle) :
    2 * T.circumradius * T.exradius_c =
    T.side_a * T.side_b * T.side_c / (T.side_a + T.side_b - T.side_c) := by
  have hp : T.side_a + T.side_b - T.side_c ≠ 0 := ne_of_gt (pc_pos T)
  have hr : T.exradius_c = 2 * T.area / (T.side_a + T.side_b - T.side_c) := by
    unfold Triangle.exradius_c Triangle.semiperimeter
    have hp2 : (T.side_a + T.side_b + T.side_c) / 2 - T.side_c
        = (T.side_a + T.side_b - T.side_c) / 2 := by ring
    rw [hp2, div_div_eq_mul_div]
    ring
  rw [hr]
  rw [show 2 * T.circumradius * (2 * T.area / (T.side_a + T.side_b - T.side_c))
        = (4 * T.circumradius * T.area) / (T.side_a + T.side_b - T.side_c) from by ring]
  rw [FeuerbachEulerOI.four_R_area_eq_abc]

/-- **Euler's circumcentre–excentre formula** (opposite B):  OI_b² = R² + 2·R·r_b. -/
theorem euler_OI_b_formula (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_b =
    T.circumradius ^ 2 + 2 * T.circumradius * T.exradius_b := by
  rw [OI_b_sq_eq_R2_add T, two_R_rb_eq T, circumradius_sq T]

/-- **Euler's circumcentre–excentre formula** (opposite C):  OI_c² = R² + 2·R·r_c. -/
theorem euler_OI_c_formula (T : Triangle) :
    dist2_sq T.circumcenter T.excenter_c =
    T.circumradius ^ 2 + 2 * T.circumradius * T.exradius_c := by
  rw [OI_c_sq_eq_R2_add T, two_R_rc_eq T, circumradius_sq T]

-- ============================================================
-- PART 8: Strict consequence  —  R < OI_a
-- ============================================================

/-- The circumcentre is strictly farther from the A-excentre than the
    circumradius:  R² < OI_a².  Immediate from the *plus* sign in Euler's
    excentre formula together with R, r_a > 0. -/
theorem circumradius_sq_lt_OI_a_sq (T : Triangle) :
    T.circumradius ^ 2 < dist2_sq T.circumcenter T.excenter_a := by
  rw [euler_OI_a_formula T]
  have hR := circumradius_pos T
  have hra := exradius_a_pos T
  nlinarith [mul_pos hR hra]

/-- True-distance form:  R < OI_a. -/
theorem circumradius_lt_OI_a (T : Triangle) :
    T.circumradius < dist2 T.circumcenter T.excenter_a := by
  have h := circumradius_sq_lt_OI_a_sq T
  have hR := le_of_lt (circumradius_pos T)
  have hd : 0 ≤ dist2 T.circumcenter T.excenter_a := by unfold dist2; exact Real.sqrt_nonneg _
  have hsq : (dist2 T.circumcenter T.excenter_a) ^ 2 = dist2_sq T.circumcenter T.excenter_a := by
    unfold dist2 dist2_sq; rw [Real.sq_sqrt (by positivity)]
  nlinarith [h, hR, hd, hsq]

-- ============================================================
-- PART 9: Worked example — the 3-4-5 right triangle
-- ============================================================

/-- The A-excentre of the 3-4-5 triangle is (6, 6). -/
theorem triangle_345_excenter_a : triangle_345.excenter_a = (6, 6) := by
  unfold Triangle.excenter_a
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- The A-exradius of the 3-4-5 triangle is r_a = 6. -/
theorem triangle_345_exradius_a : triangle_345.exradius_a = 6 := by
  unfold Triangle.exradius_a
  rw [triangle_345_area, triangle_345_semiperimeter, triangle_345_side_a]
  norm_num

/-- For the 3-4-5 triangle, dist²(O, I_a) = 145/4, matching
    R² + 2Rr_a = (5/2)² + 2·(5/2)·6 = 145/4. -/
theorem triangle_345_OI_a_sq :
    dist2_sq triangle_345.circumcenter triangle_345.excenter_a = 145 / 4 := by
  rw [triangle_345_circumcenter, triangle_345_excenter_a]
  unfold dist2_sq
  norm_num

/-- The 3-4-5 triangle satisfies Euler's excentre formula concretely. -/
theorem triangle_345_euler_a :
    triangle_345.circumradius ^ 2
      + 2 * triangle_345.circumradius * triangle_345.exradius_a = 145 / 4 := by
  rw [triangle_345_circumradius, triangle_345_exradius_a]
  norm_num

end FeuerbachExcenterEuler
