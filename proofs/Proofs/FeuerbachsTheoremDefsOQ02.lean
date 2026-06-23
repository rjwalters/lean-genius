/-
  Feuerbach's Theorem DefsOQ02: Euler's Triangle Formula  OI² = R² − 2Rr

  ## The Open Question

  The parent file `FeuerbachsTheoremDefs` defines the circumcenter O, the incenter
  I, the circumradius R and the inradius r of a triangle, and proves the
  nine-point circle / Feuerbach tangency results.  It never relates the two centers
  O and I to each other metrically.

  The single most famous such relation is **Euler's formula** (Leonhard Euler,
  1765):

      OI² = R² − 2Rr,

  i.e. the squared distance between the circumcenter and the incenter equals
  R(R − 2r).  Because a squared distance is non-negative this *forces*

      R ≥ 2r          (Euler's inequality),

  with equality iff O = I iff the triangle is equilateral.

  ## What This File Proves

  For an arbitrary non-degenerate triangle T (working purely in coordinates):

  ### The affine core
  `OI_sq_eq_R2_sub` :  dist²(O, I) = R² − abc/(a+b+c).
  This is the heart of the matter.  With O placed at the origin, the incenter is
  the side-length-weighted average I = (a·A + b·B + c·C)/(a+b+c), and the three
  circumcentre equidistances |A−O| = |B−O| = |C−O| = R collapse the expansion of
  |I−O|² to R² − abc/(a+b+c).  No square roots are needed for this step.

  ### The law-of-sines bridge
  `four_R_area_eq_abc` :  4·R·Area = abc      (squared form 16·R²·Area² = a²b²c²).
  `two_R_r_eq` :  2·R·r = abc/(a+b+c).
  Combining R = abc/(4·Area) with r = Area/s turns abc/(a+b+c) into 2Rr.

  ### Euler's formula and inequality
  `euler_OI_formula` :  dist²(O, I) = R² − 2·R·r.
  `euler_inequality` :  2·r ≤ R.

  ### Example
  `triangle_345_OI_sq` :  for the 3-4-5 triangle, dist²(O, I) = 5/4
  (and indeed R² − 2Rr = (5/2)² − 2·(5/2)·1 = 5/4).

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachEulerOI

open FeuerbachsTheorem
open scoped Real

-- ============================================================
-- PART 1: Local circumcentre equidistance (the parent's are private)
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
-- PART 2: Side lengths are positive; squared side lengths
-- ============================================================

/-- The squared side length a² equals the squared distance |BC|². -/
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

/-- Each side length is strictly positive. -/
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
-- PART 3: The affine core  —  OI² = R² − abc/(a+b+c)
-- ============================================================

/-- The master algebraic identity.  With a = side_a, b = side_b, c = side_c and
    R² = |A − O|², the weighted vector  a(A−O) + b(B−O) + c(C−O)  has squared
    length  R²(a+b+c)² − abc(a+b+c).  This is the heart of Euler's formula. -/
private lemma weighted_norm_sq (T : Triangle) :
    (T.side_a * (T.A.1 - T.circumcenter.1) + T.side_b * (T.B.1 - T.circumcenter.1)
        + T.side_c * (T.C.1 - T.circumcenter.1)) ^ 2 +
    (T.side_a * (T.A.2 - T.circumcenter.2) + T.side_b * (T.B.2 - T.circumcenter.2)
        + T.side_c * (T.C.2 - T.circumcenter.2)) ^ 2 =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
        * (T.side_a + T.side_b + T.side_c) ^ 2 -
    T.side_a * T.side_b * T.side_c * (T.side_a + T.side_b + T.side_c) := by
  set O := T.circumcenter
  -- R² abbreviation
  set R2 := (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 with hR2
  -- equidistances as "= R2"
  have e1 : (T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2 = R2 := rfl
  have e2 : (T.B.1 - O.1) ^ 2 + (T.B.2 - O.2) ^ 2 = R2 := by rw [hR2]; exact equidist_B T
  have e3 : (T.C.1 - O.1) ^ 2 + (T.C.2 - O.2) ^ 2 = R2 := by rw [hR2]; exact equidist_C T
  -- dot products expressed via the side lengths
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
    T.side_a ^ 2 * e1 + T.side_b ^ 2 * e2 + T.side_c ^ 2 * e3
    + 2 * T.side_a * T.side_b * dotAB + 2 * T.side_b * T.side_c * dotBC
    + 2 * T.side_c * T.side_a * dotCA

/-- The affine core of Euler's formula:
    dist²(O, I) = R² − abc/(a+b+c), with no square roots involved. -/
theorem OI_sq_eq_R2_sub (T : Triangle) :
    dist2_sq T.circumcenter T.incenter =
    ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
      - T.side_a * T.side_b * T.side_c / (T.side_a + T.side_b + T.side_c) := by
  set O := T.circumcenter with hO
  have hp : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  -- incenter coordinates: I − O written over the common denominator
  have hI : dist2_sq O T.incenter * (T.side_a + T.side_b + T.side_c) ^ 2 =
      (T.side_a * (T.A.1 - O.1) + T.side_b * (T.B.1 - O.1) + T.side_c * (T.C.1 - O.1)) ^ 2 +
      (T.side_a * (T.A.2 - O.2) + T.side_b * (T.B.2 - O.2) + T.side_c * (T.C.2 - O.2)) ^ 2 := by
    unfold dist2_sq Triangle.incenter
    dsimp only
    field_simp [hp]
    ring
  -- substitute the master identity
  have hmaster := weighted_norm_sq T
  rw [← hO] at hmaster
  rw [hmaster] at hI
  -- hI : dist²(O,I)·(a+b+c)² = R2·(a+b+c)² − abc·(a+b+c)
  -- cancel one factor of (a+b+c)
  have hkey : dist2_sq O T.incenter * (T.side_a + T.side_b + T.side_c) =
      ((T.A.1 - O.1) ^ 2 + (T.A.2 - O.2) ^ 2) * (T.side_a + T.side_b + T.side_c)
        - T.side_a * T.side_b * T.side_c := by
    apply mul_right_cancel₀ hp
    linear_combination hI
  field_simp [hp]
  linear_combination hkey

-- ============================================================
-- PART 4: Law-of-sines bridge  —  4·R·Area = abc
-- ============================================================

set_option maxHeartbeats 12000000 in
/-- The squared law-of-sines/area identity:  16·R²·Area² = a²·b²·c²,
    expressed in coordinates (R² = |A − O|²). -/
private lemma sixteen_R2_area_sq (T : Triangle) :
    16 * ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
        * T.area ^ 2 =
    ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2) *
    ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2) *
    ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2) := by
  have harea : T.area ^ 2 =
      ((T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) ^ 2 / 4 := by
    unfold Triangle.area
    rw [div_pow, sq_abs]
    ring
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2)) with hd_def
  have hd : d ≠ 0 := circumcenter_denom_ne_zero T
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [harea, hox, hoy]
  field_simp [hd]
  ring

/-- R² = |A − O|² (circumradius squared, dropping the square root). -/
private lemma circumradius_sq (T : Triangle) :
    T.circumradius ^ 2 = (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity)]

/-- R² > 0. -/
private lemma circumradius_sq_pos (T : Triangle) :
    0 < (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := sixteen_R2_area_sq T
  have hA := area_pos T
  have hca : 0 < (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 := by
    have h1 := side_a_sq T; have h2 := pow_pos (side_a_pos T) 2; linarith
  have hab : 0 < (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 := by
    have h1 := side_b_sq T; have h2 := pow_pos (side_b_pos T) 2; linarith
  have hbc : 0 < (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 := by
    have h1 := side_c_sq T; have h2 := pow_pos (side_c_pos T) 2; linarith
  nlinarith [h, mul_pos (mul_pos hca hab) hbc, pow_pos hA 2]

/-- Circumradius is positive. -/
private lemma circumradius_pos (T : Triangle) : 0 < T.circumradius := by
  unfold Triangle.circumradius dist2
  exact Real.sqrt_pos.mpr (circumradius_sq_pos T)

/-- Law of sines (area form):  4·R·Area = abc. -/
theorem four_R_area_eq_abc (T : Triangle) :
    4 * T.circumradius * T.area = T.side_a * T.side_b * T.side_c := by
  have habc_nn : 0 ≤ T.side_a * T.side_b * T.side_c :=
    mul_nonneg (mul_nonneg (side_a_nonneg T) (side_b_nonneg T)) (side_c_nonneg T)
  have hA_nn : 0 ≤ T.area := le_of_lt (area_pos T)
  -- (abc)² = 16·Area²·R²  via the coordinate identity and the squared side lengths
  have hsq : (T.side_a * T.side_b * T.side_c) ^ 2 =
      16 * ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2) * T.area ^ 2 := by
    rw [mul_pow, mul_pow, side_a_sq, side_b_sq, side_c_sq]
    linear_combination -(sixteen_R2_area_sq T)
  -- take square roots
  have key : T.side_a * T.side_b * T.side_c =
      4 * T.area * Real.sqrt ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2) := by
    have h1 : T.side_a * T.side_b * T.side_c
        = Real.sqrt ((T.side_a * T.side_b * T.side_c) ^ 2) := (Real.sqrt_sq habc_nn).symm
    rw [h1, hsq]
    rw [show 16 * ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2) * T.area ^ 2
          = (4 * T.area) ^ 2 * ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2)
          from by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by linarith [hA_nn])]
  rw [key]
  unfold Triangle.circumradius dist2
  ring

-- ============================================================
-- PART 5: Euler's formula and inequality
-- ============================================================

/-- 2·R·r = abc/(a+b+c). -/
theorem two_R_r_eq (T : Triangle) :
    2 * T.circumradius * T.inradius =
    T.side_a * T.side_b * T.side_c / (T.side_a + T.side_b + T.side_c) := by
  have hp : T.side_a + T.side_b + T.side_c ≠ 0 := ne_of_gt (perimeter_pos T)
  have hr : T.inradius = 2 * T.area / (T.side_a + T.side_b + T.side_c) := by
    unfold Triangle.inradius Triangle.semiperimeter
    rw [div_div_eq_mul_div]
    ring
  rw [hr]
  rw [show 2 * T.circumradius * (2 * T.area / (T.side_a + T.side_b + T.side_c))
        = (4 * T.circumradius * T.area) / (T.side_a + T.side_b + T.side_c) from by ring]
  rw [four_R_area_eq_abc]

/-- **Euler's triangle formula** (Euler, 1765):
    the squared distance between the circumcentre and incentre is R² − 2Rr. -/
theorem euler_OI_formula (T : Triangle) :
    dist2_sq T.circumcenter T.incenter =
    T.circumradius ^ 2 - 2 * T.circumradius * T.inradius := by
  rw [OI_sq_eq_R2_sub T, two_R_r_eq T, circumradius_sq T]

/-- **Euler's inequality**:  R ≥ 2r, with the circumradius at least twice the
    inradius.  Immediate from `euler_OI_formula` and the non-negativity of OI². -/
theorem euler_inequality (T : Triangle) : 2 * T.inradius ≤ T.circumradius := by
  have hOI : 0 ≤ dist2_sq T.circumcenter T.incenter := dist2_sq_nonneg _ _
  rw [euler_OI_formula T] at hOI
  have hR : 0 < T.circumradius := circumradius_pos T
  nlinarith [hOI, hR]

-- ============================================================
-- PART 6: Worked example — the 3-4-5 right triangle
-- ============================================================

/-- For the 3-4-5 triangle, dist²(O, I) = 5/4, matching
    R² − 2Rr = (5/2)² − 2·(5/2)·1 = 5/4. -/
theorem triangle_345_OI_sq :
    dist2_sq triangle_345.circumcenter triangle_345.incenter = 5 / 4 := by
  rw [triangle_345_circumcenter, triangle_345_incenter]
  unfold dist2_sq
  norm_num

/-- The 3-4-5 triangle satisfies Euler's formula concretely. -/
theorem triangle_345_euler :
    triangle_345.circumradius ^ 2 - 2 * triangle_345.circumradius * triangle_345.inradius
      = 5 / 4 := by
  rw [triangle_345_circumradius, triangle_345_inradius]
  norm_num

end FeuerbachEulerOI
