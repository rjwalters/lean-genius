import Proofs.FeuerbachsTheorem

/-
# Feuerbach Distance Relations via Coordinate Computation (feuerbachs-theorem-oq-01)

## The Open Question

Can the Feuerbach distance relations (axioms in FeuerbachsTheorem.lean) be
proved by direct coordinate computation in ℝ²?

## What This File Proves

### Altitude Feet on Nine-Point Circle (3 axioms eliminated)
We prove foot_a/b/c_on_ninePointCircle by clearing denominators (field_simp + ring).

### Equilateral Triangle Special Case
R = 2r for equilateral triangles (circumradius = 2 × inradius).

### 3-4-5 Triangle Excircle Verification (NEW)
All three excircle tangency relations verified numerically:
- d(N, I_a) = R/2 + r_a = 29/4
- d(N, I_b) = R/2 + r_b = 17/4
- d(N, I_c) = R/2 + r_c = 13/4

### General Infrastructure (NEW)
- area_pos: Triangle area is positive
- semiperimeter_pos: Semiperimeter is positive
- inradius_pos: Inradius is positive

## Remaining Axioms (4)
The four Feuerbach distance axioms remain for the general case:
- feuerbach_incircle_distance: d(N,I) = |R/2 - r|
- feuerbach_excircle_a/b/c_distance: d(N,I_k) = R/2 + r_k

### Why the General Case is Hard
The incenter/excenter coordinates involve side lengths a,b,c = √(...).
After squaring both sides, cross terms a·b = √(a²·b²) remain irrational.
A general proof requires either:
(a) Polynomial identity modulo constraints a² = P_a(coords)
(b) Mathlib inner-product infrastructure
(c) Algebraic elimination of cross-terms
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ01

open Real FeuerbachsTheorem

-- ============================================================
-- Helper lemmas (needed because originals are private)
-- ============================================================

/-- Two nonneg reals with equal squares are equal. -/
private lemma eq_of_sq_eq_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with hab | hab
  · linarith
  · linarith

/-- dist2 is nonneg. -/
private lemma dist2_nonneg' (P Q : Point) : 0 ≤ dist2 P Q := by
  unfold dist2; exact Real.sqrt_nonneg _

/-- ninePointRadius is nonneg. -/
private lemma ninePointRadius_nonneg' (T : Triangle) : 0 ≤ T.ninePointRadius := by
  unfold Triangle.ninePointRadius
  exact div_nonneg (dist2_nonneg' _ _) (by norm_num)

/-- The circumcenter denominator is nonzero. -/
private lemma circ_denom_ne (T : Triangle) :
    2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2)) ≠ 0 := by
  intro h; apply T.nondegenerate; nlinarith

/-- |BC|² is positive for nondegenerate triangles. -/
private lemma bc_sq_ne (T : Triangle) :
    (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := by
  intro h
  have h1 : T.C.1 = T.B.1 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  have h2 : T.C.2 = T.B.2 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  apply T.nondegenerate; rw [h1, h2]; ring

/-- |CA|² is positive for nondegenerate triangles. -/
private lemma ca_sq_ne (T : Triangle) :
    (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := by
  intro h
  have h1 : T.A.1 = T.C.1 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  have h2 : T.A.2 = T.C.2 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  apply T.nondegenerate; rw [h1, h2]; ring

/-- |AB|² is positive for nondegenerate triangles. -/
private lemma ab_sq_ne (T : Triangle) :
    (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := by
  intro h
  have h1 : T.B.1 = T.A.1 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  have h2 : T.B.2 = T.A.2 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  apply T.nondegenerate; rw [h1, h2]; ring

-- ============================================================
-- FOOT A ON NINE-POINT CIRCLE
-- ============================================================

set_option maxHeartbeats 32000000 in
/-- The foot of altitude from A lies on the nine-point circle.
    Key identity: |foot_a - N|² = |O - A|²/4 = R²/4 = ninePointRadius².

    After unfolding, foot_a involves division by |BC|² and N involves
    division by the circumcenter denominator d. Clearing both denominators
    yields a polynomial identity. -/
theorem foot_a_on_ninePointCircle_proved (T : Triangle) :
    dist2 T.ninePointCenter T.foot_a = T.ninePointRadius := by
  apply eq_of_sq_eq_nonneg (dist2_nonneg' _ _) (ninePointRadius_nonneg' _)
  show dist2 T.ninePointCenter T.foot_a ^ 2 = T.ninePointRadius ^ 2
  unfold dist2 at *
  rw [Real.sq_sqrt (by positivity)]
  unfold Triangle.ninePointRadius Triangle.circumradius dist2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  -- Now goal: (foot_a - N)² = ((A - O)²) / 4
  unfold Triangle.foot_a Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  dsimp only
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  set bc2 := (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2
  have hd : d ≠ 0 := circ_denom_ne T
  have hbc : bc2 ≠ 0 := bc_sq_ne T
  field_simp
  ring

-- ============================================================
-- FOOT B ON NINE-POINT CIRCLE
-- ============================================================

set_option maxHeartbeats 32000000 in
/-- The foot of altitude from B lies on the nine-point circle. -/
theorem foot_b_on_ninePointCircle_proved (T : Triangle) :
    dist2 T.ninePointCenter T.foot_b = T.ninePointRadius := by
  apply eq_of_sq_eq_nonneg (dist2_nonneg' _ _) (ninePointRadius_nonneg' _)
  show dist2 T.ninePointCenter T.foot_b ^ 2 = T.ninePointRadius ^ 2
  unfold dist2 at *
  rw [Real.sq_sqrt (by positivity)]
  unfold Triangle.ninePointRadius Triangle.circumradius dist2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  unfold Triangle.foot_b Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  dsimp only
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  set ca2 := (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2
  have hd : d ≠ 0 := circ_denom_ne T
  have hca : ca2 ≠ 0 := ca_sq_ne T
  field_simp
  ring

-- ============================================================
-- FOOT C ON NINE-POINT CIRCLE
-- ============================================================

set_option maxHeartbeats 32000000 in
/-- The foot of altitude from C lies on the nine-point circle. -/
theorem foot_c_on_ninePointCircle_proved (T : Triangle) :
    dist2 T.ninePointCenter T.foot_c = T.ninePointRadius := by
  apply eq_of_sq_eq_nonneg (dist2_nonneg' _ _) (ninePointRadius_nonneg' _)
  show dist2 T.ninePointCenter T.foot_c ^ 2 = T.ninePointRadius ^ 2
  unfold dist2 at *
  rw [Real.sq_sqrt (by positivity)]
  unfold Triangle.ninePointRadius Triangle.circumradius dist2
  rw [div_pow, Real.sq_sqrt (by positivity)]
  unfold Triangle.foot_c Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  dsimp only
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  set ab2 := (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2
  have hd : d ≠ 0 := circ_denom_ne T
  have hab : ab2 ≠ 0 := ab_sq_ne T
  field_simp
  ring

-- ============================================================
-- EQUILATERAL TRIANGLE: R = 2r
-- ============================================================

/-- √3 squared is 3. -/
private lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)

/-- The equilateral triangle constructor. -/
private def equiT (s : ℝ) (hs : s > 0) : Triangle := {
  A := (0, 0)
  B := (s, 0)
  C := (s / 2, s * Real.sqrt 3 / 2)
  nondegenerate := by
    intro heq
    have : s * (s * Real.sqrt 3 / 2) > 0 := by positivity
    nlinarith
}

/-- Side a of equilateral triangle = s. -/
private lemma equi_side_a (s : ℝ) (hs : s > 0) : (equiT s hs).side_a = s := by
  unfold equiT Triangle.side_a; simp only
  have h : (s / 2 - s) ^ 2 + (s * Real.sqrt 3 / 2 - 0) ^ 2 = s ^ 2 := by
    have := sqrt3_sq; nlinarith
  rw [h, Real.sqrt_sq (le_of_lt hs)]

/-- Side b of equilateral triangle = s. -/
private lemma equi_side_b (s : ℝ) (hs : s > 0) : (equiT s hs).side_b = s := by
  unfold equiT Triangle.side_b; simp only
  have h : (0 - s / 2) ^ 2 + (0 - s * Real.sqrt 3 / 2) ^ 2 = s ^ 2 := by
    have := sqrt3_sq; nlinarith
  rw [h, Real.sqrt_sq (le_of_lt hs)]

/-- Side c of equilateral triangle = s. -/
private lemma equi_side_c (s : ℝ) (hs : s > 0) : (equiT s hs).side_c = s := by
  unfold equiT Triangle.side_c; simp only
  have h : (s - 0) ^ 2 + (0 - 0) ^ 2 = s ^ 2 := by ring
  rw [h, Real.sqrt_sq (le_of_lt hs)]

/-- Semiperimeter of equilateral triangle = 3s/2. -/
private lemma equi_semiperimeter (s : ℝ) (hs : s > 0) :
    (equiT s hs).semiperimeter = 3 * s / 2 := by
  unfold Triangle.semiperimeter
  rw [equi_side_a, equi_side_b, equi_side_c]; ring

/-- Area of equilateral triangle = s²√3/4. -/
private lemma equi_area (s : ℝ) (hs : s > 0) :
    (equiT s hs).area = s ^ 2 * Real.sqrt 3 / 4 := by
  unfold equiT Triangle.area; simp only
  have hpos : s * (s * Real.sqrt 3 / 2) > 0 := by positivity
  rw [show (s - 0) * (s * Real.sqrt 3 / 2 - 0) - (s / 2 - 0) * (0 - 0) =
      s * (s * Real.sqrt 3 / 2) from by ring]
  rw [abs_of_pos hpos]; ring

/-- Inradius of equilateral triangle = s√3/6. -/
private lemma equi_inradius (s : ℝ) (hs : s > 0) :
    (equiT s hs).inradius = s * Real.sqrt 3 / 6 := by
  unfold Triangle.inradius
  rw [equi_area, equi_semiperimeter]
  field_simp; ring

/-- Circumcenter x-coordinate of equilateral triangle = s/2.
    The √3 terms cancel identically (true for any value of √3). -/
private lemma equi_circumcenter_fst (s : ℝ) (hs : s > 0) :
    (equiT s hs).circumcenter.1 = s / 2 := by
  unfold equiT Triangle.circumcenter; simp only
  have hd : 2 * ((0 - s / 2) * (0 - s * Real.sqrt 3 / 2) -
      (s - s / 2) * (0 - s * Real.sqrt 3 / 2)) = s ^ 2 * Real.sqrt 3 := by ring
  have hd_ne : s ^ 2 * Real.sqrt 3 ≠ 0 := by positivity
  rw [hd]; field_simp [hd_ne, ne_of_gt hs]; ring

/-- Circumcenter y-coordinate of equilateral triangle = s√3/6.
    This requires (√3)² = 3 to verify. -/
private lemma equi_circumcenter_snd (s : ℝ) (hs : s > 0) :
    (equiT s hs).circumcenter.2 = s * Real.sqrt 3 / 6 := by
  unfold equiT Triangle.circumcenter; simp only
  have hd : 2 * ((0 - s / 2) * (0 - s * Real.sqrt 3 / 2) -
      (s - s / 2) * (0 - s * Real.sqrt 3 / 2)) = s ^ 2 * Real.sqrt 3 := by ring
  have hd_ne : s ^ 2 * Real.sqrt 3 ≠ 0 := by positivity
  have hsqrt3_ne : Real.sqrt 3 ≠ 0 := by positivity
  rw [hd]; field_simp [hd_ne, ne_of_gt hs, hsqrt3_ne]
  have h3 : Real.sqrt 3 ^ 2 = 3 := sqrt3_sq
  have h_key : s ^ 2 * Real.sqrt 3 ^ 2 = 3 * s ^ 2 := by nlinarith
  nlinarith [h_key, sq_nonneg s, sq_nonneg (Real.sqrt 3), sq_nonneg (s * Real.sqrt 3)]

set_option maxHeartbeats 16000000 in
/-- R = 2r for equilateral triangle (circumradius = 2 × inradius).
    Proof: compute circumcenter = (s/2, s√3/6), then show
    circumradius² = s²/4 + s²·3/36 = s²/3 = (2·inradius)². -/
theorem equilateral_R_eq_2r_proved (s : ℝ) (hs : s > 0) :
    (equiT s hs).circumradius = 2 * (equiT s hs).inradius := by
  have hR_nonneg : 0 ≤ (equiT s hs).circumradius := dist2_nonneg' _ _
  have hr_nonneg : 0 ≤ 2 * (equiT s hs).inradius := by rw [equi_inradius]; positivity
  apply eq_of_sq_eq_nonneg hR_nonneg hr_nonneg
  -- Expand circumradius² = (A.1-O.1)² + (A.2-O.2)²
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity)]
  -- Substitute known values: A = (0,0), O = (s/2, s√3/6)
  rw [show ((equiT s hs).A.1 - (equiT s hs).circumcenter.1) ^ 2 +
      ((equiT s hs).A.2 - (equiT s hs).circumcenter.2) ^ 2 =
      (0 - s / 2) ^ 2 + (0 - s * Real.sqrt 3 / 6) ^ 2
    from by rw [show (equiT s hs).A.1 = (0 : ℝ) from rfl,
                show (equiT s hs).A.2 = (0 : ℝ) from rfl,
                equi_circumcenter_fst s hs, equi_circumcenter_snd s hs]]
  rw [equi_inradius]
  nlinarith [sqrt3_sq, sq_nonneg s, sq_nonneg (Real.sqrt 3)]

-- ============================================================
-- 3-4-5 TRIANGLE: EXCIRCLE DISTANCE VERIFICATION
-- ============================================================

-- We verify Feuerbach's excircle tangency for the 3-4-5 right triangle.
-- For this triangle: R = 5/2, r_a = area/(s-a) = 6/1 = 6,
--   r_b = area/(s-b) = 6/2 = 3, r_c = area/(s-c) = 6/3 = 2.
-- Nine-point radius = R/2 = 5/4.
-- Excircle tangency: d(N, I_k) = R/2 + r_k for each excircle.

open FeuerbachsTheorem

-- Side length helpers (re-proved since originals are private in main file)
private lemma T345_side_a : triangle_345.side_a = 5 := by
  unfold triangle_345 Triangle.side_a; simp only
  have : ((0 : ℝ) - 3) ^ 2 + (4 - 0) ^ 2 = 5 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (5 : ℝ) ≥ 0)]

private lemma T345_side_b : triangle_345.side_b = 4 := by
  unfold triangle_345 Triangle.side_b; simp only
  have : ((0 : ℝ) - 0) ^ 2 + (0 - 4) ^ 2 = 4 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (4 : ℝ) ≥ 0)]

private lemma T345_side_c : triangle_345.side_c = 3 := by
  unfold triangle_345 Triangle.side_c; simp only
  have : ((3 : ℝ) - 0) ^ 2 + (0 - 0) ^ 2 = 3 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]

/-- Excenter opposite A for 3-4-5 triangle.
    I_a = (-a*Ax + b*Bx + c*Cx)/(-a+b+c) with a=5,b=4,c=3,
    = (-5·0 + 4·3 + 3·0)/(-5+4+3), (-5·0 + 4·0 + 3·4)/(-5+4+3)
    = (12/2, 12/2) = (6, 6) -/
private lemma T345_excenter_a : triangle_345.excenter_a = (6, 6) := by
  unfold Triangle.excenter_a
  simp only [T345_side_a, T345_side_b, T345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- Exradius opposite A for 3-4-5 triangle: r_a = area/(s-a) = 6/1 = 6 -/
private lemma T345_exradius_a : triangle_345.exradius_a = 6 := by
  unfold Triangle.exradius_a
  rw [triangle_345_area, triangle_345_semiperimeter]
  simp only [T345_side_a]
  norm_num

/-- Excircle A tangency verified for 3-4-5 triangle:
    d(N, I_a) = √((6-3/4)² + (6-1)²) = √(441/16 + 25) = √(841/16) = 29/4
    R/2 + r_a = 5/4 + 6 = 29/4 ✓ -/
theorem T345_feuerbach_excircle_a :
    dist2 triangle_345.ninePointCenter triangle_345.excenter_a =
    triangle_345.ninePointRadius + triangle_345.exradius_a := by
  rw [triangle_345_ninePointCenter, T345_excenter_a,
      triangle_345_ninePointRadius, T345_exradius_a]
  unfold dist2; simp only
  have hlhs : ((6 : ℝ) - 3/4) ^ 2 + (6 - 1) ^ 2 = (29/4) ^ 2 := by norm_num
  rw [hlhs, Real.sqrt_sq (by norm_num : (29/4 : ℝ) ≥ 0)]
  norm_num

/-- Excenter opposite B for 3-4-5 triangle:
    I_b = (a*Ax - b*Bx + c*Cx)/(a-b+c) = (5·0 - 4·3 + 3·0)/4 = -3
    I_b_y = (5·0 - 4·0 + 3·4)/4 = 3.  So I_b = (-3, 3). -/
private lemma T345_excenter_b : triangle_345.excenter_b = (-3, 3) := by
  unfold Triangle.excenter_b
  simp only [T345_side_a, T345_side_b, T345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- Exradius opposite B: r_b = area/(s-b) = 6/2 = 3 -/
private lemma T345_exradius_b : triangle_345.exradius_b = 3 := by
  unfold Triangle.exradius_b
  rw [triangle_345_area, triangle_345_semiperimeter, T345_side_b]
  norm_num

/-- Excircle B tangency verified for 3-4-5 triangle:
    d(N, I_b) = √((-3-3/4)² + (3-1)²) = √(225/16 + 4) = √(289/16) = 17/4
    R/2 + r_b = 5/4 + 3 = 17/4 ✓ -/
theorem T345_feuerbach_excircle_b :
    dist2 triangle_345.ninePointCenter triangle_345.excenter_b =
    triangle_345.ninePointRadius + triangle_345.exradius_b := by
  rw [triangle_345_ninePointCenter, T345_excenter_b,
      triangle_345_ninePointRadius, T345_exradius_b]
  unfold dist2; simp only
  have hlhs : ((-3 : ℝ) - 3/4) ^ 2 + (3 - 1) ^ 2 = (17/4) ^ 2 := by norm_num
  rw [hlhs, Real.sqrt_sq (by norm_num : (17/4 : ℝ) ≥ 0)]
  norm_num

/-- Excenter opposite C for 3-4-5 triangle:
    I_c = (a*Ax + b*Bx - c*Cx)/(a+b-c) = (5·0 + 4·3 - 3·0)/(5+4-3) = 12/6 = 2
    I_c_y = (5·0 + 4·0 - 3·4)/(5+4-3) = -12/6 = -2
    So I_c = (2, -2) -/
private lemma T345_excenter_c : triangle_345.excenter_c = (2, -2) := by
  unfold Triangle.excenter_c
  simp only [T345_side_a, T345_side_b, T345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- Exradius opposite C: r_c = area/(s-c) = 6/3 = 2 -/
private lemma T345_exradius_c : triangle_345.exradius_c = 2 := by
  unfold Triangle.exradius_c
  rw [triangle_345_area, triangle_345_semiperimeter, T345_side_c]
  norm_num

/-- Excircle C tangency verified for 3-4-5 triangle:
    d(N, I_c) = √((2-3/4)² + (-2-1)²) = √(25/16 + 9) = √(169/16) = 13/4
    R/2 + r_c = 5/4 + 2 = 13/4 ✓ -/
theorem T345_feuerbach_excircle_c :
    dist2 triangle_345.ninePointCenter triangle_345.excenter_c =
    triangle_345.ninePointRadius + triangle_345.exradius_c := by
  rw [triangle_345_ninePointCenter, T345_excenter_c,
      triangle_345_ninePointRadius, T345_exradius_c]
  unfold dist2; simp only
  have hlhs : ((2 : ℝ) - 3/4) ^ 2 + ((-2 : ℝ) - 1) ^ 2 = (13/4) ^ 2 := by norm_num
  rw [hlhs, Real.sqrt_sq (by norm_num : (13/4 : ℝ) ≥ 0)]
  norm_num

-- ============================================================
-- GENERAL INFRASTRUCTURE: Euler's Formula OI² = R² - 2Rr
-- ============================================================

-- The classical approach to Feuerbach uses Euler's formula for the
-- distance from circumcenter O to incenter I:
--   OI² = R² - 2Rr
-- and the nine-point variant:
--   NI = R/2 - r  (Feuerbach's theorem for incircle)
--
-- The key algebraic obstacle for the GENERAL proof in coordinates:
-- The incenter coordinates involve side lengths a, b, c which are
-- square roots. Products like a·b cannot be simplified by `ring`.
-- A full general proof would require either:
--   (a) Working with squared expressions and proving auxiliary polynomial
--       identities modulo constraints a² = P_a(coords), etc.
--   (b) Using Mathlib's inner product / norm infrastructure instead
--       of our custom coordinate geometry
--   (c) An algebraic simplification that eliminates all cross-terms

-- For now we prove key supporting results and verify numerically.

/-- The area of a nondegenerate triangle is positive. -/
theorem area_pos (T : Triangle) : T.area > 0 := by
  unfold Triangle.area
  have h := T.nondegenerate
  have : (T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2) ≠ 0 := by
    intro heq; exact h heq
  exact div_pos (abs_pos.mpr this) (by norm_num : (0 : ℝ) < 2)

/-- The semiperimeter is positive. -/
theorem semiperimeter_pos (T : Triangle) : T.semiperimeter > 0 := by
  unfold Triangle.semiperimeter Triangle.side_a Triangle.side_b Triangle.side_c
  have ha : 0 ≤ Real.sqrt ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2) := Real.sqrt_nonneg _
  have hc : 0 ≤ Real.sqrt ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2) := Real.sqrt_nonneg _
  -- At least one side has positive length (since triangle is nondegenerate)
  -- Side c = |AB| > 0 because if A=B then cross product simplifies
  have hc_pos : 0 < Real.sqrt ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2) := by
    apply Real.sqrt_pos_of_pos
    by_contra h
    push_neg at h
    have hx : T.B.1 = T.A.1 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
    have hy : T.B.2 = T.A.2 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
    exact T.nondegenerate (by rw [hx, hy]; ring)
  linarith

/-- The inradius is positive. -/
theorem inradius_pos (T : Triangle) : T.inradius > 0 := by
  unfold Triangle.inradius
  exact div_pos (area_pos T) (semiperimeter_pos T)

-- Type-check results
#check @foot_a_on_ninePointCircle_proved
#check @foot_b_on_ninePointCircle_proved
#check @foot_c_on_ninePointCircle_proved
#check @equilateral_R_eq_2r_proved
#check @T345_feuerbach_excircle_a
#check @T345_feuerbach_excircle_b
#check @T345_feuerbach_excircle_c
#check @area_pos
#check @semiperimeter_pos
#check @inradius_pos

end FeuerbachsTheoremOQ01
