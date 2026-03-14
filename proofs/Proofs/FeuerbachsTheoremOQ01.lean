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

-- ============================================================
-- KEY ALGEBRAIC IDENTITY: SIGMA = abcs - 4·Area²
-- ============================================================

-- This is the core identity needed for the general Feuerbach proof.
-- It relates the "sigma" expression Σ = (s-a)(s-b)c² + ... to abc·s - 4·Area²
-- where Area² = s(s-a)(s-b)(s-c) by Heron's formula.
--
-- This identity is purely algebraic in a, b, c (no coordinates needed).

/-- The sigma identity: for positive reals a, b, c with s = (a+b+c)/2,
    (s-a)(s-b)c² + (s-a)(s-c)b² + (s-b)(s-c)a² = abcs - 4s(s-a)(s-b)(s-c).

    This is a key step in deriving Feuerbach's theorem from Euler's formula. -/
theorem sigma_identity (a b c : ℝ) :
    let s := (a + b + c) / 2
    (s - a) * (s - b) * c ^ 2 + (s - a) * (s - c) * b ^ 2 + (s - b) * (s - c) * a ^ 2 =
    a * b * c * s - 4 * s * (s - a) * (s - b) * (s - c) := by
  simp only
  ring

-- ============================================================
-- EXTENDED LAW OF SINES (SQUARED FORM)
-- ============================================================

-- The extended law of sines: a·b·c = 4·R·Area, or equivalently
-- a²·b²·c² = 16·R²·Area².
--
-- This is a polynomial identity in coordinates after clearing the
-- circumcenter denominator and using a² = (C.1-B.1)²+(C.2-B.2)² etc.

set_option maxHeartbeats 64000000 in
/-- The extended law of sines (squared form):
    side_a² · side_b² · side_c² = 16 · circumradius² · area².

    Proof: After squaring to eliminate sqrt, clearing the circumcenter
    denominator, and unfolding all definitions, this reduces to a
    polynomial identity in the 6 vertex coordinates.

    Key step: area² = (signed_area)² since |x|² = x². -/
theorem extended_law_of_sines_sq (T : Triangle) :
    T.side_a ^ 2 * T.side_b ^ 2 * T.side_c ^ 2 =
    16 * T.circumradius ^ 2 * T.area ^ 2 := by
  unfold Triangle.side_a Triangle.side_b Triangle.side_c
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  unfold Triangle.circumcenter Triangle.area
  dsimp only
  -- Eliminate |x|² = x² (abs squared = squared)
  rw [div_pow, sq_abs]
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd : d ≠ 0 := circ_denom_ne T
  field_simp
  ring

-- ============================================================
-- EULER'S FORMULA OI² = R² - 2Rr (3-4-5 VERIFICATION)
-- ============================================================

/-- Euler's formula for the 3-4-5 triangle:
    OI² = R² - 2Rr = (5/2)² - 2·(5/2)·1 = 25/4 - 5 = 5/4.

    Direct computation: O = (3/2, 2), I = (1, 1).
    OI² = (3/2-1)² + (2-1)² = 1/4 + 1 = 5/4.
    R² - 2Rr = 25/4 - 5 = 5/4. ✓ -/
theorem T345_euler_formula :
    dist2_sq triangle_345.circumcenter triangle_345.incenter =
    triangle_345.circumradius ^ 2 - 2 * triangle_345.circumradius * triangle_345.inradius := by
  rw [triangle_345_circumcenter, triangle_345_incenter,
      triangle_345_circumradius, triangle_345_inradius]
  unfold dist2_sq; simp only
  norm_num

/-- For the 3-4-5 triangle, the extended law of sines holds:
    abc = 4R·Area, i.e., 5·4·3 = 4·(5/2)·6. (60 = 60) -/
theorem T345_extended_law_of_sines :
    triangle_345.side_a * triangle_345.side_b * triangle_345.side_c =
    4 * triangle_345.circumradius * triangle_345.area := by
  rw [T345_side_a, T345_side_b, T345_side_c,
      triangle_345_circumradius, triangle_345_area]
  norm_num

-- ============================================================
-- ROADMAP: GENERAL FEUERBACH PROOF PATH
-- ============================================================

/-
The general Feuerbach proof (NI = |R/2 - r|) follows this chain:

1. Extended law of sines (squared): a²b²c² = 16·R²·Area² [PROVED above]
2. Sigma identity: Σ = abcs - 4s(s-a)(s-b)(s-c) [PROVED above]
3. Euler's formula: OI² = R² - 2Rr
4. Nine-point reduction: NI² = R²/4 - Rr + r² = (R/2 - r)²
5. Take sqrt: NI = |R/2 - r|

The FUNDAMENTAL OBSTACLE for steps 3-4 is that the incenter
coordinates involve side_a, side_b, side_c which are √(polynomial).
Products like side_a · side_b cannot be simplified by `ring`.

Possible approaches to overcome this:
(a) Reformulate incenter using squared-distance characterization
(b) Use Mathlib's EuclideanGeometry inner product infrastructure
(c) Implement algebraic elimination of cross-terms √(a²b²)
(d) Work in complex coordinates where the algebra is cleaner

The squared extended law of sines and sigma identity are the algebraic
backbone needed for any of these approaches.
-/

-- ============================================================
-- HERON'S FORMULA (SQUARED POLYNOMIAL FORM)
-- ============================================================

-- Heron's formula in its squared form avoids all square roots:
--   16·Area² = 2a²b² + 2b²c² + 2c²a² - a⁴ - b⁴ - c⁴
--
-- This is equivalent to: 16·Area² = (a+b+c)(-a+b+c)(a-b+c)(a+b-c)
-- but expressed entirely in terms of a², b², c² (polynomial in coordinates).

set_option maxHeartbeats 64000000 in
/-- Heron's formula (squared polynomial form):
    16 · Area² = 2·a²·b² + 2·b²·c² + 2·c²·a² - a⁴ - b⁴ - c⁴

    After substituting a² = |BC|², b² = |CA|², c² = |AB|² and
    Area = |signed_area|/2, this reduces to a polynomial identity
    in the 6 vertex coordinates, provable by ring. -/
theorem herons_formula_sq (T : Triangle) :
    16 * T.area ^ 2 =
    2 * T.side_a ^ 2 * T.side_b ^ 2 +
    2 * T.side_b ^ 2 * T.side_c ^ 2 +
    2 * T.side_c ^ 2 * T.side_a ^ 2 -
    T.side_a ^ 4 - T.side_b ^ 4 - T.side_c ^ 4 := by
  unfold Triangle.area Triangle.side_a Triangle.side_b Triangle.side_c
  rw [div_pow, sq_abs]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  -- Now a⁴ = (a²)² etc., just square the squared expressions
  ring

-- ============================================================
-- DOT PRODUCT AND INNER PRODUCT LEMMAS
-- ============================================================

/-- Dot product of 2D vectors (A-O) and (B-O). -/
def dot2 (P Q R : Point) : ℝ :=
  (P.1 - R.1) * (Q.1 - R.1) + (P.2 - R.2) * (Q.2 - R.2)

/-- Polarization identity: ⟨A-O, B-O⟩ = (|A-O|² + |B-O|² - |A-B|²)/2.
    This is a standard identity requiring no special properties of O. -/
theorem dot2_polarization (A B O : Point) :
    dot2 A B O = (dist2_sq O A + dist2_sq O B - dist2_sq A B) / 2 := by
  unfold dot2 dist2_sq
  ring

/-- For the circumcenter O with |O-A|² = |O-B|² = R²:
    ⟨A-O, B-O⟩ = R² - c²/2 where c = |AB|.

    This is the key inner product identity used in the abstract
    Feuerbach proof. -/
theorem dot_circumcenter_AB (T : Triangle) :
    dot2 T.A T.B T.circumcenter =
    T.circumradius ^ 2 - T.side_c ^ 2 / 2 := by
  rw [dot2_polarization]
  have heq : dist2_sq T.circumcenter T.B = dist2_sq T.circumcenter T.A :=
    circumcenter_equidist_sq_B T
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  unfold Triangle.side_c
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  rw [heq]
  ring

/-- ⟨A-O, C-O⟩ = R² - b²/2 where b = |CA|. -/
theorem dot_circumcenter_AC (T : Triangle) :
    dot2 T.A T.C T.circumcenter =
    T.circumradius ^ 2 - T.side_b ^ 2 / 2 := by
  rw [dot2_polarization]
  have heq : dist2_sq T.circumcenter T.C = dist2_sq T.circumcenter T.A :=
    circumcenter_equidist_sq_C T
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  unfold Triangle.side_b
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  rw [heq]
  ring

/-- ⟨B-O, C-O⟩ = R² - a²/2 where a = |BC|. -/
theorem dot_circumcenter_BC (T : Triangle) :
    dot2 T.B T.C T.circumcenter =
    T.circumradius ^ 2 - T.side_a ^ 2 / 2 := by
  rw [dot2_polarization]
  have heqB : dist2_sq T.circumcenter T.B = dist2_sq T.circumcenter T.A :=
    circumcenter_equidist_sq_B T
  have heqC : dist2_sq T.circumcenter T.C = dist2_sq T.circumcenter T.A :=
    circumcenter_equidist_sq_C T
  unfold Triangle.circumradius dist2
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  unfold Triangle.side_a
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ _)]
  rw [heqB, heqC]
  ring

-- ============================================================
-- EXTENDED LAW OF SINES (UNSQUARED FORM)
-- ============================================================

/-- Side lengths are positive for nondegenerate triangles. -/
theorem side_a_pos (T : Triangle) : T.side_a > 0 := by
  unfold Triangle.side_a
  apply Real.sqrt_pos_of_pos
  exact_mod_cast (by
    have := bc_sq_ne T
    positivity : (0 : ℝ) < (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)

theorem side_b_pos (T : Triangle) : T.side_b > 0 := by
  unfold Triangle.side_b
  apply Real.sqrt_pos_of_pos
  exact_mod_cast (by
    have := ca_sq_ne T
    positivity : (0 : ℝ) < (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)

theorem side_c_pos (T : Triangle) : T.side_c > 0 := by
  unfold Triangle.side_c
  apply Real.sqrt_pos_of_pos
  exact_mod_cast (by
    have := ab_sq_ne T
    positivity : (0 : ℝ) < (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)

/-- The circumradius is positive. -/
theorem circumradius_pos (T : Triangle) : T.circumradius > 0 := by
  -- R = |O - A| > 0. Since O ≠ A (otherwise all vertices equidistant from A
  -- would force collinearity).
  unfold Triangle.circumradius dist2
  apply Real.sqrt_pos_of_pos
  -- Need (A.1 - O.1)² + (A.2 - O.2)² > 0, i.e., A ≠ O
  by_contra h
  push_neg at h
  have hx : T.A.1 = T.circumcenter.1 := by nlinarith [sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]
  have hy : T.A.2 = T.circumcenter.2 := by nlinarith [sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]
  -- If A = O, then |O-A|² = 0 = R², so |O-B|² = 0 and |O-C|² = 0
  -- meaning B = O = A and C = O = A, contradicting nondegeneracy
  have hOA : dist2_sq T.circumcenter T.A = 0 := by unfold dist2_sq; rw [hx, hy]; ring
  have hOB : dist2_sq T.circumcenter T.B = 0 := by
    rw [circumcenter_equidist_sq_B T]; exact hOA
  have hOC : dist2_sq T.circumcenter T.C = 0 := by
    rw [circumcenter_equidist_sq_C T]; exact hOA
  have hBx : T.B.1 = T.A.1 := by
    unfold dist2_sq at hOB; rw [hx, hy] at hOB
    nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  have hBy : T.B.2 = T.A.2 := by
    unfold dist2_sq at hOB; rw [hx, hy] at hOB
    nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  exact T.nondegenerate (by rw [hBx, hBy]; ring)

/-- Extended law of sines (unsquared form):
    side_a · side_b · side_c = 4 · circumradius · area.

    Derived from the squared version by taking positive square roots. -/
theorem extended_law_of_sines (T : Triangle) :
    T.side_a * T.side_b * T.side_c = 4 * T.circumradius * T.area := by
  have hsq := extended_law_of_sines_sq T
  -- Both sides are positive
  have hlhs_pos : T.side_a * T.side_b * T.side_c > 0 := by
    exact mul_pos (mul_pos (side_a_pos T) (side_b_pos T)) (side_c_pos T)
  have hrhs_pos : 4 * T.circumradius * T.area > 0 := by
    exact mul_pos (mul_pos (by norm_num : (4 : ℝ) > 0) (circumradius_pos T)) (area_pos T)
  -- From x² = y² and x > 0 and y > 0, conclude x = y
  have hlhs_nn : 0 ≤ T.side_a * T.side_b * T.side_c := le_of_lt hlhs_pos
  have hrhs_nn : 0 ≤ 4 * T.circumradius * T.area := le_of_lt hrhs_pos
  -- hsq says (abc)² = (4RA)² in expanded form; need to show (abc)² = (4RA)²
  have hsq' : (T.side_a * T.side_b * T.side_c) ^ 2 = (4 * T.circumradius * T.area) ^ 2 := by
    nlinarith [hsq]
  exact eq_of_sq_eq_nonneg hlhs_nn hrhs_nn hsq'


-- ============================================================
-- HERON'S FORMULA: PRODUCT FORM AND CLASSICAL FORM
-- ============================================================

/-- **Heron product identity** (pure ring): The product of the four factors
    (a+b+c)(b+c-a)(a+c-b)(a+b-c) equals 2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴.
    This is a polynomial identity requiring no geometric content. -/
theorem heron_product_eq_polynomial (a b c : ℝ) :
    (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c) =
    2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 -
    a ^ 4 - b ^ 4 - c ^ 4 := by ring

/-- **Heron product form**: For any triangle, the product
    (a+b+c)(b+c-a)(a+c-b)(a+b-c) = 16·Area².
    Follows from the polynomial ring identity + the coordinate Heron formula. -/
theorem heron_product_form (T : Triangle) :
    (T.side_a + T.side_b + T.side_c) *
    (T.side_b + T.side_c - T.side_a) *
    (T.side_a + T.side_c - T.side_b) *
    (T.side_a + T.side_b - T.side_c) =
    16 * T.area ^ 2 := by
  have h1 := heron_product_eq_polynomial T.side_a T.side_b T.side_c
  have h2 := herons_formula_sq T
  linarith

/-- **Classical Heron's formula**: Area² = s(s-a)(s-b)(s-c).
    This is the standard textbook form connecting area to semiperimeter. -/
theorem area_sq_eq_heron (T : Triangle) :
    T.area ^ 2 = T.semiperimeter * (T.semiperimeter - T.side_a) *
      (T.semiperimeter - T.side_b) * (T.semiperimeter - T.side_c) := by
  have h := heron_product_form T
  unfold Triangle.semiperimeter
  nlinarith

/-- **Sigma-Heron connection**: The sigma expression equals abcs - 4·Area².
    Combines the sigma identity with classical Heron to eliminate the
    s(s-a)(s-b)(s-c) factor.
    σ = abcs - 4s(s-a)(s-b)(s-c) = abcs - 4·Area² -/
theorem sigma_eq_abcs_minus_4area_sq (T : Triangle) :
    let a := T.side_a; let b := T.side_b; let c := T.side_c
    let s := T.semiperimeter
    (s - a) * (s - b) * c ^ 2 + (s - a) * (s - c) * b ^ 2 + (s - b) * (s - c) * a ^ 2 =
    a * b * c * s - 4 * T.area ^ 2 := by
  have hsigma := sigma_identity T.side_a T.side_b T.side_c
  have hheron := area_sq_eq_heron T
  simp only [Triangle.semiperimeter] at hsigma
  nlinarith

-- ============================================================
-- FEUERBACH ALGEBRAIC CORE: THE KEY SUBSTITUTION
-- ============================================================

/-- **Feuerbach algebraic core**: The key identity that makes Feuerbach work.
    Given abc = 4R·Area (extended law of sines), show:
    R²s² - (abcs - 4·Area²) = (Rs - 2·Area)²

    Proof: R²s²-abcs+4A² = R²s²-4RAs+4A² = (Rs-2A)²
    where the substitution abcs = 4RAs uses the hypothesis.

    Combined with |u|² = R²s² - σ from the bilinear expansion of
    N-I (which uses dot_circumcenter lemmas), this gives
    |u|² = (Rs - 2Area)², hence NI² = (R/2-r)². -/
theorem feuerbach_algebraic_core (a b c R Area : ℝ)
    (hels : a * b * c = 4 * R * Area) :
    let s := (a + b + c) / 2
    R ^ 2 * s ^ 2 - (a * b * c * s - 4 * Area ^ 2) = (R * s - 2 * Area) ^ 2 := by
  simp only
  have h : a * b * c * ((a + b + c) / 2) = 4 * R * Area * ((a + b + c) / 2) := by
    rw [hels]
  nlinarith [h]

/-- **Feuerbach algebraic chain**: Complete algebraic proof that
    R²s² - σ = (Rs - 2·Area)² for any triangle.
    Uses: sigma identity + Heron + extended law of sines.

    This is the central identity in Feuerbach's theorem:
    it shows that |N-I|² = (R/2-r)² purely algebraically. -/
theorem feuerbach_algebraic_chain (T : Triangle) :
    let a := T.side_a; let b := T.side_b; let c := T.side_c
    let s := T.semiperimeter; let R := T.circumradius
    R ^ 2 * s ^ 2 -
    ((s - a) * (s - b) * c ^ 2 + (s - a) * (s - c) * b ^ 2 + (s - b) * (s - c) * a ^ 2) =
    (R * s - 2 * T.area) ^ 2 := by
  have hsigma := sigma_eq_abcs_minus_4area_sq T
  have hcore := feuerbach_algebraic_core T.side_a T.side_b T.side_c T.circumradius T.area
    (extended_law_of_sines T)
  simp only [Triangle.semiperimeter] at hsigma
  nlinarith [hsigma]

/-- **NI² = (R/2-r)² equivalence**: The Feuerbach distance relation
    (R·s - 2·Area)² / (4s²) = (R/2 - r)² when r = Area/s.

    This is the final algebraic step: divide by 4s² and substitute r = Area/s. -/
theorem feuerbach_NI_sq_algebraic (R Area s : ℝ) (hs : s > 0) :
    (R * s - 2 * Area) ^ 2 / (4 * s ^ 2) = (R / 2 - Area / s) ^ 2 := by
  field_simp
  ring

-- ============================================================
-- COMPLETE FEUERBACH PROOF ROADMAP (UPDATED)
-- ============================================================

/-
## Updated Proof Chain for Feuerbach's Theorem

### Algebraic backbone (ALL PROVED):
  1. extended_law_of_sines: abc = 4R·Area [PROVED]
  2. sigma_identity: σ = abcs - 4s(s-a)(s-b)(s-c) [PROVED by ring]
  3. herons_formula_sq: 16·Area² = 2a²b²+2b²c²+2c²a²-a⁴-b⁴-c⁴ [PROVED by ring]
  4. heron_product_form: (a+b+c)(b+c-a)(a+c-b)(a+b-c) = 16Area² [PROVED]
  5. area_sq_eq_heron: Area² = s(s-a)(s-b)(s-c) [PROVED from 3+4]
  6. sigma_eq_abcs_minus_4area_sq: σ = abcs - 4Area² [PROVED from 2+5]
  7. feuerbach_algebraic_core: R²s² - σ = (Rs-2A)² given abc=4RA [PROVED]
  8. feuerbach_algebraic_chain: R²s² - σ = (Rs-2A)² for any triangle [PROVED from 1+6+7]
  9. feuerbach_NI_sq_algebraic: (Rs-2A)²/(4s²) = (R/2-r)² [PROVED by field_simp+ring]

### Geometric link (REMAINING OBSTACLE):
  10. N-I vector formula: N-I = u/(2s) where u = Σ(s-a_i)(V_i-O)
      Status: Provable as coordinate identity (ring), but involves sqrt in denominators
  11. |u|² = R²s² - σ via bilinear expansion using dot_circumcenter
      Status: Blocked by sqrt in (s-a), (s-b), (s-c) coefficients
  12. NI² = |u|²/(4s²) = (Rs-2A)²/(4s²) = (R/2-r)²

### What remains to close the gap:
  The algebraic chain (steps 1-9) is complete. The geometric link (steps 10-12)
  requires expressing the bilinear expansion of |u|² in terms that avoid sqrt.

  The most promising approach: express 4s²·NI² directly in coordinates via
  the orthocenter/circumcenter/incenter definitions, clear ALL denominators
  (including the circumcenter denominator d and (a+b+c)), and verify the
  resulting polynomial identity by ring. This would bypass the sqrt issue entirely.

  However, this polynomial identity has ~100+ terms in 6 variables and may
  exceed Lean's heartbeat limits for ring.
-/

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
#check @sigma_identity
#check @extended_law_of_sines_sq
#check @T345_euler_formula
#check @T345_extended_law_of_sines
#check @herons_formula_sq
#check @dot2_polarization
#check @dot_circumcenter_AB
#check @dot_circumcenter_AC
#check @dot_circumcenter_BC
#check @side_a_pos
#check @side_b_pos
#check @side_c_pos
#check @circumradius_pos
#check @extended_law_of_sines
#check @heron_product_eq_polynomial
#check @heron_product_form
#check @area_sq_eq_heron
#check @sigma_eq_abcs_minus_4area_sq
#check @feuerbach_algebraic_core
#check @feuerbach_algebraic_chain
#check @feuerbach_NI_sq_algebraic

end FeuerbachsTheoremOQ01
