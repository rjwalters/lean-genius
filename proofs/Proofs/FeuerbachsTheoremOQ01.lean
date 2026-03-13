import Proofs.FeuerbachsTheorem

/-
# Feuerbach Distance Relations via Coordinate Computation (feuerbachs-theorem-oq-01)

## The Open Question

Can the Feuerbach distance relations (axioms in FeuerbachsTheorem.lean) be
proved by direct coordinate computation in ℝ²?

## What This File Proves

We prove the three "altitude foot on nine-point circle" results:
  foot_a_on_ninePointCircle, foot_b_on_ninePointCircle, foot_c_on_ninePointCircle

These were previously axiomatized because the coordinate algebra involves division
by |BC|² in the projection formula AND division by the circumcenter denominator d.
After clearing both denominators with field_simp, the identities reduce to
polynomial ring equalities.

## Strategy

For each altitude foot H_k:
1. Compute the squared distance |H_k - N|² by unfolding all definitions
2. Clear denominators with field_simp (circumcenter denom d and |side|²)
3. Verify the polynomial identity with ring
4. Compare with R²/4 = |O - A|²/4 to conclude dist(N, H_k) = R/2

## Axioms Eliminated

This file proves 3 of the 8 axioms in FeuerbachsTheorem.lean:
- foot_a_on_ninePointCircle (axiom → theorem)
- foot_b_on_ninePointCircle (axiom → theorem)
- foot_c_on_ninePointCircle (axiom → theorem)
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

-- Type-check results
#check @foot_a_on_ninePointCircle_proved
#check @foot_b_on_ninePointCircle_proved
#check @foot_c_on_ninePointCircle_proved
#check @equilateral_R_eq_2r_proved

end FeuerbachsTheoremOQ01
