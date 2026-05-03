import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Non-Desarguesian Projective Planes: The Moulton Plane

## Open Question
Can we formalize non-Desarguesian projective planes in Lean to demonstrate when
Desargues's theorem fails?

## Answer: YES — via the Moulton plane (Moulton 1902)

The **Moulton plane** is a modified affine plane over ℝ that satisfies all affine
plane axioms but violates Desargues's theorem. This proves that Desargues's theorem
is NOT derivable from the affine plane axioms alone — it requires additional algebraic
structure (coordinatization by a field or division ring).

## Construction

Points: ℝ × ℝ (ordinary Cartesian plane).
Lines: Modified to "bend" at the y-axis for positive slopes:
  - Vertical lines: {x = c}
  - Lines with left-slope m ≤ 0: ordinary lines y = mx + b
  - Lines with left-slope m > 0: y = mx + b for x ≤ 0,  y = (m/2)x + b for x > 0

## Main Result

An explicit counterexample (triangles with rational coordinates) where two triangles
are in **affine perspective from a point** (O = (0,0)) but the three intersections of
corresponding sides are **not Moulton-collinear**, refuting Desargues in this plane.

## Counterexample Data

- Center of perspectivity: O = (0, 0)
- Triangle 1: A = (-2, 3), B = (3, 1), C = (0, -1)
- Triangle 2: A' = (-4, 6), B' = (9, 3), C' = (0, -4)
- P = AB ∩ A'B' = (-17, 9)      [ordinary, negative-slope sides]
- Q = BC ∩ B'C' = (27, 17)      [right-half-plane sides]
- R = CA ∩ C'A' = (-6, 11)      [ordinary, negative-slope sides]
- P, Q, R are Euclidean-collinear (classical Desargues holds in ℝ²)
- P, Q, R are NOT Moulton-collinear (Desargues fails in the Moulton plane)
-/

namespace MoultonPlane

open Classical

/-! ## Part I: The Moulton Line Structure -/

/-- A point P lies on the Moulton non-vertical line with "left-slope" m and
    y-intercept b.  For m ≤ 0 this is just the ordinary line.  For m > 0 the
    line bends at the y-axis: left half (x ≤ 0) has slope m, right half (x > 0)
    has slope m/2, with both halves meeting at y = b when x = 0. -/
def onMoultonLine (m b : ℝ) (P : ℝ × ℝ) : Prop :=
  if m ≤ 0 then P.2 = m * P.1 + b
  else if P.1 ≤ 0 then P.2 = m * P.1 + b
  else P.2 = (m / 2) * P.1 + b

/-- Three points are Moulton-collinear if they all lie on a single Moulton line. -/
def MoultonCollinear (P Q R : ℝ × ℝ) : Prop :=
  (P.1 = Q.1 ∧ P.1 = R.1) ∨
  ∃ m b : ℝ, onMoultonLine m b P ∧ onMoultonLine m b Q ∧ onMoultonLine m b R

/-! ### Helper lemmas for onMoultonLine -/

lemma onML_neg_slope {m b : ℝ} (hm : m ≤ 0) (P : ℝ × ℝ) (h : P.2 = m * P.1 + b) :
    onMoultonLine m b P := by
  simp only [onMoultonLine, if_pos hm]; exact h

lemma onML_pos_left {m b : ℝ} (hm : ¬m ≤ 0) (P : ℝ × ℝ)
    (hx : P.1 ≤ 0) (h : P.2 = m * P.1 + b) : onMoultonLine m b P := by
  simp only [onMoultonLine, if_neg hm, if_pos hx]; exact h

lemma onML_pos_right {m b : ℝ} (hm : ¬m ≤ 0) (P : ℝ × ℝ)
    (hx : ¬P.1 ≤ 0) (h : P.2 = (m / 2) * P.1 + b) : onMoultonLine m b P := by
  simp only [onMoultonLine, if_neg hm, if_neg hx]; exact h

lemma onML_eq_neg {m b : ℝ} (hm : m ≤ 0) (P : ℝ × ℝ) (h : onMoultonLine m b P) :
    P.2 = m * P.1 + b := by
  simp only [onMoultonLine, if_pos hm] at h; exact h

lemma onML_eq_pos_left {m b : ℝ} (hm : ¬m ≤ 0) (P : ℝ × ℝ) (hx : P.1 ≤ 0)
    (h : onMoultonLine m b P) : P.2 = m * P.1 + b := by
  simp only [onMoultonLine, if_neg hm, if_pos hx] at h; exact h

lemma onML_eq_pos_right {m b : ℝ} (hm : ¬m ≤ 0) (P : ℝ × ℝ) (hx : ¬P.1 ≤ 0)
    (h : onMoultonLine m b P) : P.2 = (m / 2) * P.1 + b := by
  simp only [onMoultonLine, if_neg hm, if_neg hx] at h; exact h

/-! ## Part II: The Counterexample Points -/

private def O_pt  : ℝ × ℝ := (0,   0)
private def A_pt  : ℝ × ℝ := (-2,  3)
private def B_pt  : ℝ × ℝ := (3,   1)
private def C_pt  : ℝ × ℝ := (0,  -1)
private def A'_pt : ℝ × ℝ := (-4,  6)
private def B'_pt : ℝ × ℝ := (9,   3)
private def C'_pt : ℝ × ℝ := (0,  -4)
private def P_pt  : ℝ × ℝ := (-17, 9)
private def Q_pt  : ℝ × ℝ := (27,  17)
private def R_pt  : ℝ × ℝ := (-6,  11)

/-! ## Part III: Perspectivity from O = (0, 0)

  Lines OAA', OBB', OCC' are valid Moulton lines, establishing that triangles
  ABC and A'B'C' are in affine perspective from the center O. -/

/-- O, A, A' lie on the Moulton line with slope -3/2 and intercept 0
    (negative slope → ordinary line). -/
lemma collinear_OAA' : MoultonCollinear O_pt A_pt A'_pt := by
  right
  exact ⟨-3/2, 0,
    onML_neg_slope (by norm_num) _ (by simp [O_pt]; ring),
    onML_neg_slope (by norm_num) _ (by simp [A_pt]; ring),
    onML_neg_slope (by norm_num) _ (by simp [A'_pt]; ring)⟩

/-- O, B, B' lie on the Moulton line with left-slope 2/3 and intercept 0.
    O is at x = 0 (left boundary); B, B' are at x > 0 (right half, slope 1/3). -/
lemma collinear_OBB' : MoultonCollinear O_pt B_pt B'_pt := by
  right
  exact ⟨2/3, 0,
    onML_pos_left (by norm_num) _ (by norm_num) (by simp [O_pt]; ring),
    onML_pos_right (by norm_num) _ (by simp [B_pt]; norm_num) (by simp [B_pt]; ring),
    onML_pos_right (by norm_num) _ (by simp [B'_pt]; norm_num) (by simp [B'_pt]; ring)⟩

/-- O, C, C' lie on the vertical Moulton line x = 0. -/
lemma collinear_OCC' : MoultonCollinear O_pt C_pt C'_pt := by
  left
  simp [O_pt, C_pt, C'_pt]

/-! ## Part IV: Intersection Points

  P, Q, R are the Moulton-line intersections of corresponding sides.
  For sides with slope ≤ 0 (or entirely on one half-plane),
  Moulton lines coincide with ordinary lines, so the intersections are
  computed by ordinary linear algebra. -/

/-- P = (-17, 9) lies on Moulton line AB (slope -2/5, intercept 11/5). -/
lemma P_on_AB : onMoultonLine (-2/5) (11/5) P_pt :=
  onML_neg_slope (by norm_num) _ (by simp [P_pt]; ring)

/-- P = (-17, 9) lies on Moulton line A'B' (slope -3/13, intercept 66/13). -/
lemma P_on_A'B' : onMoultonLine (-3/13) (66/13) P_pt :=
  onML_neg_slope (by norm_num) _ (by simp [P_pt]; ring)

/-- A = (-2, 3) lies on Moulton line AB. -/
lemma A_on_AB : onMoultonLine (-2/5) (11/5) A_pt :=
  onML_neg_slope (by norm_num) _ (by simp [A_pt]; ring)

/-- B = (3, 1) lies on Moulton line AB. -/
lemma B_on_AB : onMoultonLine (-2/5) (11/5) B_pt :=
  onML_neg_slope (by norm_num) _ (by simp [B_pt]; ring)

/-- A' = (-4, 6) lies on Moulton line A'B'. -/
lemma A'_on_A'B' : onMoultonLine (-3/13) (66/13) A'_pt :=
  onML_neg_slope (by norm_num) _ (by simp [A'_pt]; ring)

/-- B' = (9, 3) lies on Moulton line A'B'. -/
lemma B'_on_A'B' : onMoultonLine (-3/13) (66/13) B'_pt :=
  onML_neg_slope (by norm_num) _ (by simp [B'_pt]; ring)

/-- Q = (27, 17) lies on the right-half Moulton line BC
    (left-slope 4/3, intercept -1; right slope 2/3). -/
lemma Q_on_BC : onMoultonLine (4/3) (-1) Q_pt :=
  onML_pos_right (by norm_num) _ (by simp [Q_pt]; norm_num) (by simp [Q_pt]; ring)

/-- Q = (27, 17) lies on the right-half Moulton line B'C'
    (left-slope 14/9, intercept -4; right slope 7/9). -/
lemma Q_on_B'C' : onMoultonLine (14/9) (-4) Q_pt :=
  onML_pos_right (by norm_num) _ (by simp [Q_pt]; norm_num) (by simp [Q_pt]; ring)

/-- B = (3, 1) lies on Moulton line BC. -/
lemma B_on_BC : onMoultonLine (4/3) (-1) B_pt :=
  onML_pos_right (by norm_num) _ (by simp [B_pt]; norm_num) (by simp [B_pt]; ring)

/-- C = (0, -1) lies on Moulton line BC. -/
lemma C_on_BC : onMoultonLine (4/3) (-1) C_pt :=
  onML_pos_left (by norm_num) _ (by simp [C_pt]; norm_num) (by simp [C_pt]; ring)

/-- B' = (9, 3) lies on Moulton line B'C'. -/
lemma B'_on_B'C' : onMoultonLine (14/9) (-4) B'_pt :=
  onML_pos_right (by norm_num) _ (by simp [B'_pt]; norm_num) (by simp [B'_pt]; ring)

/-- C' = (0, -4) lies on Moulton line B'C'. -/
lemma C'_on_B'C' : onMoultonLine (14/9) (-4) C'_pt :=
  onML_pos_left (by norm_num) _ (by simp [C'_pt]; norm_num) (by simp [C'_pt]; ring)

/-- R = (-6, 11) lies on Moulton line CA (slope -2, intercept -1). -/
lemma R_on_CA : onMoultonLine (-2) (-1) R_pt :=
  onML_neg_slope (by norm_num) _ (by simp [R_pt]; ring)

/-- R = (-6, 11) lies on Moulton line C'A' (slope -5/2, intercept -4). -/
lemma R_on_C'A' : onMoultonLine (-5/2) (-4) R_pt :=
  onML_neg_slope (by norm_num) _ (by simp [R_pt]; ring)

/-- C = (0, -1) lies on Moulton line CA. -/
lemma C_on_CA : onMoultonLine (-2) (-1) C_pt :=
  onML_neg_slope (by norm_num) _ (by simp [C_pt]; ring)

/-- A = (-2, 3) lies on Moulton line CA. -/
lemma A_on_CA : onMoultonLine (-2) (-1) A_pt :=
  onML_neg_slope (by norm_num) _ (by simp [A_pt]; ring)

/-- C' = (0, -4) lies on Moulton line C'A'. -/
lemma C'_on_C'A' : onMoultonLine (-5/2) (-4) C'_pt :=
  onML_neg_slope (by norm_num) _ (by simp [C'_pt]; ring)

/-- A' = (-4, 6) lies on Moulton line C'A'. -/
lemma A'_on_C'A' : onMoultonLine (-5/2) (-4) A'_pt :=
  onML_neg_slope (by norm_num) _ (by simp [A'_pt]; ring)

/-! ## Part V: Desargues Fails — P, Q, R Are Not Moulton-Collinear

  The key computation: P = (-17, 9), Q = (27, 17), R = (-6, 11).

  Since P, R have x < 0 and Q has x > 0, any Moulton line through all three
  must be a bent line with positive left-slope m.  Setting up the equations:
    P on left:  9 = m·(-17) + b
    Q on right: 17 = (m/2)·27 + b
  gives m = 16/61.  Then R on left:  11 = m·(-6) + b
  yields 11 = 725/61, a contradiction.

  Negative-slope Moulton lines cannot contain PQ (slope 2/11 > 0), and
  vertical lines are excluded since P, Q, R have distinct x-coordinates. -/

/-- P, Q, R have pairwise distinct x-coordinates, ruling out vertical collinearity. -/
private lemma PQR_x_distinct :
    P_pt.1 ≠ Q_pt.1 ∧ P_pt.1 ≠ R_pt.1 ∧ Q_pt.1 ≠ R_pt.1 := by
  simp [P_pt, Q_pt, R_pt]; norm_num

/-- The main theorem: P, Q, R are NOT Moulton-collinear.
    Desargues's theorem fails in the Moulton plane. -/
theorem desargues_fails : ¬ MoultonCollinear P_pt Q_pt R_pt := by
  intro h
  rcases h with ⟨hv1, _⟩ | ⟨m, b, hP, hQ, hR⟩
  · -- Vertical case: P.1 = -17 ≠ 27 = Q.1
    simp only [P_pt, Q_pt] at hv1
    norm_num at hv1
  · -- Non-vertical case: derive contradiction from the linear system
    by_cases hm : m ≤ 0
    · -- m ≤ 0: ordinary line.  hQ' - hP' gives 44m = 8, contradicting hm : m ≤ 0.
      have hP' := onML_eq_neg hm _ hP
      have hQ' := onML_eq_neg hm _ hQ
      simp only [P_pt, Q_pt] at hP' hQ'
      -- hP': 9 = m * (-17) + b,  hQ': 17 = m * 27 + b  →  44m = 8 > 0
      linarith
    · -- m > 0: P.1 = -17 ≤ 0, Q.1 = 27 > 0, R.1 = -6 ≤ 0.
      have hPx : P_pt.1 ≤ 0 := by simp [P_pt]; norm_num
      have hQx : ¬ Q_pt.1 ≤ 0 := by simp [Q_pt]; norm_num
      have hRx : R_pt.1 ≤ 0 := by simp [R_pt]; norm_num
      -- Extract equations for each point
      have hP' := onML_eq_pos_left hm _ hPx hP   -- 9 = m * (-17) + b
      have hQ' := onML_eq_pos_right hm _ hQx hQ  -- 17 = m / 2 * 27 + b
      have hR' := onML_eq_pos_left hm _ hRx hR   -- 11 = m * (-6) + b
      simp only [P_pt, Q_pt, R_pt] at hP' hQ' hR'
      -- Step 1: 11m = 2  (from hP' − hR': (m*(-17)+b−9) − (m*(-6)+b−11) = -11m+2 = 0)
      have h1 : (11 : ℝ) * m = 2 := by linear_combination hP' - hR'
      -- Step 2: 61m = 16  (from 2*hP' − 2*hQ': clears b and uses 2*(m/2*27) = 27m by ring)
      have h2 : (61 : ℝ) * m = 16 := by linear_combination 2 * hP' - 2 * hQ'
      -- Contradiction: 61*(11m) = 122 but 11*(61m) = 176, so 122 = 176
      linarith

/-! ## Part VI: The Full Desargues Counterexample -/

/-- **Main theorem**: The Moulton plane contains two triangles in affine perspective
    from a point whose corresponding-side intersections are not collinear, refuting
    Desargues's theorem in this non-Desarguesian affine plane. -/
theorem moulton_counterexample :
    -- Triangles ABC and A'B'C' are in perspective from O = (0,0):
    MoultonCollinear O_pt A_pt A'_pt ∧
    MoultonCollinear O_pt B_pt B'_pt ∧
    MoultonCollinear O_pt C_pt C'_pt ∧
    -- P, Q, R lie on the respective pairs of corresponding sides:
    onMoultonLine (-2/5) (11/5) P_pt ∧ onMoultonLine (-2/5) (11/5) A_pt ∧
      onMoultonLine (-2/5) (11/5) B_pt ∧
    onMoultonLine (-3/13) (66/13) P_pt ∧ onMoultonLine (-3/13) (66/13) A'_pt ∧
      onMoultonLine (-3/13) (66/13) B'_pt ∧
    onMoultonLine (4/3) (-1) Q_pt ∧ onMoultonLine (4/3) (-1) B_pt ∧
      onMoultonLine (4/3) (-1) C_pt ∧
    onMoultonLine (14/9) (-4) Q_pt ∧ onMoultonLine (14/9) (-4) B'_pt ∧
      onMoultonLine (14/9) (-4) C'_pt ∧
    onMoultonLine (-2) (-1) R_pt ∧ onMoultonLine (-2) (-1) C_pt ∧
      onMoultonLine (-2) (-1) A_pt ∧
    onMoultonLine (-5/2) (-4) R_pt ∧ onMoultonLine (-5/2) (-4) C'_pt ∧
      onMoultonLine (-5/2) (-4) A'_pt ∧
    -- But P, Q, R are NOT Moulton-collinear:
    ¬ MoultonCollinear P_pt Q_pt R_pt :=
  ⟨collinear_OAA', collinear_OBB', collinear_OCC',
   P_on_AB, A_on_AB, B_on_AB,
   P_on_A'B', A'_on_A'B', B'_on_A'B',
   Q_on_BC, B_on_BC, C_on_BC,
   Q_on_B'C', B'_on_B'C', C'_on_B'C',
   R_on_CA, C_on_CA, A_on_CA,
   R_on_C'A', C'_on_C'A', A'_on_C'A',
   desargues_fails⟩

end MoultonPlane
