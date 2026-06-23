/-
# Non-Desarguesian Planes: The Moulton Plane (OQ-02)

Research Question: How can we formalize non-Desarguesian planes in Lean
to demonstrate when Desargues's theorem fails?

Answer: YES. We construct the Moulton plane — an affine plane where lines
with negative slope "bend" at the y-axis (slope doubles for x > 0) — and
exhibit a concrete 6-point counterexample where two triangles are in
perspective from a point but NOT from a line.

Counterexample:
  O = (-4, 12), center of perspectivity
  Triangle: A=(-8,8), B=(-5,8), C=(-4,6)
  Triangle: A'=(-14,2), B'=(-7,0), C'=(-4,3)
  Side CA has Moulton slope -1/2, which becomes -1 for x > 0.
  This shifts intersection CA ∩ C'A' from (1, 7/2) to (6/11, 38/11),
  breaking collinearity with the other two intersection points.

Tags: projective-geometry, non-desarguesian, moulton-plane, counterexample
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace DesarguesTheoremOQ02

-- ============================================================
-- PART I: The Moulton Plane
-- ============================================================

abbrev MPoint := ℚ × ℚ

/-- A Moulton line: standard (any slope), bent (negative slope), or vertical. -/
inductive MLine where
  | standard (m b : ℚ) : MLine
  | bent (m b : ℚ) : MLine
  | vertical (a : ℚ) : MLine

/-- Incidence in the Moulton plane. For bent lines, slope doubles for x > 0. -/
def onLine (p : MPoint) (l : MLine) : Prop :=
  match l with
  | MLine.standard m b => p.2 = m * p.1 + b
  | MLine.bent m b =>
      (p.1 ≤ 0 ∧ p.2 = m * p.1 + b) ∨ (0 < p.1 ∧ p.2 = 2 * m * p.1 + b)
  | MLine.vertical a => p.1 = a

/-- Three points are Moulton-collinear if they all lie on some Moulton line. -/
def MoultonCollinear (p q r : MPoint) : Prop :=
  ∃ l : MLine, onLine p l ∧ onLine q l ∧ onLine r l

-- Helper tactic: prove bent-line incidence for a point with x ≤ 0
private theorem bent_left (m b x y : ℚ) (hx : x ≤ 0) (hy : y = m * x + b) :
    onLine (x, y) (MLine.bent m b) :=
  Or.inl ⟨hx, hy⟩

private theorem bent_right (m b x y : ℚ) (hx : 0 < x) (hy : y = 2 * m * x + b) :
    onLine (x, y) (MLine.bent m b) :=
  Or.inr ⟨hx, hy⟩

-- ============================================================
-- PART II: The Counterexample Configuration
-- ============================================================

def O : MPoint := (-4, 12)
def A : MPoint := (-8, 8)
def B : MPoint := (-5, 8)
def C : MPoint := (-4, 6)
def A' : MPoint := (-14, 2)
def B' : MPoint := (-7, 0)
def C' : MPoint := (-4, 3)

-- ============================================================
-- PART III: Perspectivity from Point O
-- ============================================================

-- Line OA = OA': y = x + 16 (slope 1, standard)
def lineOA : MLine := MLine.standard 1 16

theorem O_on_lineOA : onLine O lineOA := by show (12 : ℚ) = 1 * (-4) + 16; norm_num
theorem A_on_lineOA : onLine A lineOA := by show (8 : ℚ) = 1 * (-8) + 16; norm_num
theorem A'_on_lineOA : onLine A' lineOA := by show (2 : ℚ) = 1 * (-14) + 16; norm_num

-- Line OB = OB': y = 4x + 28 (slope 4, standard)
def lineOB : MLine := MLine.standard 4 28

theorem O_on_lineOB : onLine O lineOB := by show (12 : ℚ) = 4 * (-4) + 28; norm_num
theorem B_on_lineOB : onLine B lineOB := by show (8 : ℚ) = 4 * (-5) + 28; norm_num
theorem B'_on_lineOB : onLine B' lineOB := by show (0 : ℚ) = 4 * (-7) + 28; norm_num

-- Line OC = OC': x = -4 (vertical)
def lineOC : MLine := MLine.vertical (-4)

theorem O_on_lineOC : onLine O lineOC := by show (-4 : ℚ) = -4; rfl
theorem C_on_lineOC : onLine C lineOC := by show (-4 : ℚ) = -4; rfl
theorem C'_on_lineOC : onLine C' lineOC := by show (-4 : ℚ) = -4; rfl

/-- Lines AA', BB', CC' all pass through O. -/
theorem perspective_from_point :
    (onLine O lineOA ∧ onLine A lineOA ∧ onLine A' lineOA) ∧
    (onLine O lineOB ∧ onLine B lineOB ∧ onLine B' lineOB) ∧
    (onLine O lineOC ∧ onLine C lineOC ∧ onLine C' lineOC) :=
  ⟨⟨O_on_lineOA, A_on_lineOA, A'_on_lineOA⟩,
   ⟨O_on_lineOB, B_on_lineOB, B'_on_lineOB⟩,
   ⟨O_on_lineOC, C_on_lineOC, C'_on_lineOC⟩⟩

-- ============================================================
-- PART IV: Side Lines and Vertex Verification
-- ============================================================

def lineAB : MLine := MLine.standard 0 8
def lineApBp : MLine := MLine.bent (-2/7) (-2)
def lineBC : MLine := MLine.bent (-2) (-2)
def lineBpCp : MLine := MLine.standard 1 7
def lineCA : MLine := MLine.bent (-1/2) 4
def lineCpAp : MLine := MLine.standard (1/10) (17/5)

theorem A_on_AB : onLine A lineAB := by show (8 : ℚ) = 0 * (-8) + 8; norm_num
theorem B_on_AB : onLine B lineAB := by show (8 : ℚ) = 0 * (-5) + 8; norm_num

theorem Ap_on_ApBp : onLine A' lineApBp :=
  bent_left (-2/7) (-2) (-14) 2 (by norm_num) (by norm_num)

theorem Bp_on_ApBp : onLine B' lineApBp :=
  bent_left (-2/7) (-2) (-7) 0 (by norm_num) (by norm_num)

theorem B_on_BC : onLine B lineBC :=
  bent_left (-2) (-2) (-5) 8 (by norm_num) (by norm_num)

theorem C_on_BC : onLine C lineBC :=
  bent_left (-2) (-2) (-4) 6 (by norm_num) (by norm_num)

theorem Bp_on_BpCp : onLine B' lineBpCp := by show (0 : ℚ) = 1 * (-7) + 7; norm_num
theorem Cp_on_BpCp : onLine C' lineBpCp := by show (3 : ℚ) = 1 * (-4) + 7; norm_num

theorem C_on_CA : onLine C lineCA :=
  bent_left (-1/2) 4 (-4) 6 (by norm_num) (by norm_num)

theorem A_on_CA : onLine A lineCA :=
  bent_left (-1/2) 4 (-8) 8 (by norm_num) (by norm_num)

theorem Cp_on_CpAp : onLine C' lineCpAp := by
  show (3 : ℚ) = 1/10 * (-4) + 17/5; norm_num
theorem Ap_on_CpAp : onLine A' lineCpAp := by
  show (2 : ℚ) = 1/10 * (-14) + 17/5; norm_num

-- ============================================================
-- PART V: Moulton Intersection Points
-- ============================================================

/-- alpha = BC ∩ B'C' = (-3, 4) -/
def alpha : MPoint := (-3, 4)

theorem alpha_on_BC : onLine alpha lineBC :=
  bent_left (-2) (-2) (-3) 4 (by norm_num) (by norm_num)

theorem alpha_on_BpCp : onLine alpha lineBpCp := by
  show (4 : ℚ) = 1 * (-3) + 7; norm_num

/-- beta = CA ∩ C'A' = (6/11, 38/11).
    CA bent at x=6/11 > 0: y = 2(-1/2)(6/11)+4 = 38/11.
    C'A' standard: y = (1/10)(6/11)+17/5 = 38/11. -/
def beta : MPoint := (6/11, 38/11)

theorem beta_on_CA : onLine beta lineCA :=
  bent_right (-1/2) 4 (6/11) (38/11) (by norm_num) (by norm_num)

theorem beta_on_CpAp : onLine beta lineCpAp := by
  show (38 : ℚ) / 11 = 1/10 * (6/11) + 17/5; norm_num

/-- gamma = AB ∩ A'B' = (-35, 8) -/
def gamma : MPoint := (-35, 8)

theorem gamma_on_AB : onLine gamma lineAB := by
  show (8 : ℚ) = 0 * (-35) + 8; norm_num

theorem gamma_on_ApBp : onLine gamma lineApBp :=
  bent_left (-2/7) (-2) (-35) 8 (by norm_num) (by norm_num)

-- ============================================================
-- PART VI: Non-Collinearity Proof
-- ============================================================

/-- The three Moulton intersection points alpha=(-3,4), beta=(6/11,38/11),
    gamma=(-35,8) are NOT Moulton-collinear.

    Key arithmetic: any line through alpha and gamma has the constraint
    that its value at beta's x-coordinate misses beta's y-coordinate
    by 3/88 (for bent) or 9/88 (for standard). -/
theorem not_moulton_collinear : ¬ MoultonCollinear alpha beta gamma := by
  intro ⟨l, hl_a, hl_b, hl_g⟩
  simp only [alpha, beta, gamma] at hl_a hl_b hl_g
  cases l with
  | standard m b =>
    -- All three on y = mx + b:
    -- 4 = -3m + b, 38/11 = (6/11)m + b, 8 = -35m + b
    -- First two: 32m = -4, m = -1/8, b = 29/8
    -- Third: 38/11 = (6/11)(-1/8) + 29/8 = -3/44 + 29/8 = 313/88 ≠ 304/88
    change (4 : ℚ) = m * (-3) + b at hl_a
    change (38 : ℚ) / 11 = m * (6/11) + b at hl_b
    change (8 : ℚ) = m * (-35) + b at hl_g
    linarith
  | bent m b =>
    -- alpha at x=-3 ≤ 0 → left branch: 4 = m(-3) + b
    -- gamma at x=-35 ≤ 0 → left branch: 8 = m(-35) + b
    -- beta at x=6/11 > 0 → right branch: 38/11 = 2m(6/11) + b
    -- From alpha, gamma: m = -1/8, b = 29/8
    -- beta right: 38/11 = 2(-1/8)(6/11) + 29/8 = -6/44 + 29/8 = 307/88 ≠ 304/88
    change ((-3 : ℚ) ≤ 0 ∧ 4 = m * (-3) + b) ∨ (0 < (-3 : ℚ) ∧ _) at hl_a
    change ((-35 : ℚ) ≤ 0 ∧ 8 = m * (-35) + b) ∨ (0 < (-35 : ℚ) ∧ _) at hl_g
    change ((6 : ℚ)/11 ≤ 0 ∧ _) ∨ (0 < (6 : ℚ)/11 ∧ 38/11 = 2 * m * (6/11) + b) at hl_b
    -- Resolve disjunctions
    have ha : (4 : ℚ) = m * (-3) + b := by
      rcases hl_a with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hg : (8 : ℚ) = m * (-35) + b := by
      rcases hl_g with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hb : (38 : ℚ)/11 = 2 * m * (6/11) + b := by
      rcases hl_b with ⟨h, _⟩ | ⟨_, h⟩; norm_num at h; exact h
    linarith
  | vertical a =>
    -- alpha.1 = -3 = a, beta.1 = 6/11 = a → -3 = 6/11, contradiction
    change (-3 : ℚ) = a at hl_a
    change (6 : ℚ) / 11 = a at hl_b
    linarith

-- ============================================================
-- PART VII: Main Theorem
-- ============================================================

/-- Desargues's theorem fails in the Moulton plane.
    Two triangles in perspective from a point whose corresponding
    side-intersections are NOT Moulton-collinear. -/
theorem desargues_fails_in_moulton :
    -- Perspective from point O
    (onLine O lineOA ∧ onLine A lineOA ∧ onLine A' lineOA) ∧
    (onLine O lineOB ∧ onLine B lineOB ∧ onLine B' lineOB) ∧
    (onLine O lineOC ∧ onLine C lineOC ∧ onLine C' lineOC) ∧
    -- Intersection points on corresponding sides
    (onLine alpha lineBC ∧ onLine alpha lineBpCp) ∧
    (onLine beta lineCA ∧ onLine beta lineCpAp) ∧
    (onLine gamma lineAB ∧ onLine gamma lineApBp) ∧
    -- NOT collinear
    ¬ MoultonCollinear alpha beta gamma :=
  ⟨⟨O_on_lineOA, A_on_lineOA, A'_on_lineOA⟩,
   ⟨O_on_lineOB, B_on_lineOB, B'_on_lineOB⟩,
   ⟨O_on_lineOC, C_on_lineOC, C'_on_lineOC⟩,
   ⟨alpha_on_BC, alpha_on_BpCp⟩,
   ⟨beta_on_CA, beta_on_CpAp⟩,
   ⟨gamma_on_AB, gamma_on_ApBp⟩,
   not_moulton_collinear⟩

-- ============================================================
-- PART VIII: Structural Properties
-- ============================================================

theorem vertices_distinct :
    A ≠ B ∧ B ≠ C ∧ C ≠ A ∧ A' ≠ B' ∧ B' ≠ C' ∧ C' ≠ A' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; simp [A, B, C, A', B', C'] at h)

/-- Triangle ABC is non-degenerate (not Moulton-collinear). -/
theorem triangle_ABC_nondegenerate : ¬ MoultonCollinear A B C := by
  intro ⟨l, hlA, hlB, hlC⟩
  simp only [A, B, C] at hlA hlB hlC
  cases l with
  | standard m b =>
    change (8 : ℚ) = m * (-8) + b at hlA
    change (8 : ℚ) = m * (-5) + b at hlB
    change (6 : ℚ) = m * (-4) + b at hlC
    linarith
  | bent m b =>
    have ha : (8 : ℚ) = m * (-8) + b := by
      change ((-8 : ℚ) ≤ 0 ∧ _) ∨ _ at hlA
      rcases hlA with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hb : (8 : ℚ) = m * (-5) + b := by
      change ((-5 : ℚ) ≤ 0 ∧ _) ∨ _ at hlB
      rcases hlB with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hc : (6 : ℚ) = m * (-4) + b := by
      change ((-4 : ℚ) ≤ 0 ∧ _) ∨ _ at hlC
      rcases hlC with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    linarith
  | vertical a =>
    change (-8 : ℚ) = a at hlA; change (-5 : ℚ) = a at hlB
    linarith

/-- Triangle A'B'C' is non-degenerate (not Moulton-collinear). -/
theorem triangle_ApBpCp_nondegenerate : ¬ MoultonCollinear A' B' C' := by
  intro ⟨l, hlA, hlB, hlC⟩
  simp only [A', B', C'] at hlA hlB hlC
  cases l with
  | standard m b =>
    change (2 : ℚ) = m * (-14) + b at hlA
    change (0 : ℚ) = m * (-7) + b at hlB
    change (3 : ℚ) = m * (-4) + b at hlC
    linarith
  | bent m b =>
    have ha : (2 : ℚ) = m * (-14) + b := by
      change ((-14 : ℚ) ≤ 0 ∧ _) ∨ _ at hlA
      rcases hlA with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hb : (0 : ℚ) = m * (-7) + b := by
      change ((-7 : ℚ) ≤ 0 ∧ _) ∨ _ at hlB
      rcases hlB with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    have hc : (3 : ℚ) = m * (-4) + b := by
      change ((-4 : ℚ) ≤ 0 ∧ _) ∨ _ at hlC
      rcases hlC with ⟨_, h⟩ | ⟨h, _⟩; exact h; norm_num at h
    linarith
  | vertical a =>
    change (-14 : ℚ) = a at hlA; change (-7 : ℚ) = a at hlB
    linarith

-- ============================================================
-- PART IX: Euclidean vs Moulton Comparison
-- ============================================================

/-- In the Euclidean plane (standard lines only), the same three intersection
    points ARE collinear. This demonstrates that the non-collinearity is
    specifically due to the Moulton bending. -/
theorem euclidean_alpha_beta_gamma_collinear :
    ∃ (m b : ℚ), (4 : ℚ) = m * (-3) + b ∧
                  (7 : ℚ)/2 = m * 1 + b ∧    -- Euclidean beta = (1, 7/2)
                  (8 : ℚ) = m * (-35) + b :=
  ⟨-1/8, 29/8, by norm_num, by norm_num, by norm_num⟩

/-- But in the Moulton plane, the shifted beta = (6/11, 38/11) breaks
    the alignment. The Euclidean line y = -x/8 + 29/8 evaluates to
    307/88 at x = 6/11 (using Moulton bending), but beta.y = 38/11 = 304/88.
    Gap = 3/88. -/
theorem moulton_gap :
    let line_y_bent := 2 * (-1/8 : ℚ) * (6/11) + 29/8
    let beta_y := (38 : ℚ)/11
    line_y_bent - beta_y = 3/88 := by norm_num

end DesarguesTheoremOQ02
