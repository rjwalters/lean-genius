import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-
# Feuerbach's Theorem - Definitions and Infrastructure

## What This Contains
Core definitions, infrastructure lemmas, and nine-point circle proofs for
Feuerbach's Theorem (Wiedijk's #29): The nine-point circle of a triangle is tangent to
the incircle and all three excircles.

The main Feuerbach distance relations (incircle and excircle tangency) are proved in
FeuerbachsTheoremOQ01.lean and assembled in FeuerbachsTheorem.lean.

## Statement
For any triangle ABC:
- The nine-point circle passes through:
  1. The midpoints of the three sides
  2. The feet of the three altitudes
  3. The midpoints of segments from vertices to the orthocenter
- This circle has radius R/2 where R is the circumradius
- Its center N is the midpoint of the orthocenter H and circumcenter O

## Approach
- **Foundation (from Mathlib):** We use Mathlib's Euclidean geometry, sphere, and
  circumcenter infrastructure.
- **Coordinate Geometry:** We use explicit coordinates for computational tractability.
- **Original Contributions:** Complete formalization of the nine-point circle,
  incircle, excircles, and the tangency relations.

## Historical Note
Karl Wilhelm Feuerbach proved this theorem in 1822. The nine-point circle is also
known as Feuerbach's circle, the Euler circle, or the six-points circle.
The tangency point with the incircle is called the Feuerbach point.

## Difficulty: Hard
This involves significant geometric computation to establish all the tangency relations.

## References
- https://en.wikipedia.org/wiki/Nine-point_circle
- https://en.wikipedia.org/wiki/Feuerbach_point
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheorem

open Real EuclideanGeometry

-- ============================================================
-- PART 1: Triangle Configuration in ℝ²
-- ============================================================

/-- A point in the plane -/
abbrev Point := ℝ × ℝ

/-- A non-degenerate triangle in the plane with vertices A, B, C.
    We require the triangle to have positive area (non-collinear vertices). -/
structure Triangle where
  /-- First vertex -/
  A : Point
  /-- Second vertex -/
  B : Point
  /-- Third vertex -/
  C : Point
  /-- Triangle inequality: vertices are non-collinear -/
  nondegenerate : (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- Side length a = |BC| -/
def Triangle.side_a (T : Triangle) : ℝ :=
  Real.sqrt ((T.C.1 - T.B.1)^2 + (T.C.2 - T.B.2)^2)

/-- Side length b = |CA| -/
def Triangle.side_b (T : Triangle) : ℝ :=
  Real.sqrt ((T.A.1 - T.C.1)^2 + (T.A.2 - T.C.2)^2)

/-- Side length c = |AB| -/
def Triangle.side_c (T : Triangle) : ℝ :=
  Real.sqrt ((T.B.1 - T.A.1)^2 + (T.B.2 - T.A.2)^2)

/-- Semi-perimeter s = (a + b + c) / 2 -/
def Triangle.semiperimeter (T : Triangle) : ℝ :=
  (T.side_a + T.side_b + T.side_c) / 2

/-- Area of the triangle using the shoelace formula -/
def Triangle.area (T : Triangle) : ℝ :=
  abs ((T.B.1 - T.A.1) * (T.C.2 - T.A.2) - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) / 2

-- ============================================================
-- PART 2: Special Points of a Triangle
-- ============================================================

/-- Midpoint of two points -/
def pointMidpoint (P Q : Point) : Point := ((P.1 + Q.1) / 2, (P.2 + Q.2) / 2)

/-- Midpoint of BC -/
def Triangle.midpoint_a (T : Triangle) : Point := pointMidpoint T.B T.C

/-- Midpoint of CA -/
def Triangle.midpoint_b (T : Triangle) : Point := pointMidpoint T.C T.A

/-- Midpoint of AB -/
def Triangle.midpoint_c (T : Triangle) : Point := pointMidpoint T.A T.B

/-- The circumcenter O: equidistant from all three vertices.
    Computed using the circumcenter formula. -/
def Triangle.circumcenter (T : Triangle) : Point :=
  let d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  let ux := ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
             (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d
  let uy := ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
             (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d
  (ux, uy)

/-- Distance between two points in ℝ² -/
def dist2 (P Q : Point) : ℝ :=
  Real.sqrt ((Q.1 - P.1)^2 + (Q.2 - P.2)^2)

/-- Circumradius R: distance from circumcenter to any vertex -/
def Triangle.circumradius (T : Triangle) : ℝ :=
  dist2 T.circumcenter T.A

/-- The orthocenter H: intersection of altitudes.
    H = A + B + C - 2·O for circumcenter O (Euler line relation) -/
def Triangle.orthocenter (T : Triangle) : Point :=
  let O := T.circumcenter
  (T.A.1 + T.B.1 + T.C.1 - 2 * O.1, T.A.2 + T.B.2 + T.C.2 - 2 * O.2)

/-- The centroid G: intersection of medians -/
def Triangle.centroid (T : Triangle) : Point :=
  ((T.A.1 + T.B.1 + T.C.1) / 3, (T.A.2 + T.B.2 + T.C.2) / 3)

-- ============================================================
-- PART 3: The Nine-Point Circle
-- ============================================================

/-- The nine-point center N: midpoint of orthocenter H and circumcenter O -/
def Triangle.ninePointCenter (T : Triangle) : Point :=
  pointMidpoint T.orthocenter T.circumcenter

/-- The nine-point radius: R/2 where R is the circumradius -/
def Triangle.ninePointRadius (T : Triangle) : ℝ :=
  T.circumradius / 2

/-- Midpoint of AH (A to orthocenter) -/
def Triangle.midpoint_AH (T : Triangle) : Point := pointMidpoint T.A T.orthocenter

/-- Midpoint of BH (B to orthocenter) -/
def Triangle.midpoint_BH (T : Triangle) : Point := pointMidpoint T.B T.orthocenter

/-- Midpoint of CH (C to orthocenter) -/
def Triangle.midpoint_CH (T : Triangle) : Point := pointMidpoint T.C T.orthocenter

/-- Squared distance between two points (avoids sqrt) -/
def dist2_sq (P Q : Point) : ℝ := (Q.1 - P.1)^2 + (Q.2 - P.2)^2

/-- Foot of the altitude from A to line BC (orthogonal projection) -/
def Triangle.foot_a (T : Triangle) : Point :=
  let dx := T.C.1 - T.B.1
  let dy := T.C.2 - T.B.2
  let bc_sq := dx^2 + dy^2
  let t := ((T.A.1 - T.B.1) * dx + (T.A.2 - T.B.2) * dy) / bc_sq
  (T.B.1 + t * dx, T.B.2 + t * dy)

/-- Foot of the altitude from B to line CA (orthogonal projection) -/
def Triangle.foot_b (T : Triangle) : Point :=
  let dx := T.A.1 - T.C.1
  let dy := T.A.2 - T.C.2
  let ca_sq := dx^2 + dy^2
  let t := ((T.B.1 - T.C.1) * dx + (T.B.2 - T.C.2) * dy) / ca_sq
  (T.C.1 + t * dx, T.C.2 + t * dy)

/-- Foot of the altitude from C to line AB (orthogonal projection) -/
def Triangle.foot_c (T : Triangle) : Point :=
  let dx := T.B.1 - T.A.1
  let dy := T.B.2 - T.A.2
  let ab_sq := dx^2 + dy^2
  let t := ((T.C.1 - T.A.1) * dx + (T.C.2 - T.A.2) * dy) / ab_sq
  (T.A.1 + t * dx, T.A.2 + t * dy)

-- ============================================================
-- PART 4: Incircle and Excircles
-- ============================================================

/-- The incenter I: intersection of angle bisectors.
    Computed as weighted average of vertices by opposite side lengths. -/
def Triangle.incenter (T : Triangle) : Point :=
  let a := T.side_a
  let b := T.side_b
  let c := T.side_c
  let p := a + b + c
  ((a * T.A.1 + b * T.B.1 + c * T.C.1) / p, (a * T.A.2 + b * T.B.2 + c * T.C.2) / p)

/-- The inradius r: area / semi-perimeter -/
def Triangle.inradius (T : Triangle) : ℝ :=
  T.area / T.semiperimeter

/-- Excircle center opposite to A (touches side BC) -/
def Triangle.excenter_a (T : Triangle) : Point :=
  let a := T.side_a
  let b := T.side_b
  let c := T.side_c
  let p := -a + b + c
  ((-a * T.A.1 + b * T.B.1 + c * T.C.1) / p, (-a * T.A.2 + b * T.B.2 + c * T.C.2) / p)

/-- Excircle center opposite to B (touches side CA) -/
def Triangle.excenter_b (T : Triangle) : Point :=
  let a := T.side_a
  let b := T.side_b
  let c := T.side_c
  let p := a - b + c
  ((a * T.A.1 - b * T.B.1 + c * T.C.1) / p, (a * T.A.2 - b * T.B.2 + c * T.C.2) / p)

/-- Excircle center opposite to C (touches side AB) -/
def Triangle.excenter_c (T : Triangle) : Point :=
  let a := T.side_a
  let b := T.side_b
  let c := T.side_c
  let p := a + b - c
  ((a * T.A.1 + b * T.B.1 - c * T.C.1) / p, (a * T.A.2 + b * T.B.2 - c * T.C.2) / p)

/-- Exradius opposite to A: r_a = area / (s - a) -/
def Triangle.exradius_a (T : Triangle) : ℝ :=
  T.area / (T.semiperimeter - T.side_a)

/-- Exradius opposite to B: r_b = area / (s - b) -/
def Triangle.exradius_b (T : Triangle) : ℝ :=
  T.area / (T.semiperimeter - T.side_b)

/-- Exradius opposite to C: r_c = area / (s - c) -/
def Triangle.exradius_c (T : Triangle) : ℝ :=
  T.area / (T.semiperimeter - T.side_c)

-- ============================================================
-- PART 5: Tangency Definitions
-- ============================================================

/-- Two circles (given by center and radius) are internally tangent if the distance
    between centers equals the absolute difference of radii -/
def circlesInternallyTangent (c₁ r₁ c₂ r₂ : ℝ × ℝ × ℝ) : Prop :=
  dist2 (c₁.1, c₁.2.1) (c₂.1, c₂.2.1) = abs (c₁.2.2 - c₂.2.2)

/-- Two circles (given by center and radius) are externally tangent if the distance
    between centers equals the sum of radii -/
def circlesExternallyTangent (c₁ c₂ : Point) (r₁ r₂ : ℝ) : Prop :=
  dist2 c₁ c₂ = r₁ + r₂

-- ============================================================
-- PART 6: Key Relations for Feuerbach's Theorem
-- ============================================================

/-- The Euler line relation: O, G, H are collinear with G dividing OH in ratio 1:2.
    This is formalized as: G = (2O + H) / 3. -/
theorem euler_line_relation (T : Triangle) :
    T.centroid = ((2 * T.circumcenter.1 + T.orthocenter.1) / 3,
                  (2 * T.circumcenter.2 + T.orthocenter.2) / 3) := by
  unfold Triangle.centroid Triangle.orthocenter
  exact Prod.ext (by ring) (by ring)

/-- The nine-point center lies on the Euler line, midway between O and H -/
theorem ninePointCenter_on_euler_line (T : Triangle) :
    T.ninePointCenter = pointMidpoint T.circumcenter T.orthocenter := by
  unfold Triangle.ninePointCenter pointMidpoint
  exact Prod.ext (by ring) (by ring)

-- ============================================================
-- PART 8: Nine-Point Circle Properties
-- ============================================================

/-- The nine-point circle radius is half the circumradius: R₉ = R/2 -/
theorem ninePointRadius_eq_half_circumradius (T : Triangle) :
    T.ninePointRadius = T.circumradius / 2 := rfl

/-- Two nonneg reals with equal squares are equal -/
lemma eq_of_sq_eq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have h1 : (a - b) * (a + b) = 0 := by nlinarith
  rcases mul_eq_zero.mp h1 with hab | hab
  · linarith
  · linarith

/-- dist2 is nonneg -/
lemma dist2_nonneg (P Q : Point) : 0 ≤ dist2 P Q := by
  unfold dist2; exact Real.sqrt_nonneg _

/-- ninePointRadius is nonneg -/
lemma ninePointRadius_nonneg (T : Triangle) : 0 ≤ T.ninePointRadius := by
  unfold Triangle.ninePointRadius
  exact div_nonneg (dist2_nonneg _ _) (by norm_num)

/-- The circumcenter denominator is nonzero (follows from nondegenerate). -/
lemma circumcenter_denom_ne_zero (T : Triangle) :
    2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2)) ≠ 0 := by
  intro h
  apply T.nondegenerate
  nlinarith

-- The perpendicular bisector condition: (B-A) dot (B+A-2O) = 0.
-- This is LINEAR in O, so much easier to verify by ring than the quadratic form.
set_option maxHeartbeats 6400000 in
private lemma circumcenter_perp_bisector_AB (T : Triangle) :
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

-- The circumcenter is equidistant from B and A (squared version).
private lemma circumcenter_equidist_sq_B (T : Triangle) :
    (T.B.1 - T.circumcenter.1) ^ 2 + (T.B.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := circumcenter_perp_bisector_AB T
  nlinarith [sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.B.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

-- The perpendicular bisector condition for AC.
set_option maxHeartbeats 6400000 in
private lemma circumcenter_perp_bisector_AC (T : Triangle) :
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

-- The circumcenter is equidistant from C and A (squared version).
private lemma circumcenter_equidist_sq_C (T : Triangle) :
    (T.C.1 - T.circumcenter.1) ^ 2 + (T.C.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := circumcenter_perp_bisector_AC T
  nlinarith [sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.C.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- General nine-point membership: if P - N = (O - V)/2 for some vertex V
    with dist(O,V)² = R², then dist(N, P) = R/2. -/
private lemma ninepoint_membership (T : Triangle) (P : Point)
    (dx dy : ℝ)
    (hx : P.1 - T.ninePointCenter.1 = dx)
    (hy : P.2 - T.ninePointCenter.2 = dy)
    (hsq : dx ^ 2 + dy ^ 2 =
      ((T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2) / 4) :
    dist2 T.ninePointCenter P = T.ninePointRadius := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _) (ninePointRadius_nonneg _)
  unfold dist2
  rw [Real.sq_sqrt (by positivity : 0 ≤ (P.1 - T.ninePointCenter.1) ^ 2 +
      (P.2 - T.ninePointCenter.2) ^ 2)]
  unfold Triangle.ninePointRadius Triangle.circumradius dist2
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (T.A.1 - T.circumcenter.1) ^ 2 +
      (T.A.2 - T.circumcenter.2) ^ 2)]
  rw [hx, hy]
  linarith

/-- The midpoint of side BC lies on the nine-point circle.
    Key: M_a - N = (O - A)/2, and |O - A| = R. -/
theorem midpoint_a_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_a = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.circumcenter.1 - T.A.1) / 2) ((T.circumcenter.2 - T.A.2) / 2)
  · unfold Triangle.midpoint_a Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_a Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · ring

/-- The midpoint of side CA lies on the nine-point circle.
    Key: M_b - N = (O - B)/2, and |O - B| = |O - A| = R. -/
theorem midpoint_b_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_b = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.circumcenter.1 - T.B.1) / 2) ((T.circumcenter.2 - T.B.2) / 2)
  · unfold Triangle.midpoint_b Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_b Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · have h := circumcenter_equidist_sq_B T
    nlinarith [sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.B.2 - T.circumcenter.2),
               sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- The midpoint of side AB lies on the nine-point circle.
    Key: M_c - N = (O - C)/2, and |O - C| = |O - A| = R. -/
theorem midpoint_c_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_c = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.circumcenter.1 - T.C.1) / 2) ((T.circumcenter.2 - T.C.2) / 2)
  · unfold Triangle.midpoint_c Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_c Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · have h := circumcenter_equidist_sq_C T
    nlinarith [sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.C.2 - T.circumcenter.2),
               sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- The midpoint of AH lies on the nine-point circle.
    Key: mid(A,H) - N = (A - O)/2, and |A - O| = R. -/
theorem midpoint_AH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_AH = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.A.1 - T.circumcenter.1) / 2) ((T.A.2 - T.circumcenter.2) / 2)
  · unfold Triangle.midpoint_AH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_AH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · ring

/-- The midpoint of BH lies on the nine-point circle.
    Key: mid(B,H) - N = (B - O)/2, and |B - O| = |A - O| = R. -/
theorem midpoint_BH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_BH = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.B.1 - T.circumcenter.1) / 2) ((T.B.2 - T.circumcenter.2) / 2)
  · unfold Triangle.midpoint_BH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_BH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · have h := circumcenter_equidist_sq_B T
    nlinarith [sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.B.2 - T.circumcenter.2),
               sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- The midpoint of CH lies on the nine-point circle.
    Key: mid(C,H) - N = (C - O)/2, and |C - O| = |A - O| = R. -/
theorem midpoint_CH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_CH = T.ninePointRadius := by
  apply ninepoint_membership T _
    ((T.C.1 - T.circumcenter.1) / 2) ((T.C.2 - T.circumcenter.2) / 2)
  · unfold Triangle.midpoint_CH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · unfold Triangle.midpoint_CH Triangle.ninePointCenter pointMidpoint Triangle.orthocenter; ring
  · have h := circumcenter_equidist_sq_C T
    nlinarith [sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.C.2 - T.circumcenter.2),
               sq_nonneg (T.A.1 - T.circumcenter.1), sq_nonneg (T.A.2 - T.circumcenter.2)]

-- ============================================================
-- PART 8b: Altitude Feet on the Nine-Point Circle
-- ============================================================

/-- Side BC has positive length squared (follows from nondegeneracy). -/
lemma bc_sq_ne_zero (T : Triangle) :
    (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := by
  intro h
  apply T.nondegenerate
  have hx : T.C.1 = T.B.1 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  have hy : T.C.2 = T.B.2 := by nlinarith [sq_nonneg (T.C.1 - T.B.1), sq_nonneg (T.C.2 - T.B.2)]
  rw [hx, hy]; ring

/-- Side CA has positive length squared (follows from nondegeneracy). -/
lemma ca_sq_ne_zero (T : Triangle) :
    (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := by
  intro h
  apply T.nondegenerate
  have hx : T.A.1 = T.C.1 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  have hy : T.A.2 = T.C.2 := by nlinarith [sq_nonneg (T.A.1 - T.C.1), sq_nonneg (T.A.2 - T.C.2)]
  rw [hx, hy]; ring

/-- Side AB has positive length squared (follows from nondegeneracy). -/
lemma ab_sq_ne_zero (T : Triangle) :
    (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := by
  intro h
  apply T.nondegenerate
  have hx : T.B.1 = T.A.1 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  have hy : T.B.2 = T.A.2 := by nlinarith [sq_nonneg (T.B.1 - T.A.1), sq_nonneg (T.B.2 - T.A.2)]
  rw [hx, hy]; ring

set_option maxHeartbeats 25600000 in
/-- The foot of altitude from A lies on the nine-point circle.

    **Proof strategy**: Show |H_a - N|² = R²/4. After clearing the
    denominator |BC|² and circumcenter denominator d, this reduces to
    a polynomial identity in the vertex coordinates. -/
theorem foot_a_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.foot_a = T.ninePointRadius := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _) (ninePointRadius_nonneg _)
  have hlhs : dist2 T.ninePointCenter T.foot_a ^ 2 =
    dist2_sq T.ninePointCenter T.foot_a := by
    unfold dist2 dist2_sq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hrhs : T.ninePointRadius ^ 2 =
    dist2_sq T.circumcenter T.A / 4 := by
    unfold Triangle.ninePointRadius Triangle.circumradius dist2 dist2_sq
    rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    norm_num
  rw [hlhs, hrhs]
  unfold dist2_sq Triangle.foot_a Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  simp only []
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  set bc_sq := (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2
  have hbc_ne : bc_sq ≠ 0 := bc_sq_ne_zero T
  field_simp [hd_ne, hbc_ne]
  ring

set_option maxHeartbeats 25600000 in
/-- The foot of altitude from B lies on the nine-point circle. -/
theorem foot_b_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.foot_b = T.ninePointRadius := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _) (ninePointRadius_nonneg _)
  have hlhs : dist2 T.ninePointCenter T.foot_b ^ 2 =
    dist2_sq T.ninePointCenter T.foot_b := by
    unfold dist2 dist2_sq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hrhs : T.ninePointRadius ^ 2 =
    dist2_sq T.circumcenter T.A / 4 := by
    unfold Triangle.ninePointRadius Triangle.circumradius dist2 dist2_sq
    rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    norm_num
  rw [hlhs, hrhs]
  unfold dist2_sq Triangle.foot_b Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  simp only []
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  set ca_sq := (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2
  have hca_ne : ca_sq ≠ 0 := ca_sq_ne_zero T
  field_simp [hd_ne, hca_ne]
  ring

set_option maxHeartbeats 25600000 in
/-- The foot of altitude from C lies on the nine-point circle. -/
theorem foot_c_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.foot_c = T.ninePointRadius := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _) (ninePointRadius_nonneg _)
  have hlhs : dist2 T.ninePointCenter T.foot_c ^ 2 =
    dist2_sq T.ninePointCenter T.foot_c := by
    unfold dist2 dist2_sq
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  have hrhs : T.ninePointRadius ^ 2 =
    dist2_sq T.circumcenter T.A / 4 := by
    unfold Triangle.ninePointRadius Triangle.circumradius dist2 dist2_sq
    rw [div_pow, Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    norm_num
  rw [hlhs, hrhs]
  unfold dist2_sq Triangle.foot_c Triangle.ninePointCenter pointMidpoint
    Triangle.orthocenter Triangle.circumcenter
  simp only []
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  set ab_sq := (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2
  have hab_ne : ab_sq ≠ 0 := ab_sq_ne_zero T
  field_simp [hd_ne, hab_ne]
  ring

/-- **The Nine-Point Circle passes through all 9 special points.**
    Summary of all nine point memberships:
    - 3 side midpoints: M_a, M_b, M_c
    - 3 Euler midpoints: mid(A,H), mid(B,H), mid(C,H)
    - 3 altitude feet: H_a, H_b, H_c -/
theorem ninePoints_all_on_circle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_a = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_b = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_c = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_AH = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_BH = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_CH = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.foot_a = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.foot_b = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.foot_c = T.ninePointRadius :=
  ⟨midpoint_a_on_ninePointCircle T,
   midpoint_b_on_ninePointCircle T,
   midpoint_c_on_ninePointCircle T,
   midpoint_AH_on_ninePointCircle T,
   midpoint_BH_on_ninePointCircle T,
   midpoint_CH_on_ninePointCircle T,
   foot_a_on_ninePointCircle T,
   foot_b_on_ninePointCircle T,
   foot_c_on_ninePointCircle T⟩

-- ============================================================
-- PART 12: Numerical Verification
-- ============================================================

/-- Example: 3-4-5 right triangle

    For a right triangle with legs 3 and 4, hypotenuse 5:
    - The circumradius R = 5/2 (half the hypotenuse)
    - The nine-point radius = 5/4
    - The inradius r = 1 -/
def triangle_345 : Triangle := {
  A := (0, 0)
  B := (3, 0)
  C := (0, 4)
  nondegenerate := by norm_num
}

theorem triangle_345_area : triangle_345.area = 6 := by
  unfold triangle_345 Triangle.area
  norm_num

theorem triangle_345_semiperimeter : triangle_345.semiperimeter = 6 := by
  unfold triangle_345 Triangle.semiperimeter Triangle.side_a Triangle.side_b Triangle.side_c
  simp only
  have h1 : Real.sqrt (((0 : ℝ) - 3)^2 + (4 - 0)^2) = 5 := by
    have : ((0 : ℝ) - 3) ^ 2 + (4 - 0) ^ 2 = 5 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num : (5 : ℝ) ≥ 0)]
  have h2 : Real.sqrt (((0 : ℝ) - 0)^2 + (0 - 4)^2) = 4 := by
    have : ((0 : ℝ) - 0) ^ 2 + (0 - 4) ^ 2 = 4 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num : (4 : ℝ) ≥ 0)]
  have h3 : Real.sqrt (((3 : ℝ) - 0)^2 + (0 - 0)^2) = 3 := by
    have : ((3 : ℝ) - 0) ^ 2 + (0 - 0) ^ 2 = 3 ^ 2 := by norm_num
    rw [this, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]
  rw [h1, h2, h3]
  norm_num

theorem triangle_345_inradius : triangle_345.inradius = 1 := by
  unfold Triangle.inradius
  rw [triangle_345_area, triangle_345_semiperimeter]
  norm_num

/-- Helper: side lengths of the 3-4-5 triangle -/
lemma triangle_345_side_a : triangle_345.side_a = 5 := by
  unfold triangle_345 Triangle.side_a; simp only
  have : ((0 : ℝ) - 3) ^ 2 + (4 - 0) ^ 2 = 5 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (5 : ℝ) ≥ 0)]

lemma triangle_345_side_b : triangle_345.side_b = 4 := by
  unfold triangle_345 Triangle.side_b; simp only
  have : ((0 : ℝ) - 0) ^ 2 + (0 - 4) ^ 2 = 4 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (4 : ℝ) ≥ 0)]

lemma triangle_345_side_c : triangle_345.side_c = 3 := by
  unfold triangle_345 Triangle.side_c; simp only
  have : ((3 : ℝ) - 0) ^ 2 + (0 - 0) ^ 2 = 3 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (3 : ℝ) ≥ 0)]

/-- Circumcenter of 3-4-5 triangle is at (3/2, 2) = midpoint of hypotenuse -/
theorem triangle_345_circumcenter : triangle_345.circumcenter = (3/2, 2) := by
  unfold triangle_345 Triangle.circumcenter; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- Circumradius of 3-4-5 right triangle is 5/2 (half the hypotenuse) -/
theorem triangle_345_circumradius : triangle_345.circumradius = 5 / 2 := by
  unfold Triangle.circumradius
  rw [triangle_345_circumcenter]
  unfold triangle_345 dist2; simp only
  have : ((0 : ℝ) - 3 / 2) ^ 2 + ((0 : ℝ) - 2) ^ 2 = (5/2) ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num : (5/2 : ℝ) ≥ 0)]

/-- Nine-point radius of 3-4-5 triangle is 5/4 -/
theorem triangle_345_ninePointRadius : triangle_345.ninePointRadius = 5 / 4 := by
  unfold Triangle.ninePointRadius
  rw [triangle_345_circumradius]; ring

/-- Orthocenter of 3-4-5 right triangle is at the right angle vertex (0,0) -/
theorem triangle_345_orthocenter : triangle_345.orthocenter = (0, 0) := by
  unfold Triangle.orthocenter
  rw [triangle_345_circumcenter]
  unfold triangle_345; simp only
  exact Prod.ext (by ring) (by ring)

/-- Nine-point center of 3-4-5 triangle is at (3/4, 1) -/
theorem triangle_345_ninePointCenter : triangle_345.ninePointCenter = (3/4, 1) := by
  unfold Triangle.ninePointCenter
  rw [triangle_345_orthocenter, triangle_345_circumcenter]
  unfold pointMidpoint; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- Incenter of 3-4-5 triangle is at (1, 1) -/
theorem triangle_345_incenter : triangle_345.incenter = (1, 1) := by
  unfold Triangle.incenter
  simp only [triangle_345_side_a, triangle_345_side_b, triangle_345_side_c]
  unfold triangle_345; simp only
  exact Prod.ext (by norm_num) (by norm_num)

/-- **Feuerbach verified for 3-4-5 triangle (incircle tangency)**
    |NI| = |R/2 - r| = |5/4 - 1| = 1/4 -/
theorem triangle_345_feuerbach_incircle :
    dist2 triangle_345.ninePointCenter triangle_345.incenter =
    abs (triangle_345.ninePointRadius - triangle_345.inradius) := by
  rw [triangle_345_ninePointCenter, triangle_345_incenter,
      triangle_345_ninePointRadius, triangle_345_inradius]
  unfold dist2; simp only
  have hlhs : ((1 : ℝ) - 3/4) ^ 2 + (1 - 1) ^ 2 = (1/4) ^ 2 := by norm_num
  rw [hlhs, Real.sqrt_sq (by norm_num : (1/4 : ℝ) ≥ 0)]
  norm_num

end FeuerbachsTheorem

end
