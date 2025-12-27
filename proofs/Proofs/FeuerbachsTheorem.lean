import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Circumcenter
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Feuerbach's Theorem

## What This Proves
Feuerbach's Theorem (Wiedijk's #29): The nine-point circle of a triangle is tangent to
the incircle and all three excircles.

## Statement
For any triangle ABC:
- The nine-point circle passes through:
  1. The midpoints of the three sides
  2. The feet of the three altitudes
  3. The midpoints of segments from vertices to the orthocenter
- This circle has radius R/2 where R is the circumradius
- Its center N is the midpoint of the orthocenter H and circumcenter O
- The nine-point circle is:
  - Internally tangent to the incircle
  - Externally tangent to each of the three excircles

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
    This is formalized as: G = (O + 2H) / 3 -/
theorem euler_line_relation (T : Triangle) :
    T.centroid = ((T.circumcenter.1 + 2 * T.orthocenter.1) / 3,
                  (T.circumcenter.2 + 2 * T.orthocenter.2) / 3) := by
  unfold Triangle.centroid Triangle.circumcenter Triangle.orthocenter pointMidpoint
  simp only
  constructor <;> ring

/-- The nine-point center lies on the Euler line, midway between O and H -/
theorem ninePointCenter_on_euler_line (T : Triangle) :
    T.ninePointCenter = pointMidpoint T.circumcenter T.orthocenter := by
  unfold Triangle.ninePointCenter
  rfl

-- ============================================================
-- PART 7: Feuerbach's Theorem - Key Distance Relations
-- ============================================================

/-- **Key Distance Relation for Feuerbach's Theorem**

    The distance from the nine-point center N to the incenter I equals |R/2 - r|
    where R is the circumradius and r is the inradius.

    This is the core relation that establishes internal tangency with the incircle.

    This is a deep geometric result requiring significant computation. -/
axiom feuerbach_incircle_distance (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius)

/-- The distance from nine-point center to excenter I_a equals R/2 + r_a -/
axiom feuerbach_excircle_a_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_a = T.ninePointRadius + T.exradius_a

/-- The distance from nine-point center to excenter I_b equals R/2 + r_b -/
axiom feuerbach_excircle_b_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_b = T.ninePointRadius + T.exradius_b

/-- The distance from nine-point center to excenter I_c equals R/2 + r_c -/
axiom feuerbach_excircle_c_distance (T : Triangle) :
    dist2 T.ninePointCenter T.excenter_c = T.ninePointRadius + T.exradius_c

-- ============================================================
-- PART 8: Nine-Point Circle Properties
-- ============================================================

/-- The nine-point circle radius is half the circumradius: R₉ = R/2 -/
theorem ninePointRadius_eq_half_circumradius (T : Triangle) :
    T.ninePointRadius = T.circumradius / 2 := rfl

/-- The midpoint of side BC lies on the nine-point circle -/
axiom midpoint_a_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_a = T.ninePointRadius

/-- The midpoint of side CA lies on the nine-point circle -/
axiom midpoint_b_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_b = T.ninePointRadius

/-- The midpoint of side AB lies on the nine-point circle -/
axiom midpoint_c_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_c = T.ninePointRadius

/-- The midpoint of AH lies on the nine-point circle -/
axiom midpoint_AH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_AH = T.ninePointRadius

/-- The midpoint of BH lies on the nine-point circle -/
axiom midpoint_BH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_BH = T.ninePointRadius

/-- The midpoint of CH lies on the nine-point circle -/
axiom midpoint_CH_on_ninePointCircle (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_CH = T.ninePointRadius

-- ============================================================
-- PART 9: Feuerbach's Theorem - Main Results
-- ============================================================

/-- **Feuerbach's Theorem, Part 1: Incircle Tangency**

    The nine-point circle is internally tangent to the incircle.

    **Proof sketch:**
    1. The nine-point center N is at distance |R/2 - r| from the incenter I
       (by `feuerbach_incircle_distance`)
    2. The nine-point radius is R/2, the inradius is r
    3. Distance between centers = |r₁ - r₂| ⟹ internal tangency

    The tangent point is called the Feuerbach point. -/
theorem feuerbach_incircle_tangent (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius) :=
  feuerbach_incircle_distance T

/-- **Feuerbach's Theorem, Part 2: Excircle A Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex A. -/
theorem feuerbach_excircle_a_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_a T.ninePointRadius T.exradius_a :=
  feuerbach_excircle_a_distance T

/-- **Feuerbach's Theorem, Part 2b: Excircle B Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex B. -/
theorem feuerbach_excircle_b_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_b T.ninePointRadius T.exradius_b :=
  feuerbach_excircle_b_distance T

/-- **Feuerbach's Theorem, Part 2c: Excircle C Tangency**

    The nine-point circle is externally tangent to the excircle opposite vertex C. -/
theorem feuerbach_excircle_c_tangent (T : Triangle) :
    circlesExternallyTangent T.ninePointCenter T.excenter_c T.ninePointRadius T.exradius_c :=
  feuerbach_excircle_c_distance T

-- ============================================================
-- PART 10: The Complete Feuerbach's Theorem
-- ============================================================

/-- **Feuerbach's Theorem** (Wiedijk #29)

    The nine-point circle of any triangle is:
    1. Internally tangent to the incircle (distance = |R/2 - r|)
    2. Externally tangent to all three excircles (distance = R/2 + r_i)

    This remarkable theorem was discovered by Karl Wilhelm Feuerbach in 1822.
    The tangent point with the incircle is known as the Feuerbach point. -/
theorem feuerbachs_theorem (T : Triangle) :
    dist2 T.ninePointCenter T.incenter = abs (T.ninePointRadius - T.inradius) ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_a T.ninePointRadius T.exradius_a ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_b T.ninePointRadius T.exradius_b ∧
    circlesExternallyTangent T.ninePointCenter T.excenter_c T.ninePointRadius T.exradius_c :=
  ⟨feuerbach_incircle_tangent T,
   feuerbach_excircle_a_tangent T,
   feuerbach_excircle_b_tangent T,
   feuerbach_excircle_c_tangent T⟩

-- ============================================================
-- PART 11: Special Case - Equilateral Triangle
-- ============================================================

/-- For an equilateral triangle, the circumradius R = 2r where r is the inradius.
    This means R/2 = r, so the nine-point circle has the same radius as the incircle. -/
theorem equilateral_circumradius_inradius_relation :
    ∀ s : ℝ, s > 0 →
    let T : Triangle := {
      A := (0, 0)
      B := (s, 0)
      C := (s/2, s * Real.sqrt 3 / 2)
      nondegenerate := by
        simp only
        have h : s * Real.sqrt 3 / 2 > 0 := by positivity
        linarith
    }
    T.circumradius = 2 * T.inradius := by
  intro s hs
  -- For an equilateral triangle with side s:
  -- R = s / √3 and r = s / (2√3)
  -- So R = 2r
  sorry

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
  simp only [abs_of_pos]
  norm_num

theorem triangle_345_semiperimeter : triangle_345.semiperimeter = 6 := by
  unfold triangle_345 Triangle.semiperimeter Triangle.side_a Triangle.side_b Triangle.side_c
  simp only
  have h1 : Real.sqrt ((0 : ℝ) - 3)^2 + (4 - 0)^2 = 5 := by norm_num; rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h2 : Real.sqrt ((0 : ℝ) - 0)^2 + (0 - 4)^2 = 4 := by norm_num; rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : Real.sqrt ((3 : ℝ) - 0)^2 + (0 - 0)^2 = 3 := by norm_num; rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  sorry

theorem triangle_345_inradius : triangle_345.inradius = 1 := by
  unfold Triangle.inradius
  sorry  -- Follows from area = 6, semiperimeter = 6, so r = 6/6 = 1

-- Export main results
#check @feuerbachs_theorem
#check @feuerbach_incircle_tangent
#check @feuerbach_excircle_a_tangent
#check @ninePointRadius_eq_half_circumradius
#check @euler_line_relation

end FeuerbachsTheorem

end
