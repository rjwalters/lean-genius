/-
  Erdős Problem #898: The Erdős-Mordell Inequality

  Source: https://erdosproblems.com/898
  Status: SOLVED (Mordell, 1937)
  Proposed by: Erdős (1935)

  Statement:
  If P is an interior point of triangle ABC, and X, Y, Z are the feet of
  the perpendiculars from P to sides BC, CA, AB respectively, then:

    PA + PB + PC ≥ 2(PX + PY + PZ)

  This elegant inequality relates distances from an interior point to
  vertices versus distances to sides. Equality holds iff ABC is equilateral
  and P is its center.

  History:
  - Erdős proposed this in 1935 in the American Mathematical Monthly
  - Mordell and Barrow independently proved it in 1937
  - Many alternative proofs have been found since

  Tags: geometry, inequalities, triangles, classical
-/

import Mathlib

namespace Erdos898

/-!
## Part I: Points and Triangles in ℝ²

We set up the geometric framework using Mathlib's Euclidean geometry.
-/

/-- A point in the Euclidean plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points. -/
noncomputable def dist (P Q : Point) : ℝ := ‖P - Q‖

/-- Three points form a non-degenerate triangle if they are not collinear. -/
def IsTriangle (A B C : Point) : Prop :=
  ¬Collinear ℝ ({A, B, C} : Set Point)

/-- A point P is in the interior of triangle ABC. -/
def IsInteriorPoint (P A B C : Point) : Prop :=
  sorry -- P is strictly inside the convex hull of {A, B, C}

/-!
## Part II: Perpendicular Feet

The foot of the perpendicular from P to a line segment.
-/

/-- The foot of the perpendicular from P to the line through A and B.
    This is the point X on line AB closest to P. -/
noncomputable def perpendicularFoot (P A B : Point) : Point :=
  sorry -- Orthogonal projection of P onto line AB

/-- The distance from P to its perpendicular foot on AB. -/
noncomputable def distToLine (P A B : Point) : ℝ :=
  dist P (perpendicularFoot P A B)

/-- The three feet of perpendiculars from P to the sides of triangle ABC. -/
structure PerpendicularFeet (P A B C : Point) where
  /-- Foot on side BC -/
  X : Point
  /-- Foot on side CA -/
  Y : Point
  /-- Foot on side AB -/
  Z : Point
  hX : X = perpendicularFoot P B C
  hY : Y = perpendicularFoot P C A
  hZ : Z = perpendicularFoot P A B

/-!
## Part III: The Erdős-Mordell Inequality

The main inequality: PA + PB + PC ≥ 2(PX + PY + PZ)
-/

/-- Sum of distances from P to the three vertices. -/
noncomputable def vertexDistanceSum (P A B C : Point) : ℝ :=
  dist P A + dist P B + dist P C

/-- Sum of distances from P to the three sides (perpendicular distances). -/
noncomputable def sideDistanceSum (P A B C : Point) : ℝ :=
  distToLine P B C + distToLine P C A + distToLine P A B

/-- The Erdős-Mordell inequality: vertex distances ≥ 2 × side distances. -/
def ErdosMordellInequality (P A B C : Point) : Prop :=
  vertexDistanceSum P A B C ≥ 2 * sideDistanceSum P A B C

/-- **The Erdős-Mordell Theorem** (Mordell, 1937):
    For any interior point P of a triangle ABC,
    PA + PB + PC ≥ 2(PX + PY + PZ). -/
axiom erdos_mordell_inequality (A B C P : Point)
    (hT : IsTriangle A B C) (hP : IsInteriorPoint P A B C) :
    ErdosMordellInequality P A B C

/-!
## Part IV: Equality Condition

Equality holds if and only if the triangle is equilateral and P is its center.
-/

/-- A triangle is equilateral if all sides have equal length. -/
def IsEquilateral (A B C : Point) : Prop :=
  dist A B = dist B C ∧ dist B C = dist C A

/-- The centroid (center of mass) of a triangle. -/
noncomputable def centroid (A B C : Point) : Point :=
  (1/3 : ℝ) • (A + B + C)

/-- The incenter of a triangle (center of inscribed circle). -/
noncomputable def incenter (A B C : Point) : Point :=
  sorry -- Weighted average by opposite side lengths

/-- For an equilateral triangle, centroid = incenter = circumcenter. -/
axiom equilateral_centers_coincide (A B C : Point) (h : IsEquilateral A B C) :
    centroid A B C = incenter A B C

/-- Equality in Erdős-Mordell holds iff equilateral with P at center. -/
axiom erdos_mordell_equality (A B C P : Point)
    (hT : IsTriangle A B C) (hP : IsInteriorPoint P A B C) :
    vertexDistanceSum P A B C = 2 * sideDistanceSum P A B C ↔
    IsEquilateral A B C ∧ P = centroid A B C

/-!
## Part V: Alternative Formulations

The inequality can be written in several equivalent ways.
-/

/-- Using the notation PA, PB, PC for vertex distances and
    d_a, d_b, d_c for distances to opposite sides. -/
def ErdosMordellAlt (PA PB PC d_a d_b d_c : ℝ) : Prop :=
  PA + PB + PC ≥ 2 * (d_a + d_b + d_c)

/-- The inequality also holds in stronger weighted forms. -/
axiom weighted_erdos_mordell (A B C P : Point)
    (hT : IsTriangle A B C) (hP : IsInteriorPoint P A B C) :
    let a := dist B C
    let b := dist C A
    let c := dist A B
    let PA := dist P A
    let PB := dist P B
    let PC := dist P C
    let d_a := distToLine P B C
    let d_b := distToLine P C A
    let d_c := distToLine P A B
    a * PA + b * PB + c * PC ≥ 2 * (a * d_a + b * d_b + c * d_c)

/-!
## Part VI: Proofs and History

The original proof and subsequent simplifications.
-/

/-- Mordell's original proof (1937) used trigonometric identities. -/
axiom mordell_proof : ∀ (A B C P : Point),
    IsTriangle A B C → IsInteriorPoint P A B C → ErdosMordellInequality P A B C

/-- Barrow's proof (1937) was independent and more elementary. -/
axiom barrow_proof : ∀ (A B C P : Point),
    IsTriangle A B C → IsInteriorPoint P A B C → ErdosMordellInequality P A B C

/-- Kazarinoff's proof (1957) used the law of cosines. -/
axiom kazarinoff_proof : ∀ (A B C P : Point),
    IsTriangle A B C → IsInteriorPoint P A B C → ErdosMordellInequality P A B C

/-- Bankoff's proof (1958) was particularly elegant. -/
axiom bankoff_proof : ∀ (A B C P : Point),
    IsTriangle A B C → IsInteriorPoint P A B C → ErdosMordellInequality P A B C

/-!
## Part VII: Generalizations

The inequality extends to higher dimensions and other settings.
-/

/-- The Erdős-Mordell inequality generalizes to tetrahedra in ℝ³.
    For a point P inside tetrahedron ABCD:
    PA + PB + PC + PD ≥ 2(d_a + d_b + d_c + d_d)
    where d_i is the distance from P to face i. -/
def ErdosMordellTetrahedron : Prop :=
  ∀ (A B C D P : EuclideanSpace ℝ (Fin 3)),
    sorry -- Analogous statement for tetrahedra

/-- The inequality for regular n-gons with interior point. -/
axiom erdos_mordell_polygon (n : ℕ) (hn : n ≥ 3) :
    sorry -- Sum of vertex distances ≥ 2 × sum of side distances

/-!
## Part VIII: Related Inequalities

Other classical triangle inequalities in the same family.
-/

/-- The triangle inequality: any side < sum of other two. -/
theorem triangle_inequality (A B C : Point) (hT : IsTriangle A B C) :
    dist A B < dist B C + dist C A ∧
    dist B C < dist C A + dist A B ∧
    dist C A < dist A B + dist B C := by
  sorry

/-- Viviani's theorem: In an equilateral triangle, the sum of distances
    from any interior point to the sides equals the altitude. -/
axiom viviani_theorem (A B C P : Point)
    (hE : IsEquilateral A B C) (hP : IsInteriorPoint P A B C) :
    sideDistanceSum P A B C = sorry -- altitude of the triangle

/-- The Weitzenböck inequality: For triangle with sides a, b, c and area S,
    a² + b² + c² ≥ 4√3 · S. -/
axiom weitzenbock_inequality (A B C : Point) (hT : IsTriangle A B C) :
    let a := dist B C
    let b := dist C A
    let c := dist A B
    a^2 + b^2 + c^2 ≥ 4 * Real.sqrt 3 * sorry -- area

/-!
## Part IX: Main Result

Erdős Problem #898 is SOLVED.
-/

/-- **Erdős Problem #898: SOLVED**

    The Erdős-Mordell inequality holds:
    PA + PB + PC ≥ 2(PX + PY + PZ)

    for any interior point P of triangle ABC, where X, Y, Z are the
    feet of perpendiculars from P to the sides.

    Equality holds iff ABC is equilateral and P is its center. -/
theorem erdos_898 (A B C P : Point)
    (hT : IsTriangle A B C) (hP : IsInteriorPoint P A B C) :
    ErdosMordellInequality P A B C :=
  erdos_mordell_inequality A B C P hT hP

/-- The problem was proposed by Erdős in 1935. -/
def erdos_898_year : ℕ := 1935

/-- The problem was solved by Mordell in 1937. -/
def mordell_solution_year : ℕ := 1937

#check erdos_898
#check erdos_mordell_equality

end Erdos898
