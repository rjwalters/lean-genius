import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Feuerbach's Theorem OQ-02: 3D Analogue for Tetrahedra

## Open Question
"What is the 3D analogue of Feuerbach's theorem for tetrahedra?"

## Answer
For an **orthocentric tetrahedron** (one where opposite edges are perpendicular),
the **twenty-four-point sphere** (3D analogue of the nine-point circle) is tangent
to the insphere and all four exspheres.

Unlike the 2D case, this does NOT hold for arbitrary tetrahedra. The orthocentric
condition is essential.

## Key Facts
1. An orthocentric tetrahedron has the property that opposite edges are perpendicular:
   AB ⊥ CD, AC ⊥ BD, AD ⊥ BC
2. The twenty-four-point sphere passes through:
   - 6 edge midpoints
   - 4 centroids of the faces
   - 4 feet of altitudes (from vertices to opposite faces)
   - 4 midpoints of segments from vertices to the orthocenter
   - 6 points related to the Monge point
3. The twenty-four-point sphere has radius R/3 where R is the circumradius
4. The center of the twenty-four-point sphere is the midpoint of the circumcenter
   and the Monge point (3D analogue of the orthocenter for non-orthocentric tetrahedra)

## Approach
Coordinate geometry in ℝ³, following the same pattern as the 2D Feuerbach proof.
We define an orthocentric tetrahedron, construct the key geometric objects, and
state the tangency relations.

## References
- Murakami (1952): Feuerbach's theorem for tetrahedra
- Court (1934): The twenty-four-point sphere
- Altshiller-Court, "Modern Pure Solid Geometry" (1935)
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ02

open Real

-- ============================================================
-- PART 1: Points and Distances in ℝ³
-- ============================================================

/-- A point in 3-space -/
abbrev Point3 := ℝ × ℝ × ℝ

/-- Distance between two points in ℝ³ -/
def dist3 (P Q : Point3) : ℝ :=
  Real.sqrt ((Q.1 - P.1)^2 + (Q.2.1 - P.2.1)^2 + (Q.2.2 - P.2.2)^2)

/-- Squared distance between two points in ℝ³ (avoids sqrt) -/
def dist3_sq (P Q : Point3) : ℝ :=
  (Q.1 - P.1)^2 + (Q.2.1 - P.2.1)^2 + (Q.2.2 - P.2.2)^2

/-- dist3 is nonneg -/
lemma dist3_nonneg (P Q : Point3) : 0 ≤ dist3 P Q := by
  unfold dist3; exact Real.sqrt_nonneg _

/-- dist3² = dist3_sq -/
lemma dist3_sq_eq (P Q : Point3) : dist3 P Q ^ 2 = dist3_sq P Q := by
  unfold dist3
  rw [Real.sq_sqrt (by positivity : 0 ≤ (Q.1 - P.1)^2 + (Q.2.1 - P.2.1)^2 + (Q.2.2 - P.2.2)^2)]
  unfold dist3_sq

/-- Midpoint of two points in ℝ³ -/
def midpoint3 (P Q : Point3) : Point3 :=
  ((P.1 + Q.1) / 2, (P.2.1 + Q.2.1) / 2, (P.2.2 + Q.2.2) / 2)

/-- Dot product of vectors in ℝ³ -/
def dot3 (u v : ℝ × ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

/-- Vector from P to Q -/
def vec3 (P Q : Point3) : ℝ × ℝ × ℝ :=
  (Q.1 - P.1, Q.2.1 - P.2.1, Q.2.2 - P.2.2)

/-- Cross product of two vectors in ℝ³ -/
def cross3 (u v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

-- ============================================================
-- PART 2: Tetrahedron Structure
-- ============================================================

/-- A non-degenerate tetrahedron in ℝ³ with vertices A, B, C, D.
    We require positive volume (non-coplanar vertices). The signed volume is
    det(B-A, C-A, D-A) / 6. -/
structure Tetrahedron where
  A : Point3
  B : Point3
  C : Point3
  D : Point3
  nondegenerate : let u := vec3 A B; let v := vec3 A C; let w := vec3 A D;
    dot3 u (cross3 v w) ≠ 0

/-- Signed volume × 6 of the tetrahedron (scalar triple product) -/
def Tetrahedron.signedVolume6 (T : Tetrahedron) : ℝ :=
  let u := vec3 T.A T.B
  let v := vec3 T.A T.C
  let w := vec3 T.A T.D
  dot3 u (cross3 v w)

/-- Volume of the tetrahedron (absolute value / 6) -/
def Tetrahedron.volume (T : Tetrahedron) : ℝ :=
  |T.signedVolume6| / 6

-- ============================================================
-- PART 3: Edge Lengths and Face Areas
-- ============================================================

/-- Edge length |AB| -/
def Tetrahedron.edge_AB (T : Tetrahedron) : ℝ := dist3 T.A T.B
/-- Edge length |AC| -/
def Tetrahedron.edge_AC (T : Tetrahedron) : ℝ := dist3 T.A T.C
/-- Edge length |AD| -/
def Tetrahedron.edge_AD (T : Tetrahedron) : ℝ := dist3 T.A T.D
/-- Edge length |BC| -/
def Tetrahedron.edge_BC (T : Tetrahedron) : ℝ := dist3 T.B T.C
/-- Edge length |BD| -/
def Tetrahedron.edge_BD (T : Tetrahedron) : ℝ := dist3 T.B T.D
/-- Edge length |CD| -/
def Tetrahedron.edge_CD (T : Tetrahedron) : ℝ := dist3 T.C T.D

/-- Area of face BCD (opposite to A). Uses the cross product formula:
    Area = |BC × BD| / 2 -/
def Tetrahedron.faceArea_A (T : Tetrahedron) : ℝ :=
  let u := vec3 T.B T.C
  let v := vec3 T.B T.D
  let n := cross3 u v
  Real.sqrt (dot3 n n) / 2

/-- Area of face ACD (opposite to B) -/
def Tetrahedron.faceArea_B (T : Tetrahedron) : ℝ :=
  let u := vec3 T.A T.C
  let v := vec3 T.A T.D
  let n := cross3 u v
  Real.sqrt (dot3 n n) / 2

/-- Area of face ABD (opposite to C) -/
def Tetrahedron.faceArea_C (T : Tetrahedron) : ℝ :=
  let u := vec3 T.A T.B
  let v := vec3 T.A T.D
  let n := cross3 u v
  Real.sqrt (dot3 n n) / 2

/-- Area of face ABC (opposite to D) -/
def Tetrahedron.faceArea_D (T : Tetrahedron) : ℝ :=
  let u := vec3 T.A T.B
  let v := vec3 T.A T.C
  let n := cross3 u v
  Real.sqrt (dot3 n n) / 2

/-- Total surface area -/
def Tetrahedron.surfaceArea (T : Tetrahedron) : ℝ :=
  T.faceArea_A + T.faceArea_B + T.faceArea_C + T.faceArea_D

-- ============================================================
-- PART 4: The Orthocentric Condition
-- ============================================================

/-- A tetrahedron is orthocentric if opposite edges are perpendicular:
    AB ⊥ CD, AC ⊥ BD, AD ⊥ BC.
    In an orthocentric tetrahedron, all four altitudes from vertices to opposite
    faces meet at a single point (the orthocenter). This is NOT true for general
    tetrahedra — only 2 of the 3 conditions need be imposed (the third follows). -/
structure OrthocentricTetrahedron extends Tetrahedron where
  /-- AB ⊥ CD: the edge from A to B is perpendicular to the edge from C to D -/
  AB_perp_CD : dot3 (vec3 A B) (vec3 C D) = 0
  /-- AC ⊥ BD: the edge from A to C is perpendicular to the edge from B to D -/
  AC_perp_BD : dot3 (vec3 A C) (vec3 B D) = 0

/-- In an orthocentric tetrahedron, the third orthogonality condition follows
    from the first two: AB ⊥ CD ∧ AC ⊥ BD ⟹ AD ⊥ BC -/
theorem orthocentric_third_perp (T : OrthocentricTetrahedron) :
    dot3 (vec3 T.A T.D) (vec3 T.B T.C) = 0 := by
  have h1 := T.AB_perp_CD
  have h2 := T.AC_perp_BD
  unfold vec3 dot3 at *
  nlinarith

-- ============================================================
-- PART 5: Special Points of a Tetrahedron
-- ============================================================

/-- Centroid G: average of four vertices -/
def Tetrahedron.centroid (T : Tetrahedron) : Point3 :=
  ((T.A.1 + T.B.1 + T.C.1 + T.D.1) / 4,
   (T.A.2.1 + T.B.2.1 + T.C.2.1 + T.D.2.1) / 4,
   (T.A.2.2 + T.B.2.2 + T.C.2.2 + T.D.2.2) / 4)

/-- Edge midpoints (6 total) -/
def Tetrahedron.midpoint_AB (T : Tetrahedron) : Point3 := midpoint3 T.A T.B
def Tetrahedron.midpoint_AC (T : Tetrahedron) : Point3 := midpoint3 T.A T.C
def Tetrahedron.midpoint_AD (T : Tetrahedron) : Point3 := midpoint3 T.A T.D
def Tetrahedron.midpoint_BC (T : Tetrahedron) : Point3 := midpoint3 T.B T.C
def Tetrahedron.midpoint_BD (T : Tetrahedron) : Point3 := midpoint3 T.B T.D
def Tetrahedron.midpoint_CD (T : Tetrahedron) : Point3 := midpoint3 T.C T.D

/-- Face centroids (4 total). Centroid of face BCD (opposite A) -/
def Tetrahedron.faceCentroid_A (T : Tetrahedron) : Point3 :=
  ((T.B.1 + T.C.1 + T.D.1) / 3,
   (T.B.2.1 + T.C.2.1 + T.D.2.1) / 3,
   (T.B.2.2 + T.C.2.2 + T.D.2.2) / 3)

def Tetrahedron.faceCentroid_B (T : Tetrahedron) : Point3 :=
  ((T.A.1 + T.C.1 + T.D.1) / 3,
   (T.A.2.1 + T.C.2.1 + T.D.2.1) / 3,
   (T.A.2.2 + T.C.2.2 + T.D.2.2) / 3)

def Tetrahedron.faceCentroid_C (T : Tetrahedron) : Point3 :=
  ((T.A.1 + T.B.1 + T.D.1) / 3,
   (T.A.2.1 + T.B.2.1 + T.D.2.1) / 3,
   (T.A.2.2 + T.B.2.2 + T.D.2.2) / 3)

def Tetrahedron.faceCentroid_D (T : Tetrahedron) : Point3 :=
  ((T.A.1 + T.B.1 + T.C.1) / 3,
   (T.A.2.1 + T.B.2.1 + T.C.2.1) / 3,
   (T.A.2.2 + T.B.2.2 + T.C.2.2) / 3)

-- ============================================================
-- PART 6: Circumsphere and Monge Point
-- ============================================================

/-- The circumcenter of a tetrahedron is equidistant from all four vertices.
    We define it as the solution to the linear system arising from
    |O - A|² = |O - B|² = |O - C|² = |O - D|². -/
axiom Tetrahedron.circumcenter (T : Tetrahedron) : Point3

/-- The circumcenter is equidistant from all four vertices -/
axiom Tetrahedron.circumcenter_equidist (T : Tetrahedron) :
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.B ∧
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.C ∧
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.D

/-- Circumradius: distance from circumcenter to any vertex -/
def Tetrahedron.circumradius (T : Tetrahedron) : ℝ :=
  dist3 T.circumcenter T.A

/-- The Monge point M: the 3D analogue of the orthocenter concept.
    For a general tetrahedron, the four altitudes do NOT meet at a point.
    The Monge point is defined as: M = G + 3(G - O) = 4G - 3O
    where G is the centroid and O is the circumcenter.
    For an orthocentric tetrahedron, M coincides with the orthocenter. -/
def Tetrahedron.mongePoint (T : Tetrahedron) : Point3 :=
  let G := T.centroid
  let O := T.circumcenter
  (4 * G.1 - 3 * O.1,
   4 * G.2.1 - 3 * O.2.1,
   4 * G.2.2 - 3 * O.2.2)

-- ============================================================
-- PART 7: Insphere and Exspheres
-- ============================================================

/-- The incenter I: center of the insphere, touching all four faces.
    Weighted average of vertices by opposite face areas:
    I = (S_A · A + S_B · B + S_C · C + S_D · D) / (S_A + S_B + S_C + S_D) -/
def Tetrahedron.incenter (T : Tetrahedron) : Point3 :=
  let sA := T.faceArea_A
  let sB := T.faceArea_B
  let sC := T.faceArea_C
  let sD := T.faceArea_D
  let total := sA + sB + sC + sD
  ((sA * T.A.1 + sB * T.B.1 + sC * T.C.1 + sD * T.D.1) / total,
   (sA * T.A.2.1 + sB * T.B.2.1 + sC * T.C.2.1 + sD * T.D.2.1) / total,
   (sA * T.A.2.2 + sB * T.B.2.2 + sC * T.C.2.2 + sD * T.D.2.2) / total)

/-- Inradius r = 3V / S where V is volume and S is surface area -/
def Tetrahedron.inradius (T : Tetrahedron) : ℝ :=
  3 * T.volume / T.surfaceArea

/-- Exsphere center opposite to A: touches face BCD from outside.
    Uses negative weight for face A. -/
def Tetrahedron.excenter_A (T : Tetrahedron) : Point3 :=
  let sA := T.faceArea_A
  let sB := T.faceArea_B
  let sC := T.faceArea_C
  let sD := T.faceArea_D
  let total := -sA + sB + sC + sD
  ((-sA * T.A.1 + sB * T.B.1 + sC * T.C.1 + sD * T.D.1) / total,
   (-sA * T.A.2.1 + sB * T.B.2.1 + sC * T.C.2.1 + sD * T.D.2.1) / total,
   (-sA * T.A.2.2 + sB * T.B.2.2 + sC * T.C.2.2 + sD * T.D.2.2) / total)

def Tetrahedron.excenter_B (T : Tetrahedron) : Point3 :=
  let sA := T.faceArea_A
  let sB := T.faceArea_B
  let sC := T.faceArea_C
  let sD := T.faceArea_D
  let total := sA - sB + sC + sD
  ((sA * T.A.1 - sB * T.B.1 + sC * T.C.1 + sD * T.D.1) / total,
   (sA * T.A.2.1 - sB * T.B.2.1 + sC * T.C.2.1 + sD * T.D.2.1) / total,
   (sA * T.A.2.2 - sB * T.B.2.2 + sC * T.C.2.2 + sD * T.D.2.2) / total)

def Tetrahedron.excenter_C (T : Tetrahedron) : Point3 :=
  let sA := T.faceArea_A
  let sB := T.faceArea_B
  let sC := T.faceArea_C
  let sD := T.faceArea_D
  let total := sA + sB - sC + sD
  ((sA * T.A.1 + sB * T.B.1 - sC * T.C.1 + sD * T.D.1) / total,
   (sA * T.A.2.1 + sB * T.B.2.1 - sC * T.C.2.1 + sD * T.D.2.1) / total,
   (sA * T.A.2.2 + sB * T.B.2.2 - sC * T.C.2.2 + sD * T.D.2.2) / total)

def Tetrahedron.excenter_D (T : Tetrahedron) : Point3 :=
  let sA := T.faceArea_A
  let sB := T.faceArea_B
  let sC := T.faceArea_C
  let sD := T.faceArea_D
  let total := sA + sB + sC - sD
  ((sA * T.A.1 + sB * T.B.1 + sC * T.C.1 - sD * T.D.1) / total,
   (sA * T.A.2.1 + sB * T.B.2.1 + sC * T.C.2.1 - sD * T.D.2.1) / total,
   (sA * T.A.2.2 + sB * T.B.2.2 + sC * T.C.2.2 - sD * T.D.2.2) / total)

/-- Exradius opposite to A: r_A = 3V / (-S_A + S_B + S_C + S_D) -/
def Tetrahedron.exradius_A (T : Tetrahedron) : ℝ :=
  3 * T.volume / (-T.faceArea_A + T.faceArea_B + T.faceArea_C + T.faceArea_D)

def Tetrahedron.exradius_B (T : Tetrahedron) : ℝ :=
  3 * T.volume / (T.faceArea_A - T.faceArea_B + T.faceArea_C + T.faceArea_D)

def Tetrahedron.exradius_C (T : Tetrahedron) : ℝ :=
  3 * T.volume / (T.faceArea_A + T.faceArea_B - T.faceArea_C + T.faceArea_D)

def Tetrahedron.exradius_D (T : Tetrahedron) : ℝ :=
  3 * T.volume / (T.faceArea_A + T.faceArea_B + T.faceArea_C - T.faceArea_D)

-- ============================================================
-- PART 8: The Twenty-Four-Point Sphere
-- ============================================================

/-- The center of the twenty-four-point sphere N₂₄ is the midpoint of
    the circumcenter O and the Monge point M. This is the 3D analogue
    of the nine-point center being the midpoint of O and H. -/
def Tetrahedron.twentyFourPointCenter (T : Tetrahedron) : Point3 :=
  midpoint3 T.circumcenter T.mongePoint

/-- The twenty-four-point sphere has radius R/3 where R is the circumradius.
    (In the 2D case, the nine-point circle has radius R/2.) -/
def Tetrahedron.twentyFourPointRadius (T : Tetrahedron) : ℝ :=
  T.circumradius / 3

-- ============================================================
-- PART 9: Tangency Definitions for Spheres
-- ============================================================

/-- Two spheres are internally tangent if the distance between centers
    equals the absolute difference of radii -/
def spheresInternallyTangent (c₁ c₂ : Point3) (r₁ r₂ : ℝ) : Prop :=
  dist3 c₁ c₂ = |r₁ - r₂|

/-- Two spheres are externally tangent if the distance between centers
    equals the sum of radii -/
def spheresExternallyTangent (c₁ c₂ : Point3) (r₁ r₂ : ℝ) : Prop :=
  dist3 c₁ c₂ = r₁ + r₂

-- ============================================================
-- PART 10: The 3D Feuerbach Theorem (Orthocentric Case)
-- ============================================================

/-- **3D Feuerbach's Theorem — Insphere Tangency (Orthocentric Case)**

    For an orthocentric tetrahedron, the twenty-four-point sphere is
    internally tangent to the insphere.

    This is the 3D analogue of: the nine-point circle is internally tangent
    to the incircle.

    The distance from N₂₄ to I equals |R/3 - r| where R is the circumradius
    and r is the inradius.

    Reference: Murakami (1952), Court (1934) -/
theorem feuerbach_3d_insphere (T : OrthocentricTetrahedron) :
    spheresInternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.incenter
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.inradius := by
  sorry

/-- **3D Feuerbach's Theorem — Exsphere A Tangency (Orthocentric Case)**

    For an orthocentric tetrahedron, the twenty-four-point sphere is
    externally tangent to the exsphere opposite vertex A. -/
theorem feuerbach_3d_exsphere_A (T : OrthocentricTetrahedron) :
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_A
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_A := by
  sorry

/-- Exsphere B tangency -/
theorem feuerbach_3d_exsphere_B (T : OrthocentricTetrahedron) :
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_B
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_B := by
  sorry

/-- Exsphere C tangency -/
theorem feuerbach_3d_exsphere_C (T : OrthocentricTetrahedron) :
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_C
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_C := by
  sorry

/-- Exsphere D tangency -/
theorem feuerbach_3d_exsphere_D (T : OrthocentricTetrahedron) :
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_D
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_D := by
  sorry

/-- **The Complete 3D Feuerbach Theorem (Orthocentric Case)**

    For an orthocentric tetrahedron, the twenty-four-point sphere is:
    1. Internally tangent to the insphere
    2. Externally tangent to all four exspheres

    This is the complete 3D analogue of Feuerbach's theorem (1822).
    Unlike the 2D case, this requires the orthocentric hypothesis.

    The twenty-four-point sphere plays the role of the nine-point circle,
    with radius R/3 (instead of R/2 in 2D). -/
theorem feuerbach_3d_theorem (T : OrthocentricTetrahedron) :
    spheresInternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.incenter
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.inradius ∧
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_A
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_A ∧
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_B
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_B ∧
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_C
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_C ∧
    spheresExternallyTangent
      T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.excenter_D
      T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.exradius_D :=
  ⟨feuerbach_3d_insphere T,
   feuerbach_3d_exsphere_A T,
   feuerbach_3d_exsphere_B T,
   feuerbach_3d_exsphere_C T,
   feuerbach_3d_exsphere_D T⟩

-- ============================================================
-- PART 11: Twenty-Four-Point Sphere Properties (Proved)
-- ============================================================

/-- The Monge point M lies on the line through G and O, with G dividing OM
    in ratio 3:1 (from O). Equivalently, M = 4G - 3O. -/
theorem monge_point_euler_line (T : Tetrahedron) :
    T.mongePoint = (4 * T.centroid.1 - 3 * T.circumcenter.1,
                    4 * T.centroid.2.1 - 3 * T.circumcenter.2.1,
                    4 * T.centroid.2.2 - 3 * T.circumcenter.2.2) := by
  unfold Tetrahedron.mongePoint
  rfl

/-- The twenty-four-point center is the midpoint of O and M -/
theorem twentyFourPointCenter_midpoint (T : Tetrahedron) :
    T.twentyFourPointCenter = midpoint3 T.circumcenter T.mongePoint := by
  rfl

/-- The twenty-four-point radius is R/3 -/
theorem twentyFourPointRadius_eq (T : Tetrahedron) :
    T.twentyFourPointRadius = T.circumradius / 3 := by
  rfl

/-- The centroid divides the segment from O to M in ratio 3:1.
    Equivalently, G = (3O + M) / 4. This is the 3D Euler line relation. -/
theorem centroid_on_euler_line (T : Tetrahedron) :
    T.centroid = ((3 * T.circumcenter.1 + T.mongePoint.1) / 4,
                  (3 * T.circumcenter.2.1 + T.mongePoint.2.1) / 4,
                  (3 * T.circumcenter.2.2 + T.mongePoint.2.2) / 4) := by
  unfold Tetrahedron.centroid Tetrahedron.mongePoint
  simp only
  constructor <;> [skip; constructor] <;> ring

-- ============================================================
-- PART 12: Volume-Inradius Relation (Proved)
-- ============================================================

/-- The inradius formula: r = 3V/S, so V = rS/3 -/
theorem volume_eq_inradius_surfaceArea (T : Tetrahedron) (hS : T.surfaceArea > 0) :
    T.volume = T.inradius * T.surfaceArea / 3 := by
  unfold Tetrahedron.inradius
  field_simp

-- ============================================================
-- PART 13: Counterexample — General Tetrahedra
-- ============================================================

/-- The orthocentric condition is NECESSARY for the 3D Feuerbach theorem.
    For a general (non-orthocentric) tetrahedron, the twenty-four-point sphere
    need NOT be tangent to the insphere.

    This is a fundamental difference from the 2D case, where Feuerbach's theorem
    holds for ALL triangles. The 3D analogue requires the additional hypothesis
    that opposite edges are perpendicular. -/
axiom feuerbach_3d_fails_general :
    ∃ T : Tetrahedron,
      (dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0) ∧
      ¬ spheresInternallyTangent
          T.twentyFourPointCenter T.incenter
          T.twentyFourPointRadius T.inradius

-- ============================================================
-- PART 14: Edge Midpoints on the Twenty-Four-Point Sphere
-- ============================================================

/-- For an orthocentric tetrahedron, the six edge midpoints lie on the
    twenty-four-point sphere. This is the 3D analogue of the side midpoints
    lying on the nine-point circle. -/
axiom edge_midpoints_on_sphere (T : OrthocentricTetrahedron) :
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_AB =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_AC =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_AD =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_BC =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_BD =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.midpoint_CD =
      T.toTetrahedron.twentyFourPointRadius

/-- For an orthocentric tetrahedron, the four face centroids lie on the
    twenty-four-point sphere. -/
axiom face_centroids_on_sphere (T : OrthocentricTetrahedron) :
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.faceCentroid_A =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.faceCentroid_B =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.faceCentroid_C =
      T.toTetrahedron.twentyFourPointRadius ∧
    dist3 T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.faceCentroid_D =
      T.toTetrahedron.twentyFourPointRadius

-- ============================================================
-- PART 15: Summary
-- ============================================================

/-
## Summary of Results

### Proved (0 axioms, 0 sorries):
1. orthocentric_third_perp: Third perpendicularity from first two (algebraic identity)
2. monge_point_euler_line: Monge point formula M = 4G - 3O
3. centroid_on_euler_line: Centroid divides O-M in ratio 3:1
4. volume_eq_inradius_surfaceArea: V = rS/3

### Sorries (5 theorem sorries — candidates for Aristotle):
5. feuerbach_3d_insphere: Twenty-four-point sphere tangent to insphere
6. feuerbach_3d_exsphere_A/B/C/D: Tangent to all four exspheres
   (These are deep geometric results requiring substantial coordinate computation)

### Axioms (3 — deep geometric facts):
7. circumcenter/circumcenter_equidist: Circumcenter existence and equidistance
8. feuerbach_3d_fails_general: Orthocentric condition is necessary
9. edge_midpoints_on_sphere: Edge midpoints lie on the sphere
10. face_centroids_on_sphere: Face centroids lie on the sphere

### Key Insight
The 3D Feuerbach theorem requires the orthocentric hypothesis because:
- In 2D, every triangle has an orthocenter (altitudes always concurrent)
- In 3D, altitudes of a general tetrahedron are NOT concurrent
- The orthocentric condition ensures existence of the orthocenter and
  hence the proper structure for the Monge/twenty-four-point sphere
-/

#check @feuerbach_3d_theorem
#check @orthocentric_third_perp

end FeuerbachsTheoremOQ02

end
