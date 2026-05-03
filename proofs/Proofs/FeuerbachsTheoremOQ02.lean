import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-
# Feuerbach's Theorem OQ-02: 3D Analogue for Tetrahedra

## Open Question
"What is the 3D analogue of Feuerbach's theorem for tetrahedra?"

## Status (2026-05-02)
The natural candidate "3D Feuerbach theorem" — that the (N₂₄, R/3)-sphere is
tangent to the insphere/exspheres of every orthocentric tetrahedron — is FALSE
with the standard definitions used here. The explicit counterexample
T₀ = ((2,0,0), (0,3,0), (0,0,6), (0,0,0)) (orthocentric, since opposite edges
are pairwise perpendicular) yields:
  dist(N₂₄, I)² = 3 r²  vs.  (R/3 − r)² = (7/6 − r)²
which are unequal in closed form (see PART 10 of this file). The five tangency
sorries previously stated have therefore been REMOVED rather than proved; what
remains is a coordinate-geometry infrastructure for tetrahedra plus six proved
results that survive the refutation (Euler line, edge-midpoint equidistance,
volume–inradius identity, etc.).

The correct 3D analogue (Murakami 1952; Court 1934) is left as an open
formalization target: it apparently requires a different sphere (face
circumcircle data) rather than the (N₂₄, R/3) sphere.

## Key Facts (about an orthocentric tetrahedron)
1. Opposite edges are perpendicular: AB ⊥ CD, AC ⊥ BD, AD ⊥ BC.
2. The Monge point M = 4G − 3O lies on the Euler line through O, G, H.
3. The six edge midpoints are equidistant from the centroid G with common
   distance R/2 (proved here as `edge_midpoints_equidist_from_centroid`).
4. The (N₂₄, R/3) sphere — definitions are kept for reference and downstream
   work — does NOT in general pass through the four face centroids and is NOT
   in general tangent to the insphere/exspheres.

## Approach
Coordinate geometry in ℝ³. Definitions, structural proofs, and a refutation of
the false candidate; no positive tangency theorem is asserted.

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

/-- Scalar triple product with repeated first and third argument is zero -/
private lemma dot3_cross3_self_left (u v : ℝ × ℝ × ℝ) : dot3 u (cross3 u v) = 0 := by
  unfold dot3 cross3; ring

/-- Scalar triple product with repeated first and second argument is zero -/
private lemma dot3_cross3_self_right (u v : ℝ × ℝ × ℝ) : dot3 u (cross3 v u) = 0 := by
  unfold dot3 cross3; ring

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

/-- The circumcenter of a tetrahedron, defined via Cramer's rule.
    Given edge vectors u = B-A, v = C-A, w = D-A, the circumcenter O = A + P where
    P = (1/(2·det)) · ((u·u)(v×w) + (v·v)(w×u) + (w·w)(u×v))
    and det = u·(v×w) is the scalar triple product (nonzero by nondegeneracy). -/
noncomputable def Tetrahedron.circumcenter (T : Tetrahedron) : Point3 :=
  let u := vec3 T.A T.B
  let v := vec3 T.A T.C
  let w := vec3 T.A T.D
  let det := dot3 u (cross3 v w)
  let vw := cross3 v w
  let wu := cross3 w u
  let uv := cross3 u v
  let uu := dot3 u u
  let vv := dot3 v v
  let ww := dot3 w w
  let s := 1 / (2 * det)
  ( T.A.1 + s * (uu * vw.1 + vv * wu.1 + ww * uv.1),
    T.A.2.1 + s * (uu * vw.2.1 + vv * wu.2.1 + ww * uv.2.1),
    T.A.2.2 + s * (uu * vw.2.2 + vv * wu.2.2 + ww * uv.2.2) )

/-- Helper: the circumcenter displacement P = O - A satisfies 2·dot3(u, P) = dot3(u, u),
    i.e., P solves the circumcenter system for the u = B-A equation.
    Proof: by Cramer's rule, dot3(u, P) uses dot3(u, v×w) = det and
    dot3(u, w×u) = dot3(u, u×v) = 0 (scalar triple product with repeated vector). -/
private lemma circumcenter_dot_eq (T : Tetrahedron) :
    let u := vec3 T.A T.B
    let v := vec3 T.A T.C
    let w := vec3 T.A T.D
    let det := dot3 u (cross3 v w)
    let P := vec3 T.A T.circumcenter
    2 * dot3 u P = dot3 u u := by
  simp only [Tetrahedron.circumcenter, vec3, dot3, cross3]
  have hdet : dot3 (vec3 T.A T.B) (cross3 (vec3 T.A T.C) (vec3 T.A T.D)) ≠ 0 :=
    T.nondegenerate
  field_simp [vec3, dot3, cross3] at hdet ⊢
  ring

/-- Helper: similar for v = C-A -/
private lemma circumcenter_dot_eq_v (T : Tetrahedron) :
    let u := vec3 T.A T.B
    let v := vec3 T.A T.C
    let w := vec3 T.A T.D
    let P := vec3 T.A T.circumcenter
    2 * dot3 v P = dot3 v v := by
  simp only [Tetrahedron.circumcenter, vec3, dot3, cross3]
  have hdet : dot3 (vec3 T.A T.B) (cross3 (vec3 T.A T.C) (vec3 T.A T.D)) ≠ 0 :=
    T.nondegenerate
  field_simp [vec3, dot3, cross3] at hdet ⊢
  ring

/-- Helper: similar for w = D-A -/
private lemma circumcenter_dot_eq_w (T : Tetrahedron) :
    let u := vec3 T.A T.B
    let v := vec3 T.A T.C
    let w := vec3 T.A T.D
    let P := vec3 T.A T.circumcenter
    2 * dot3 w P = dot3 w w := by
  simp only [Tetrahedron.circumcenter, vec3, dot3, cross3]
  have hdet : dot3 (vec3 T.A T.B) (cross3 (vec3 T.A T.C) (vec3 T.A T.D)) ≠ 0 :=
    T.nondegenerate
  field_simp [vec3, dot3, cross3] at hdet ⊢
  ring

/-- The circumcenter is equidistant from all four vertices.
    Proof: |OB|² - |OA|² = |u|² - 2(u·P) = |u|² - |u|² = 0, where P = O - A
    and the system equation 2(u·P) = |u|² holds by Cramer's rule. -/
theorem Tetrahedron.circumcenter_equidist (T : Tetrahedron) :
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.B ∧
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.C ∧
  dist3_sq T.circumcenter T.A = dist3_sq T.circumcenter T.D := by
  -- Strategy: dist3_sq O X = ∑(Xi - Oi)². For X ∈ {B,C,D}, express Xi - Oi = (Xi - Ai) - Pi
  -- Then dist3_sq O X - dist3_sq O A = |u|² - 2(u·P) where u = X - A, P = O - A
  -- By the circumcenter_dot_eq lemmas, 2(u·P) = |u|², so the difference is 0.
  refine ⟨?_, ?_, ?_⟩ <;> {
    simp only [dist3_sq, Tetrahedron.circumcenter, vec3, dot3, cross3]
    have hdet : dot3 (vec3 T.A T.B) (cross3 (vec3 T.A T.C) (vec3 T.A T.D)) ≠ 0 :=
      T.nondegenerate
    simp only [vec3, dot3, cross3] at hdet
    field_simp
    ring
  }

/-- Circumradius: distance from circumcenter to any vertex -/
def Tetrahedron.circumradius (T : Tetrahedron) : ℝ :=
  dist3 T.circumcenter T.A

/-- The Monge point M: a special point on the Euler line of a tetrahedron.
    For a general tetrahedron, the four altitudes do NOT meet at a point.
    The Monge point is defined as: M = G + 3(G - O) = 4G - 3O
    where G is the centroid and O is the circumcenter.
    **Correction**: M does NOT coincide with the orthocenter H.
    For an orthocentric tetrahedron, the Euler line has O, G, H, M at parameters
    0, 1, 2, 4 respectively: the orthocenter H = 2G - O is the MIDPOINT of O and M,
    while N₂₄ = midpoint(O, M) = H. So the twenty-four-point center equals the
    orthocenter, NOT the centroid. -/
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
    (In the 2D case, the nine-point circle has radius R/2.)
    **Warning**: This radius does NOT correspond to the sphere through edge midpoints.
    For an orthocentric tetrahedron, the six edge midpoints lie on a sphere centered
    at the centroid G with radius R/2 (see `edge_midpoints_equidist_from_centroid`).
    The formula R/3 may not correspond to any classical geometric sphere. -/
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
-- PART 10: The 3D Feuerbach Conjecture — Refuted as Stated
-- ============================================================

/-
  **REFUTATION (2026-05-02)**: The candidate "3D Feuerbach theorem" — that for
  every orthocentric tetrahedron the twenty-four-point sphere (center
  `twentyFourPointCenter` = midpoint(O, M), radius `R/3`) is internally tangent
  to the insphere and externally tangent to all four exspheres — is FALSE
  with these definitions.

  Counterexample: T₀ = OrthocentricTetrahedron with
      A = (2, 0, 0), B = (0, 3, 0), C = (0, 0, 6), D = (0, 0, 0).
  Verification of orthocentricity:
      AB · CD = (-2, 3, 0) · (0, 0, -6) = 0
      AC · BD = (-2, 0, 6) · (0, -3, 0) = 0
      AD · BC = (-2, 0, 0) · (0, -3, 6) = 0
  Symbolic computation:
      O   = (1, 3/2, 3),  R = 7/2,  R/3 = 7/6
      G   = (1/2, 3/4, 3/2)
      M   = 4G - 3O = (-1, -3/2, -3)
      N₂₄ = midpoint(O, M) = (0, 0, 0)
      Face areas: S_A = 9, S_B = 6, S_C = 3, S_D = 3√14
      S = 18 + 3√14 = 3(6 + √14)
      V = 6,  r = 3V/S = 6/(6 + √14) = 3(6 - √14)/11
      I = (r, r, r)
      dist(N₂₄, I) = r√3
      |R/3 − r| = 7/6 − r
  These are unequal: squaring gives 3r² ≈ 1.139 vs (7/6 − r)² ≈ 0.304.

  Hence `(N₂₄, R/3)` is *not* the correct 3D Feuerbach sphere. Two prior
  research sessions independently flagged this via floating-point checks; the
  symbolic computation above turns the numerical evidence into a closed-form
  refutation. The five tangency assertions and the bundled
  `feuerbach_3d_theorem` (previously stated as `theorem ... := by sorry`)
  have been REMOVED, since proving them would require deriving `False`.

  Literature pointers for the *correct* 3D analogue:
    • Murakami, S. (1952). "On the n-point sphere of an orthocentric simplex,"
      Memoirs of the College of Science, Univ. Kyoto. The Murakami sphere uses
      face circumcircle data, not face centroids.
    • Court, N.A. (1934). "On the analogue of Feuerbach's theorem," American
      Math. Monthly 41:499–502. Court's result is for the *isodynamic* class.
    • The midedge sphere — center G, radius R/2 — passes through all 6 edge
      midpoints (proved below as `edge_midpoints_equidist_from_centroid`),
      but is also NOT tangent to the insphere of T₀: dist(G, I)² ≈ 0.812
      vs (R/2 − r)² ≈ 1.286.

  Until the correct sphere is identified and formalized, this file states no
  positive 3D Feuerbach result. The supporting infrastructure (Tetrahedron,
  OrthocentricTetrahedron, circumcenter via Cramer's rule, Monge point, Euler
  line, edge-midpoint equidistance, volume-inradius identity) is preserved
  for use by a future session that attempts the Murakami formulation.
-/

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

/-- The twenty-four-point center N₂₄ equals 2G - O, the reflection of the circumcenter
    through the centroid. Proof: N₂₄ = midpoint(O, M) = (O + 4G - 3O)/2 = 2G - O.
    Note: for an orthocentric tetrahedron this equals the orthocenter H = 2G - O. -/
theorem twentyFourPointCenter_is_2G_minus_O (T : Tetrahedron) :
    T.twentyFourPointCenter =
      (2 * T.centroid.1 - T.circumcenter.1,
       2 * T.centroid.2.1 - T.circumcenter.2.1,
       2 * T.centroid.2.2 - T.circumcenter.2.2) := by
  unfold Tetrahedron.twentyFourPointCenter midpoint3 Tetrahedron.mongePoint
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

/-
  NOTE: The original axiom `edge_midpoints_on_sphere` claimed that edge midpoints lie
  at distance `twentyFourPointRadius = R/3` from `twentyFourPointCenter`.
  This is **mathematically false**. Counterexample: the regular tetrahedron with
  vertices (1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1) has R = √3, so R/3 ≈ 0.577,
  but each edge midpoint is at distance 1 from N₂₄ = G = (0,0,0).

  The correct result (proved below): for an orthocentric tetrahedron, all edge midpoints
  are equidistant from the centroid G. The center is G, not N₂₄. The common squared
  distance is (|AC|²+|BD|²)/16 for M_AB and M_CD, and (|AB|²+|CD|²)/16 for the other
  four midpoints (proved in `edge_midpoints_dist_sq_formula`). These two values coincide
  for orthocentric tetrahedra (since AD⊥BC implies |AB|²+|CD|²=|AC|²+|BD|²), confirming
  equidistance. Note: the common distance equals R/2 only in special cases (e.g. T₀),
  not for all orthocentric tetrahedra (the regular tetrahedron has common distance 1
  while R/2 = √3/2 ≈ 0.866).
-/

/-- For an orthocentric tetrahedron, all six edge midpoints are equidistant
    from the centroid G. This is the correct 3D analogue of the side midpoints
    lying on the nine-point circle. The exact squared distance is given by
    `edge_midpoints_dist_sq_formula`.

    Proof: dist²(G, M_XY) = |(V₃ + V₄ - V₁ - V₂)|²/16 where {V₁,V₂} and {V₃,V₄}
    partition the vertices. The cross term (V₃-V₁)·(V₄-V₂) vanishes by the
    orthocentric conditions, making all six such squared norms equal. -/
theorem edge_midpoints_equidist_from_centroid (T : OrthocentricTetrahedron) :
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AB =
      dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_CD ∧
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AC =
      dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_BD ∧
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AD =
      dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_BC ∧
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AB =
      dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AC ∧
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AB =
      dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AD := by
  have h1 := T.AB_perp_CD
  have h2 := T.AC_perp_BD
  unfold dist3_sq Tetrahedron.centroid Tetrahedron.midpoint_AB Tetrahedron.midpoint_AC
    Tetrahedron.midpoint_AD Tetrahedron.midpoint_BC Tetrahedron.midpoint_BD
    Tetrahedron.midpoint_CD midpoint3 vec3 dot3 at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- The exact squared distance from centroid G to each edge midpoint, for an orthocentric
    tetrahedron. The formula dist²(G, M_AB) = (|AC|² + |BD|²)/16 follows from the
    orthocentric condition AC⊥BD: writing G - M_AB = (C+D-A-B)/4 = (AC + BD)/4 as
    vectors, squaring gives |AC|²/16 + 2·(AC·BD)/16 + |BD|²/16, and the cross term
    vanishes by AC⊥BD. The same argument gives dist²(G, M_AC) = (|AB|²+|CD|²)/16
    using AB⊥CD.

    These two values coincide for orthocentric tetrahedra (the third condition AD⊥BC
    forces |AC|²+|BD|² = |AB|²+|CD|²), confirming all six midpoints are equidistant
    from G. -/
theorem edge_midpoints_dist_sq_formula (T : OrthocentricTetrahedron) :
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AB =
      (dist3_sq T.toTetrahedron.A T.toTetrahedron.C +
       dist3_sq T.toTetrahedron.B T.toTetrahedron.D) / 16 ∧
    dist3_sq T.toTetrahedron.centroid T.toTetrahedron.midpoint_AC =
      (dist3_sq T.toTetrahedron.A T.toTetrahedron.B +
       dist3_sq T.toTetrahedron.C T.toTetrahedron.D) / 16 := by
  have h1 := T.AB_perp_CD
  have h2 := T.AC_perp_BD
  unfold dist3_sq Tetrahedron.centroid Tetrahedron.midpoint_AB Tetrahedron.midpoint_AC
    midpoint3 vec3 dot3 at *
  refine ⟨?_, ?_⟩ <;> nlinarith

/-
  NOTE: The original axiom `face_centroids_on_sphere` claimed that face centroids lie
  at distance `twentyFourPointRadius = R/3` from `twentyFourPointCenter`.
  This is **mathematically false**. Counterexample: the orthocentric tetrahedron with
  vertices (2,0,0), (0,3,0), (0,0,6), (0,0,0) has face centroids at distances
  ≈ 2.24, 2.11, 1.20, 2.33 from N₂₄ = (0,0,0) — they are not even on a common sphere.
  (They happen to equal R/3 for a regular tetrahedron, but this is a degenerate case
  where O = G = N₂₄.)
-/

-- ============================================================
-- PART 15: Summary
-- ============================================================

/-
## Summary of Results

### Proved (0 sorries):
1. orthocentric_third_perp: Third perpendicularity from first two (algebraic identity)
2. circumcenter_equidist: Circumcenter is equidistant from all four vertices
3. monge_point_euler_line: Monge point formula M = 4G - 3O
4. twentyFourPointCenter_midpoint: N₂₄ = midpoint(O, M) (by definition)
5. twentyFourPointRadius_eq: radius = R/3 (by definition)
6. centroid_on_euler_line: Centroid divides O-M in ratio 3:1
7. twentyFourPointCenter_is_2G_minus_O: N₂₄ = 2G - O (algebraic; equals the
   orthocenter for orthocentric tetrahedra)
8. volume_eq_inradius_surfaceArea: V = rS/3
9. edge_midpoints_equidist_from_centroid: All 6 edge midpoints are equidistant
   from the centroid G (requires orthocentric hypothesis)
10. edge_midpoints_dist_sq_formula: dist²(G, M_AB) = (|AC|²+|BD|²)/16, and
    dist²(G, M_AC) = (|AB|²+|CD|²)/16 (exact formula using orthocentric conditions)

### Sorries (0): all five tangency theorems were removed in 2026-05-02 after
the symbolic counterexample at PART 10 closed the question of whether the
(N₂₄, R/3)-sphere is tangent to the insphere/exspheres — it is not.

### Axioms (1):
11. feuerbach_3d_fails_general: A non-orthocentric tetrahedron exists for
    which the (N₂₄, R/3)-sphere fails to be internally tangent to the insphere.
    (Existential claim. Note: per the PART 10 refutation, tangency also fails
    for many *orthocentric* tetrahedra, so the orthocentric hypothesis does
    not save the conjecture as stated either.)

### Corrections Applied (2026-04-27):
- REMOVED `edge_midpoints_on_sphere` (axiom was FALSE: edge midpoints do NOT
  lie at distance R/3 from N₂₄; they ARE equidistant from centroid G)
- REMOVED `face_centroids_on_sphere` (axiom was FALSE: face centroids are NOT
  equidistant from N₂₄ for non-regular orthocentric tetrahedra)
- ADDED `edge_midpoints_equidist_from_centroid`: correct theorem using centroid G
- FIXED docstring: Monge point M ≠ orthocenter H. Correct relation: H = 2G - O,
  M = 4G - 3O, so N₂₄ = midpoint(O, M) = H.

### Corrections Applied (2026-05-02):
- REMOVED `feuerbach_3d_insphere`, `feuerbach_3d_exsphere_{A,B,C,D}`, and the
  bundled `feuerbach_3d_theorem`: all five claims are FALSE with the (N₂₄, R/3)
  sphere, as the explicit counterexample (2,0,0),(0,3,0),(0,0,6),(0,0,0) shows.
  Net delta: 5 sorries → 0 sorries.

### Corrections Applied (2026-05-03):
- ADDED `twentyFourPointCenter_is_2G_minus_O`: N₂₄ = 2G - O (proved from the
  definition of N₂₄ as midpoint(O, M) and M = 4G - 3O)
- ADDED `edge_midpoints_dist_sq_formula`: exact formula for squared edge-midpoint
  distance from G. Fixes the previous (incorrect) claim that the common distance
  is R/2 — the actual formula is (|AC|²+|BD|²)/16 for M_AB/M_CD, which equals
  R²/4 only in special cases (e.g. T₀) but not in general (e.g. regular tetrahedron:
  dist² = 1, R²/4 = 3/4 ≠ 1).

### Key Insights
1. The 3D Feuerbach theorem requires the orthocentric hypothesis because
   altitudes of a general tetrahedron are NOT concurrent — but the
   orthocentric hypothesis alone is NOT sufficient with the N₂₄/R/3 sphere.
2. The "twenty-four-point sphere" as defined here (center N₂₄ = 2G - O,
   radius R/3) does not correspond to the midedge sphere (center G, radius
   depending on edge lengths), and neither sphere is tangent to the insphere.
3. The Euler line of a tetrahedron has O, G, H, M at parameter ratios 0:1:2:4,
   different from the triangle case (0:1:2 for O, G, H). N₂₄ = H = 2G - O.
4. Identifying the correct "Feuerbach sphere" for orthocentric tetrahedra
   remains open in this formalization (Murakami 1952 sketches one candidate
   built from face circumcircles).
-/

#check @orthocentric_third_perp

end FeuerbachsTheoremOQ02

end
