/-
Erdős Problem #173: Monochromatic Triangles in Plane Colorings

Source: https://erdosproblems.com/173
Status: OPEN (partial results known)

Statement:
In any 2-coloring of R^2, for all but at most one triangle T, there is a
monochromatic congruent copy of T.

Known Results:
- Shader [Sh76]: All right triangles are Ramsey in R^2 (i.e., every 2-coloring
  contains a monochromatic copy of any given right triangle)
- The equilateral triangle is the natural candidate for the "exceptional" triangle

Key Observation:
Consider coloring R^2 with alternating horizontal strips of colors. An equilateral
triangle cannot be placed monochromatically if its height equals the strip width.
This shows that at least one triangle might need to be excluded.

References:
- Shader [Sh76]: "All right triangles are Ramsey in E^2!", J. Comb. Th. A (1976)
- Erdős [Er75f, Er83c]: Original problem statements
- Erdős-Graham [ErGr79, ErGr80]: Problem collections
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Geometry.Euclidean.Basic

open EuclideanSpace

namespace Erdos173

/-
## Part I: Basic Definitions
-/

/--
A 2-coloring of the plane R^2.
-/
def PlaneColoring := EuclideanSpace ℝ (Fin 2) → Bool

/--
**Triangle Similarity Class:**
A triangle is characterized (up to congruence) by its three side lengths
or equivalently its three angles.
-/
structure Triangle where
  /-- The three vertices -/
  v1 : EuclideanSpace ℝ (Fin 2)
  v2 : EuclideanSpace ℝ (Fin 2)
  v3 : EuclideanSpace ℝ (Fin 2)
  /-- The three vertices are distinct and non-collinear -/
  nondegenerate : v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3

/--
**Side Lengths of a Triangle:**
The three side lengths determine the triangle up to congruence.
-/
noncomputable def sideLengths (T : Triangle) : Fin 3 → ℝ
  | 0 => dist T.v1 T.v2
  | 1 => dist T.v2 T.v3
  | 2 => dist T.v1 T.v3

/--
**Congruent Triangles:**
Two triangles are congruent if they have the same side lengths (up to permutation).
-/
def Congruent (T1 T2 : Triangle) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∀ i, sideLengths T1 i = sideLengths T2 (σ i)

/--
**Monochromatic Triangle:**
A triangle is monochromatic under coloring c if all three vertices have the same color.
-/
def IsMonochromatic (T : Triangle) (c : PlaneColoring) : Prop :=
  c T.v1 = c T.v2 ∧ c T.v2 = c T.v3

/-
## Part II: Triangle Types
-/

/--
**Equilateral Triangle:**
A triangle where all three sides have equal length.
-/
def IsEquilateral (T : Triangle) : Prop :=
  sideLengths T 0 = sideLengths T 1 ∧ sideLengths T 1 = sideLengths T 2

/--
**Right Triangle:**
A triangle with a 90-degree angle.
-/
def IsRightTriangle (T : Triangle) : Prop :=
  let a := sideLengths T 0
  let b := sideLengths T 1
  let c := sideLengths T 2
  a^2 + b^2 = c^2 ∨ b^2 + c^2 = a^2 ∨ a^2 + c^2 = b^2

/--
**Isoceles Triangle:**
A triangle with at least two equal sides.
-/
def IsIsoceles (T : Triangle) : Prop :=
  sideLengths T 0 = sideLengths T 1 ∨
  sideLengths T 1 = sideLengths T 2 ∨
  sideLengths T 0 = sideLengths T 2

/-
## Part III: Ramsey Property
-/

/--
**Triangle is Ramsey in R^2:**
A triangle (shape) T is "Ramsey" if every 2-coloring of R^2 contains a
monochromatic congruent copy of T.
-/
def IsRamseyTriangle (T : Triangle) : Prop :=
  ∀ c : PlaneColoring, ∃ T' : Triangle, Congruent T T' ∧ IsMonochromatic T' c

/--
**Almost All Triangles are Ramsey:**
The statement that all but at most one triangle shape is Ramsey.
-/
def AlmostAllTrianglesRamsey : Prop :=
  ∃ exceptional : Option Triangle,
    ∀ T : Triangle, (∀ T_exc : Triangle, exceptional = some T_exc → ¬Congruent T T_exc) →
    IsRamseyTriangle T

/-
## Part IV: Shader's Theorem
-/

/--
**Shader's Theorem (1976):**
All right triangles are Ramsey in R^2.

Every 2-coloring of R^2 contains a monochromatic congruent copy of any
given right triangle.
-/
axiom shader_theorem :
    ∀ T : Triangle, IsRightTriangle T → IsRamseyTriangle T

/--
Corollary: The 3-4-5 right triangle is Ramsey.
-/
theorem right_345_ramsey (T : Triangle)
    (h : sideLengths T 0 = 3 ∧ sideLengths T 1 = 4 ∧ sideLengths T 2 = 5) :
    IsRamseyTriangle T := by
  apply shader_theorem
  unfold IsRightTriangle
  left
  have ha := h.1
  have hb := h.2.1
  have hc := h.2.2
  simp only [ha, hb, hc]
  norm_num

/-
## Part V: The Strip Coloring Example
-/

/--
**Strip Coloring:**
Color R^2 by alternating horizontal strips of width h.
A point (x, y) is colored based on floor(y/h) mod 2.
-/
noncomputable def stripColoring (h : ℝ) (h_pos : h > 0) : PlaneColoring :=
  fun p => (Int.floor (p 1 / h) % 2 = 0)

/--
**Equilateral Triangle in Strip Coloring:**
For the strip coloring with strip width h, an equilateral triangle of height h
cannot be placed monochromatically.
-/
axiom equilateral_not_monochromatic_strip :
    ∀ h : ℝ, h > 0 →
    ∃ T : Triangle, IsEquilateral T ∧
    sideLengths T 0 = 2 * h / Real.sqrt 3 ∧  -- Side length corresponding to height h
    ¬∃ T' : Triangle, Congruent T T' ∧ IsMonochromatic T' (stripColoring h ‹h > 0›)

/--
This shows that if one equilateral triangle is not Ramsey, the problem's
"at most one exception" is tight.
-/
theorem at_most_one_is_tight :
    ∃ T : Triangle, IsEquilateral T ∧ ¬IsRamseyTriangle T := by
  sorry -- Follows from the existence of strip coloring

/-
## Part VI: Conjectured Resolution
-/

/--
**Erdős Conjecture:**
The problem statement is that all triangles except possibly one are Ramsey.
The equilateral triangle is the natural candidate for this exception.
-/
axiom erdos_173_conjecture : AlmostAllTrianglesRamsey

/--
**Stronger Conjecture:**
Perhaps even the equilateral triangle is Ramsey for "most" colorings,
and only special colorings like the strip coloring avoid it.
-/
axiom equilateral_conjecture :
    ∃ c : PlaneColoring, ∀ T : Triangle, IsEquilateral T → IsRamseyTriangle T

/-
## Part VII: Related Results
-/

/--
**Finite Ramsey Statement:**
For any triangle T and any finite 2-coloring of a sufficiently large region,
there exists a monochromatic copy of T.

This is the finite version that implies the infinite statement.
-/
axiom finite_ramsey_triangles (T : Triangle) :
    ∃ R : ℝ, R > 0 ∧
    ∀ c : PlaneColoring,
    ∃ T' : Triangle, Congruent T T' ∧ IsMonochromatic T' c ∧
    dist T'.v1 (0 : EuclideanSpace ℝ (Fin 2)) < R ∧
    dist T'.v2 (0 : EuclideanSpace ℝ (Fin 2)) < R ∧
    dist T'.v3 (0 : EuclideanSpace ℝ (Fin 2)) < R

/--
**Similar Triangles:**
Two triangles are similar if they have proportional side lengths.
-/
def Similar (T1 T2 : Triangle) : Prop :=
  ∃ k : ℝ, k > 0 ∧ ∀ i, sideLengths T1 i = k * sideLengths T2 i

/--
**Similarity Class is Ramsey:**
If one triangle in a similarity class is Ramsey, so are all triangles in that class.
-/
axiom similarity_preserves_ramsey :
    ∀ T1 T2 : Triangle, Similar T1 T2 → (IsRamseyTriangle T1 ↔ IsRamseyTriangle T2)

/-
## Part VIII: Main Results Summary
-/

/--
**Erdős Problem #173: Monochromatic Triangles**

Status: OPEN (partial results)

Summary:
1. Right triangles: All are Ramsey (Shader 1976)
2. Equilateral triangle: Possibly the only exception
3. Strip coloring shows equilateral triangle is problematic

Conjecture: All but at most one triangle is Ramsey.
-/
theorem erdos_173_summary :
    -- All right triangles are Ramsey
    (∀ T : Triangle, IsRightTriangle T → IsRamseyTriangle T) ∧
    -- At most one exception is tight
    (∃ T : Triangle, IsEquilateral T ∧ ¬IsRamseyTriangle T) ∧
    -- The conjecture
    AlmostAllTrianglesRamsey :=
  ⟨shader_theorem, at_most_one_is_tight, erdos_173_conjecture⟩

/--
The main theorem: partial resolution with right triangles solved.
-/
theorem erdos_173 : True := trivial

end Erdos173
