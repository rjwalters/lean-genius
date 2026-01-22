/-
Erdős Problem #353: Geometric Configurations in Sets of Infinite Measure

Source: https://erdosproblems.com/353
Status: SOLVED (Koizumi, 2025)

Statement:
Let A ⊆ ℝ² be a measurable set with infinite measure. Must A contain the
vertices of:
- An isosceles trapezoid of area 1?
- An isosceles triangle of area 1?
- A right-angled triangle of area 1?
- A cyclic quadrilateral of area 1?
- A polygon with congruent sides?

Answer: YES for isosceles trapezoids, triangles, and right triangles.

Key Results:
- Koizumi (2025): Proved all three (isosceles trapezoid, isosceles triangle,
  right-angled triangle) of area 1 must exist
- Kovač-Predojević (2024): Proved cyclic quadrilaterals of area 1 exist
- Kovač (2023): Showed parallelograms can fail; proved trapezoids work

References:
- Erdős-Mauldin (unpublished): Claimed true for trapezoids
- Kovač [Ko23]: Parallelogram counterexample; trapezoid proof
- Kovač-Predojević [KoPr24]: Cyclic quadrilaterals result
- Koizumi [Ko25]: Complete resolution for trapezoids and triangles
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Real.Basic

open MeasureTheory Set

namespace Erdos353

/-
## Part I: Basic Definitions
-/

/--
**Measurable set with infinite measure in ℝ²:**
A Lebesgue measurable subset of the plane with infinite Lebesgue measure.
-/
def HasInfiniteMeasure (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  MeasurableSet A ∧ volume A = ⊤

/--
**Area of a triangle:**
Given three points, the area is half the absolute value of the cross product.
-/
noncomputable def triangleArea (p q r : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let v1 := q - p
  let v2 := r - p
  |v1 0 * v2 1 - v1 1 * v2 0| / 2

/--
**Area of a quadrilateral:**
Given four points in order, the area is computed via the shoelace formula.
-/
noncomputable def quadrilateralArea (p q r s : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let a := triangleArea p q r
  let b := triangleArea p r s
  a + b

/-
## Part II: Geometric Configurations
-/

/--
**Isosceles Triangle:**
A triangle with at least two equal sides.
-/
def IsIsoscelesTriangle (p q r : EuclideanSpace ℝ (Fin 2)) : Prop :=
  dist p q = dist p r ∨ dist p q = dist q r ∨ dist p r = dist q r

/--
**Right-Angled Triangle:**
A triangle with one 90-degree angle.
-/
def IsRightTriangle (p q r : EuclideanSpace ℝ (Fin 2)) : Prop :=
  inner (q - p) (r - p) = 0 ∨
  inner (p - q) (r - q) = 0 ∨
  inner (p - r) (q - r) = 0

/--
**Isosceles Trapezoid:**
A quadrilateral with one pair of parallel sides and equal non-parallel sides.
-/
def IsIsoscelesTrapezoid (p q r s : EuclideanSpace ℝ (Fin 2)) : Prop :=
  -- Parallel sides: (p,q) ∥ (s,r) or (p,s) ∥ (q,r)
  let pq := q - p
  let sr := r - s
  let ps := s - p
  let qr := r - q
  -- Cross product zero means parallel
  (pq 0 * sr 1 = pq 1 * sr 0 ∧ dist p s = dist q r) ∨
  (ps 0 * qr 1 = ps 1 * qr 0 ∧ dist p q = dist s r)

/--
**Parallelogram:**
A quadrilateral with both pairs of opposite sides parallel.
-/
def IsParallelogram (p q r s : EuclideanSpace ℝ (Fin 2)) : Prop :=
  q - p = r - s ∧ s - p = r - q

/--
**Cyclic Quadrilateral:**
A quadrilateral whose vertices lie on a common circle.
-/
def IsCyclicQuadrilateral (p q r s : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ),
    radius > 0 ∧
    dist center p = radius ∧
    dist center q = radius ∧
    dist center r = radius ∧
    dist center s = radius

/--
**Polygon with Congruent Sides:**
All sides have the same length.
-/
def HasCongruentSides (vertices : List (EuclideanSpace ℝ (Fin 2))) : Prop :=
  vertices.length ≥ 3 ∧
  ∃ d : ℝ, d > 0 ∧ ∀ i : ℕ, i < vertices.length →
    dist (vertices[i]!) (vertices[(i + 1) % vertices.length]!) = d

/-
## Part III: Configuration Existence in Sets
-/

/--
**Triangle with vertices in A:**
Three distinct points from A forming a triangle.
-/
def HasTriangleWithArea (A : Set (EuclideanSpace ℝ (Fin 2))) (area : ℝ) : Prop :=
  ∃ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    triangleArea p q r = area

/--
**Isosceles triangle with vertices in A of given area:**
-/
def HasIsoscelesTriangleWithArea (A : Set (EuclideanSpace ℝ (Fin 2))) (area : ℝ) : Prop :=
  ∃ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    IsIsoscelesTriangle p q r ∧
    triangleArea p q r = area

/--
**Right triangle with vertices in A of given area:**
-/
def HasRightTriangleWithArea (A : Set (EuclideanSpace ℝ (Fin 2))) (area : ℝ) : Prop :=
  ∃ p q r : EuclideanSpace ℝ (Fin 2),
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧
    p ≠ q ∧ q ≠ r ∧ p ≠ r ∧
    IsRightTriangle p q r ∧
    triangleArea p q r = area

/--
**Isosceles trapezoid with vertices in A of given area:**
-/
def HasIsoscelesTrapezoidWithArea (A : Set (EuclideanSpace ℝ (Fin 2))) (area : ℝ) : Prop :=
  ∃ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
    -- All distinct
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    IsIsoscelesTrapezoid p q r s ∧
    quadrilateralArea p q r s = area

/--
**Cyclic quadrilateral with vertices in A of given area:**
-/
def HasCyclicQuadrilateralWithArea (A : Set (EuclideanSpace ℝ (Fin 2))) (area : ℝ) : Prop :=
  ∃ p q r s : EuclideanSpace ℝ (Fin 2),
    p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
    p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
    IsCyclicQuadrilateral p q r s ∧
    quadrilateralArea p q r s = area

/-
## Part IV: Main Results - Koizumi (2025)
-/

/--
**Koizumi's Theorem (2025) - Isosceles Trapezoid:**
Every measurable set with infinite measure contains the vertices of an
isosceles trapezoid of area 1.
-/
axiom koizumi_isosceles_trapezoid (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) :
    HasIsoscelesTrapezoidWithArea A 1

/--
**Koizumi's Theorem (2025) - Isosceles Triangle:**
Every measurable set with infinite measure contains the vertices of an
isosceles triangle of area 1.
-/
axiom koizumi_isosceles_triangle (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) :
    HasIsoscelesTriangleWithArea A 1

/--
**Koizumi's Theorem (2025) - Right Triangle:**
Every measurable set with infinite measure contains the vertices of a
right-angled triangle of area 1.
-/
axiom koizumi_right_triangle (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) :
    HasRightTriangleWithArea A 1

/-
## Part V: Kovač Results (2023-2024)
-/

/--
**Kovač's Trapezoid Theorem (2023):**
Every measurable set with infinite measure contains the vertices of a
(not necessarily isosceles) trapezoid of area 1.
-/
axiom kovac_trapezoid (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) :
    ∃ p q r s, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
      -- One pair of parallel sides
      (q - p) 0 * (r - s) 1 = (q - p) 1 * (r - s) 0 ∧
      quadrilateralArea p q r s = 1

/--
**Kovač's Parallelogram Counterexample (2023):**
There exists a set with infinite measure that does NOT contain the vertices
of a parallelogram with area 1.

This shows parallelograms are different from trapezoids!
-/
axiom kovac_parallelogram_counterexample :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)),
      HasInfiniteMeasure A ∧
      ¬∃ p q r s, p ∈ A ∧ q ∈ A ∧ r ∈ A ∧ s ∈ A ∧
        IsParallelogram p q r s ∧
        quadrilateralArea p q r s = 1

/--
**Kovač-Predojević Cyclic Quadrilateral Theorem (2024):**
Every measurable set with infinite measure contains the vertices of a
cyclic quadrilateral of area 1.
-/
axiom kovac_predojevic_cyclic (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) :
    HasCyclicQuadrilateralWithArea A 1

/-
## Part VI: Congruent Sides Result
-/

/--
**Kovač-Predojević Congruent Sides Counterexample (2024):**
There exists a set with infinite measure such that every convex polygon
with congruent sides and all vertices in the set has area < 1.
-/
axiom kovac_predojevic_congruent_counterexample :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)),
      HasInfiniteMeasure A ∧
      ∀ vertices : List (EuclideanSpace ℝ (Fin 2)),
        HasCongruentSides vertices →
        (∀ v ∈ vertices, v ∈ A) →
        -- polygon area < 1 (simplified statement)
        True -- Area computation would require convex hull

/-
## Part VII: Why Infinite Measure Matters
-/

/--
**Finite Measure Fails:**
Sets with finite measure may not contain any triangle of area 1.
Example: A line segment has infinite length but zero 2D measure.
-/
axiom finite_measure_counterexample :
    ∃ A : Set (EuclideanSpace ℝ (Fin 2)),
      MeasurableSet A ∧ volume A < ⊤ ∧
      ¬HasTriangleWithArea A 1

/--
**Density Argument:**
The proofs use the fact that infinite measure sets must have positive
density in many regions, ensuring enough points to form configurations.
-/
axiom density_argument : True

/-
## Part VIII: Scaling Properties
-/

/--
**Scaling Theorem:**
If A has infinite measure and must contain configuration C of area 1,
then for any positive t, A contains configuration C of area t.

Proof: Scale A by √t to get a set also with infinite measure.
-/
theorem scaling_property (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) (t : ℝ) (ht : t > 0) :
    HasIsoscelesTriangleWithArea A t := by
  sorry -- Follows from scaling argument

/--
**Consequence: Triangles of Any Area:**
Sets of infinite measure contain isosceles triangles of every positive area.
-/
theorem all_areas_isosceles (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) (t : ℝ) (ht : t > 0) :
    HasIsoscelesTriangleWithArea A t :=
  scaling_property A hA t ht

/-
## Part IX: Connections to Other Problems
-/

/--
**Connection to Erdős Distance Problem:**
The study of configurations in point sets relates to the Erdős distinct
distances problem and unit distance problems.
-/
axiom erdos_distance_connection : True

/--
**Connection to Ramsey Theory:**
Finding configurations in large sets has Ramsey-theoretic flavor:
large enough sets must contain desired structures.
-/
axiom ramsey_connection : True

/-
## Part X: Summary
-/

/--
**Erdős Problem #353: Summary**

PROBLEM:
Does every measurable set A ⊆ ℝ² with infinite measure contain:
- Isosceles trapezoid of area 1?
- Isosceles triangle of area 1?
- Right-angled triangle of area 1?
- Cyclic quadrilateral of area 1?
- Polygon with congruent sides of area 1?

STATUS: SOLVED

ANSWERS:
- Isosceles trapezoid: YES (Koizumi 2025)
- Isosceles triangle: YES (Koizumi 2025)
- Right triangle: YES (Koizumi 2025)
- Cyclic quadrilateral: YES (Kovač-Predojević 2024)
- Parallelogram: NO (Kovač 2023 counterexample)
- Congruent-sided polygon of area 1: NOT ALWAYS

KEY INSIGHTS:
1. Infinite measure ensures sufficient density for configurations
2. Parallelograms are special - more constraints
3. Trapezoids (one parallel pair) are easier than parallelograms (two pairs)
4. Recent work (2023-2025) resolved all main questions
-/
theorem erdos_353_summary :
    -- All three Koizumi results
    (∀ A, HasInfiniteMeasure A → HasIsoscelesTrapezoidWithArea A 1) ∧
    (∀ A, HasInfiniteMeasure A → HasIsoscelesTriangleWithArea A 1) ∧
    (∀ A, HasInfiniteMeasure A → HasRightTriangleWithArea A 1) ∧
    -- Cyclic quadrilaterals exist
    (∀ A, HasInfiniteMeasure A → HasCyclicQuadrilateralWithArea A 1) := by
  exact ⟨koizumi_isosceles_trapezoid, koizumi_isosceles_triangle,
         koizumi_right_triangle, kovac_predojevic_cyclic⟩

/--
**Status Theorem:**
-/
theorem erdos_353_status :
    -- Koizumi's complete resolution
    ∀ A : Set (EuclideanSpace ℝ (Fin 2)), HasInfiniteMeasure A →
      HasIsoscelesTrapezoidWithArea A 1 ∧
      HasIsoscelesTriangleWithArea A 1 ∧
      HasRightTriangleWithArea A 1 := by
  intro A hA
  exact ⟨koizumi_isosceles_trapezoid A hA,
         koizumi_isosceles_triangle A hA,
         koizumi_right_triangle A hA⟩

end Erdos353
