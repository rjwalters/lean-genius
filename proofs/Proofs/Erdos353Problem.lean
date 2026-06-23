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
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Set Pointwise

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
  inner (𝕜 := ℝ) (q - p) (r - p) = 0 ∨
  inner (𝕜 := ℝ) (p - q) (r - q) = 0 ∨
  inner (𝕜 := ℝ) (p - r) (q - r) = 0

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

/-
**Kovač's Trapezoid Theorem (2023):**
Every measurable set with infinite measure contains the vertices of a
(not necessarily isosceles) trapezoid of area 1.
-/
/-
**Kovač's Parallelogram Counterexample (2023):**
There exists a set with infinite measure that does NOT contain the vertices
of a parallelogram with area 1.

This shows parallelograms are different from trapezoids!
-/
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

/-
**Kovač-Predojević Congruent Sides Counterexample (2024):**
There exists a set with infinite measure such that every convex polygon
with congruent sides and all vertices in the set has area < 1.
-/
/-
## Part VII: Why Infinite Measure Matters
-/

/-
**Finite Measure Fails:**
Sets with finite measure may not contain any triangle of area 1.
Example: A line segment has infinite length but zero 2D measure.
-/
/-
**Density Argument:**
The proofs use the fact that infinite measure sets must have positive
density in many regions, ensuring enough points to form configurations.
-/

/-
## Part VIII: Scaling Properties — Infrastructure
-/

/-- Preimage characterization: c⁻¹ • A equals the preimage of A under scaling by c. -/
private lemma inv_smul_set_eq_preimage (c : ℝ) (hc : c ≠ 0)
    (A : Set (EuclideanSpace ℝ (Fin 2))) :
    c⁻¹ • A = (fun x => c • x) ⁻¹' A := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, rfl⟩; rwa [smul_inv_smul₀ hc]
  · intro h; exact ⟨c • x, h, inv_smul_smul₀ hc x⟩

/-- Scaling a set of infinite measure by a nonzero constant preserves infinite measure.
    This follows from the Haar measure scaling formula: μ(c • A) = |c|^n · μ(A). -/
private lemma hasInfiniteMeasure_inv_smul (c : ℝ) (hc : c ≠ 0)
    (A : Set (EuclideanSpace ℝ (Fin 2))) (hA : HasInfiniteMeasure A) :
    HasInfiniteMeasure (c⁻¹ • A) := by
  rw [inv_smul_set_eq_preimage c hc A]
  constructor
  · exact hA.1.preimage (measurable_const_smul c)
  · -- volume ((c • ·)⁻¹' A) = ⊤ because Lebesgue measure of preimage
    -- under scaling by c ≠ 0 is |c|⁻ⁿ · volume(A) = |c|⁻ⁿ · ⊤ = ⊤
    -- Rewrite preimage as smul set, apply Haar measure scaling, then simplify
    rw [show (fun x : EuclideanSpace ℝ (Fin 2) => c • x) ⁻¹' A = c⁻¹ • A
      from (inv_smul_set_eq_preimage c hc A).symm]
    rw [MeasureTheory.Measure.addHaar_smul volume c⁻¹ A, hA.2]
    -- Goal: ENNReal.ofReal |c⁻¹| ^ finrank ℝ (EuclideanSpace ℝ (Fin 2)) * ⊤ = ⊤
    have h_pos : (0 : ℝ≥0∞) < ENNReal.ofReal |c⁻¹| ^ FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin 2)) :=
      pow_pos (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero.mpr hc))) _
    simp [ENNReal.mul_top, h_pos.ne']

/-- Scaling preserves the isosceles triangle property. -/
private lemma isIsoscelesTriangle_smul (c : ℝ) (hc : c ≠ 0)
    {p q r : EuclideanSpace ℝ (Fin 2)} (h : IsIsoscelesTriangle p q r) :
    IsIsoscelesTriangle (c • p) (c • q) (c • r) := by
  have ds : ∀ x y : EuclideanSpace ℝ (Fin 2),
      dist (c • x) (c • y) = ‖c‖ * dist x y := by
    intro x y; rw [dist_eq_norm, ← smul_sub, norm_smul, dist_eq_norm]
  unfold IsIsoscelesTriangle at *
  rw [ds p q, ds p r, ds q r]
  rcases h with h | h | h
  · left; rw [h]
  · right; left; rw [h]
  · right; right; rw [h]

/-- Triangle area scales by c² under uniform scaling of vertices by c > 0. -/
private lemma triangleArea_smul_eq (c : ℝ) (hc : c > 0)
    (p q r : EuclideanSpace ℝ (Fin 2)) :
    triangleArea (c • p) (c • q) (c • r) = c ^ 2 * triangleArea p q r := by
  unfold triangleArea
  dsimp only
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [show (c * q 0 - c * p 0) * (c * r 1 - c * p 1) - (c * q 1 - c * p 1) * (c * r 0 - c * p 0) =
      c ^ 2 * ((q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)) from by ring]
  rw [abs_mul, abs_of_pos (pow_pos hc 2)]
  ring

/-
## Part VIII: Scaling Properties — Main Result
-/

/--
**Scaling Theorem:**
If A has infinite measure and must contain an isosceles triangle of area 1,
then for any positive t, A contains an isosceles triangle of area t.

Proof: Scale A by 1/√t to get a set B with infinite measure. By Koizumi's
theorem, B contains an isosceles triangle of area 1. Scaling back by √t gives
an isosceles triangle of area (√t)² = t with vertices in A.
-/
theorem scaling_property (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : HasInfiniteMeasure A) (t : ℝ) (ht : t > 0) :
    HasIsoscelesTriangleWithArea A t := by
  -- Let c = √t > 0
  set c := Real.sqrt t with hc_def
  have hc_pos : 0 < c := Real.sqrt_pos_of_pos ht
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  -- B = c⁻¹ • A has infinite measure
  have hB : HasInfiniteMeasure (c⁻¹ • A) := hasInfiniteMeasure_inv_smul c hc_ne A hA
  -- By Koizumi, B contains an isosceles triangle of area 1
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hpr, hiso, harea⟩ :=
    koizumi_isosceles_triangle (c⁻¹ • A) hB
  -- Membership: p ∈ c⁻¹ • A implies c • p ∈ A
  rw [inv_smul_set_eq_preimage c hc_ne A] at hp hq hr
  -- Construct the isosceles triangle in A
  refine ⟨c • p, c • q, c • r, hp, hq, hr, ?_, ?_, ?_, ?_, ?_⟩
  -- Distinctness: scaling by c ≠ 0 is injective
  · exact fun h => hpq (smul_left_cancel₀ hc_ne h)
  · exact fun h => hqr (smul_left_cancel₀ hc_ne h)
  · exact fun h => hpr (smul_left_cancel₀ hc_ne h)
  -- Isosceles: scaling preserves distance ratios
  · exact isIsoscelesTriangle_smul c hc_ne hiso
  -- Area: c² · area(p,q,r) = (√t)² · 1 = t
  · rw [triangleArea_smul_eq c hc_pos p q r, harea, mul_one, hc_def,
        Real.sq_sqrt (le_of_lt ht)]

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

/-
**Connection to Erdős Distance Problem:**
The study of configurations in point sets relates to the Erdős distinct
distances problem and unit distance problems.
-/

/-
**Connection to Ramsey Theory:**
Finding configurations in large sets has Ramsey-theoretic flavor:
large enough sets must contain desired structures.
-/

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
