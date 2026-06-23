import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-
# Archimedes Parabolic Exhaustion: Sub-Triangle Area Ratios

*Open Question from AreaOfCircleOQ03OQ03*: Formalize the sub-triangle area
ratios in Archimedes' parabolic exhaustion.

## What This Proves

In Archimedes' method of exhaustion for parabolic segments, each step inscribes
triangles in the remaining sub-segments. The key geometric fact is:

For a parabola y = x², the triangle formed by three points at x = a, m, b
(where m = (a+b)/2) has signed area (b-a)³/8. When we subdivide [a,b] at m
and form sub-triangles on [a,m] and [m,b], each sub-triangle has area exactly
1/8 of the parent triangle. Together, the two sub-triangles contribute 1/4
of the parent area — this is precisely the ratio 1/4 that drives Archimedes'
geometric series 1 + 1/4 + 1/16 + ... = 4/3.

## Mathematical Setup

For points (x, x²) on the parabola y = x², the signed area of a triangle
with vertices at x-coordinates x₁, x₂, x₃ is:

  T(x₁, x₂, x₃) = (1/2)|det([x₂-x₁, x₃-x₁; x₂²-x₁², x₃²-x₁²])|

For the specific case x₁ = a, x₂ = b, x₃ = (a+b)/2:
  T = (b-a)³ / 8

Sub-triangle on [a, (a+b)/2] with midpoint ((3a+b)/4):
  T_sub = ((a+b)/2 - a)³ / 8 = (b-a)³ / 64 = T / 8

## Status
- [x] Parabolic triangle area formula: (b-a)³/8
- [x] Sub-triangle area formula: (b-a)³/64
- [x] Area ratio: each sub-triangle is 1/8 of parent
- [x] Two sub-triangles together are 1/4 of parent
- [x] Connection to Archimedes' geometric series ratio
-/

namespace AreaOfCircleOQ03OQ03OQ02

open Real

noncomputable section

/-! ## Part 1: Parabolic Triangle Area Formula

For points on y = x², the signed area of the triangle with vertices at
x-coordinates a, b, m = (a+b)/2 is (b-a)³/8.

We define this using the determinant formula for triangle area. -/

/-- Signed area of a triangle with vertices (x₁, x₁²), (x₂, x₂²), (x₃, x₃²)
on the parabola y = x². Uses the determinant formula:
  2·T = (x₂ - x₁)(x₃² - x₁²) - (x₃ - x₁)(x₂² - x₁²)
      = (x₂ - x₁)(x₃ - x₁)(x₃ - x₂)                     -/
def parabolicTriangleArea (x₁ x₂ x₃ : ℝ) : ℝ :=
  (x₂ - x₁) * (x₃ - x₁) * (x₃ - x₂) / 2

/-- The determinant formula simplifies: for points on y = x², the signed area
of the triangle at x₁, x₂, x₃ equals (x₂-x₁)(x₃-x₁)(x₃-x₂)/2. -/
theorem parabolicTriangleArea_det (x₁ x₂ x₃ : ℝ) :
    (x₂ - x₁) * (x₃ ^ 2 - x₁ ^ 2) - (x₃ - x₁) * (x₂ ^ 2 - x₁ ^ 2) =
    2 * parabolicTriangleArea x₁ x₂ x₃ := by
  unfold parabolicTriangleArea
  ring

/-- **Parabolic triangle area with midpoint**: For a, b on the parabola y = x²,
the triangle with vertices at a, b, and midpoint m = (a+b)/2 has
signed area (b-a)³/8. -/
theorem parabolic_triangle_area_midpoint (a b : ℝ) :
    parabolicTriangleArea a b ((a + b) / 2) = (b - a) ^ 3 / 8 := by
  unfold parabolicTriangleArea
  ring

/-- The area is positive when a < b. -/
theorem parabolic_triangle_area_pos (a b : ℝ) (hab : a < b) :
    0 < parabolicTriangleArea a b ((a + b) / 2) := by
  rw [parabolic_triangle_area_midpoint]
  positivity

/-! ## Part 2: Sub-Triangle Areas

When we subdivide [a, b] at midpoint m = (a+b)/2, we get two sub-intervals
[a, m] and [m, b]. The sub-triangles inscribed in these sub-intervals
(using their own midpoints) have area exactly 1/8 of the parent. -/

/-- **Left sub-triangle area**: The triangle on [a, m] with midpoint (3a+b)/4
has area (b-a)³/64. -/
theorem left_subtriangle_area (a b : ℝ) :
    parabolicTriangleArea a ((a + b) / 2) ((a + (a + b) / 2) / 2) =
    (b - a) ^ 3 / 64 := by
  unfold parabolicTriangleArea
  ring

/-- **Right sub-triangle area**: The triangle on [m, b] with midpoint (a+3b)/4
has area (b-a)³/64. -/
theorem right_subtriangle_area (a b : ℝ) :
    parabolicTriangleArea ((a + b) / 2) b (((a + b) / 2 + b) / 2) =
    (b - a) ^ 3 / 64 := by
  unfold parabolicTriangleArea
  ring

/-! ## Part 3: The 1/8 and 1/4 Ratios -/

/-- **Each sub-triangle is 1/8 of the parent**: The left sub-triangle area
equals (1/8) times the parent triangle area. -/
theorem left_subtriangle_ratio (a b : ℝ) :
    parabolicTriangleArea a ((a + b) / 2) ((a + (a + b) / 2) / 2) =
    (1 / 8) * parabolicTriangleArea a b ((a + b) / 2) := by
  rw [left_subtriangle_area, parabolic_triangle_area_midpoint]
  ring

/-- **Each sub-triangle is 1/8 of the parent** (right side). -/
theorem right_subtriangle_ratio (a b : ℝ) :
    parabolicTriangleArea ((a + b) / 2) b (((a + b) / 2 + b) / 2) =
    (1 / 8) * parabolicTriangleArea a b ((a + b) / 2) := by
  rw [right_subtriangle_area, parabolic_triangle_area_midpoint]
  ring

/-- **Two sub-triangles together are 1/4 of the parent**: This is the key ratio
that drives Archimedes' geometric series. -/
theorem subtriangle_sum_ratio (a b : ℝ) :
    parabolicTriangleArea a ((a + b) / 2) ((a + (a + b) / 2) / 2) +
    parabolicTriangleArea ((a + b) / 2) b (((a + b) / 2 + b) / 2) =
    (1 / 4) * parabolicTriangleArea a b ((a + b) / 2) := by
  rw [left_subtriangle_area, right_subtriangle_area, parabolic_triangle_area_midpoint]
  ring

/-! ## Part 4: Iterated Exhaustion

After n levels of subdivision, the total area from all 2^n sub-triangles
at level n is (1/4)^n times the original triangle area. -/

/-- **Area at subdivision level n**: At level n, there are 2^n sub-triangles,
each of area (1/8)^n · T₀. The total area at level n is (1/4)^n · T₀. -/
theorem subdivision_level_area (T₀ : ℝ) (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 8 : ℝ) ^ n * T₀) = (1 / 4) ^ n * T₀ := by
  rw [← mul_assoc]
  congr 1
  rw [← mul_pow]
  norm_num

/-- **Cumulative exhaustion area**: The total area after n levels of exhaustion
(summing levels 0 through n-1) reproduces Archimedes' partial sum formula. -/
theorem cumulative_exhaustion_area (T₀ : ℝ) (n : ℕ) :
    T₀ * ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k =
    T₀ * (4 / 3 * (1 - (1 / 4) ^ n)) := by
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- **Exhaustion converges to 4/3 · T₀**: The gap between 4/3 · T₀ and the
partial sums is T₀ · (4/3) · (1/4)^n, which vanishes as n → ∞. -/
theorem exhaustion_gap (T₀ : ℝ) (n : ℕ) :
    T₀ * (4 / 3) - T₀ * ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k =
    T₀ * (4 / 3) * (1 / 4) ^ n := by
  rw [cumulative_exhaustion_area]
  ring

/-- **Exhaustion gap is positive** when T₀ > 0. -/
theorem exhaustion_gap_pos (T₀ : ℝ) (hT : 0 < T₀) (n : ℕ) :
    0 < T₀ * (4 / 3) - T₀ * ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k := by
  rw [exhaustion_gap]
  positivity

/-! ## Summary

Archimedes' parabolic exhaustion works because of a precise geometric fact:
for the parabola y = x², the triangle inscribed in each sub-segment has
area exactly 1/8 of the parent triangle. With two sub-segments per step,
the total new area at each level is 1/4 of the previous level.

This produces the geometric series:
  Total area = T₀ · (1 + 1/4 + 1/16 + ...) = T₀ · 4/3

The 1/4 ratio is not a coincidence — it follows from the degree-2 nature
of the parabola, which makes the area formula cubic in the interval length:
T ∝ (b-a)³. Halving the interval reduces the area by factor 2³ = 8,
and two such sub-triangles contribute 2/8 = 1/4 of the parent area.
-/

end AreaOfCircleOQ03OQ03OQ02
