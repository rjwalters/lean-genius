import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Sum of Angles of a Triangle (Wiedijk #27)

## What This Proves
The sum of the interior angles of a triangle equals 180 degrees (or π radians).

For a triangle with vertices at points p₁, p₂, p₃:
$$\angle p_1 p_2 p_3 + \angle p_2 p_3 p_1 + \angle p_3 p_1 p_2 = \pi$$

This is one of the most fundamental results in Euclidean geometry, known since
ancient Greek mathematics and appearing in Euclid's Elements (Book I, Prop. 32).

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`
  which proves the theorem for any three points where two pairs are distinct from the first.
- **Key Insight:** The angle function `EuclideanGeometry.angle` measures the angle at
  the middle point, so `angle p₁ p₂ p₃` is the angle at vertex p₂.
- **Proof Techniques Demonstrated:** Using Mathlib's Euclidean geometry library,
  working with angles in affine spaces.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `EuclideanGeometry.angle` : Angle at a point between two other points
- `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` : The main triangle angle sum theorem
- `EuclideanGeometry.angle_nonneg` : Interior angles are non-negative
- `EuclideanGeometry.angle_le_pi` : Each angle is at most π

## Historical Note
This theorem is one of the oldest in mathematics. Euclid proved it around 300 BCE
by constructing a line through one vertex parallel to the opposite side. The theorem
characterizes Euclidean (flat) geometry: in spherical geometry the sum is greater
than π, while in hyperbolic geometry it is less than π. This relationship between
angle sums and curvature became foundational for non-Euclidean geometry in the 19th century.

This is #27 on Wiedijk's list of 100 theorems.
-/

namespace TriangleAngleSum

open scoped EuclideanGeometry

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-! ## The Main Theorem

The sum of the three interior angles of a triangle equals π radians. -/

/-- **Sum of Angles of a Triangle (Wiedijk #27)**

For any three points p₁, p₂, p₃ in a Euclidean space (with p₂ ≠ p₁ and p₃ ≠ p₁):
  angle(p₁, p₂, p₃) + angle(p₂, p₃, p₁) + angle(p₃, p₁, p₂) = π

This is the fundamental theorem about triangle angles: their sum is always 180°. -/
theorem triangle_angle_sum {p₁ p₂ p₃ : P} (h₂ : p₂ ≠ p₁) (h₃ : p₃ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi :=
  EuclideanGeometry.angle_add_angle_add_angle_eq_pi h₂ h₃

/-! ## Non-Degenerate Triangle Version

For a proper (non-degenerate) triangle where all three vertices are distinct,
we have the same result with a more natural hypothesis. -/

/-- Triangle angle sum for three distinct points -/
theorem triangle_angle_sum_of_distinct {p₁ p₂ p₃ : P}
    (h₁₂ : p₁ ≠ p₂) (_h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi :=
  triangle_angle_sum h₁₂.symm h₃₁

/-! ## Properties of Triangle Angles

Each interior angle of a triangle is bounded between 0 and π. -/

/-- Each angle in the triangle is at most π -/
theorem angle_le_pi (p₁ p₂ p₃ : P) : ∠ p₁ p₂ p₃ ≤ Real.pi :=
  EuclideanGeometry.angle_le_pi p₁ p₂ p₃

/-- Each angle in the triangle is non-negative -/
theorem angle_nonneg (p₁ p₂ p₃ : P) : 0 ≤ ∠ p₁ p₂ p₃ :=
  EuclideanGeometry.angle_nonneg p₁ p₂ p₃

/-! ## Corollaries

Useful consequences of the triangle angle sum. -/

/-- If two angles are known, the third is determined -/
theorem third_angle_eq {p₁ p₂ p₃ : P} (h₂ : p₂ ≠ p₁) (h₃ : p₃ ≠ p₁) :
    ∠ p₃ p₁ p₂ = Real.pi - ∠ p₁ p₂ p₃ - ∠ p₂ p₃ p₁ := by
  have := triangle_angle_sum h₂ h₃
  linarith

/-- Any single angle must be less than π (for a non-degenerate triangle) -/
theorem any_angle_lt_pi {p₁ p₂ p₃ : P}
    (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁)
    (hpos₁ : 0 < ∠ p₁ p₂ p₃) (hpos₂ : 0 < ∠ p₂ p₃ p₁) :
    ∠ p₃ p₁ p₂ < Real.pi := by
  have hsum := triangle_angle_sum_of_distinct h₁₂ h₂₃ h₃₁
  linarith

/-- In a non-degenerate triangle, the sum of any two angles is less than π -/
theorem two_angles_lt_pi {p₁ p₂ p₃ : P}
    (h₁₂ : p₁ ≠ p₂) (h₂₃ : p₂ ≠ p₃) (h₃₁ : p₃ ≠ p₁)
    (hpos : 0 < ∠ p₃ p₁ p₂) :
    ∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ < Real.pi := by
  have hsum := triangle_angle_sum_of_distinct h₁₂ h₂₃ h₃₁
  linarith

/-! ## Right Triangle Special Case

In a right triangle, the two acute angles sum to π/2. -/

/-- In a right triangle with right angle at p₂, the other two angles sum to π/2 -/
theorem right_triangle_acute_sum {p₁ p₂ p₃ : P} (h₂ : p₂ ≠ p₁) (h₃ : p₃ ≠ p₁)
    (hright : ∠ p₁ p₂ p₃ = Real.pi / 2) :
    ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ = Real.pi / 2 := by
  have hsum := triangle_angle_sum h₂ h₃
  linarith

/-! ## Exterior Angle Theorem

The exterior angle of a triangle equals the sum of the two non-adjacent interior angles.
An exterior angle at a vertex is π minus the interior angle at that vertex. -/

/-- The exterior angle at a vertex equals the sum of the two remote interior angles -/
theorem exterior_angle_theorem {p₁ p₂ p₃ : P} (h₂ : p₂ ≠ p₁) (h₃ : p₃ ≠ p₁) :
    (Real.pi - ∠ p₁ p₂ p₃) = ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂ := by
  have hsum := triangle_angle_sum h₂ h₃
  linarith

/-! ## In Degrees

For intuition, we can express the theorem in terms of degrees.
180° = π radians. -/

/-- The sum of angles in degrees is 180 -/
theorem triangle_angle_sum_degrees {p₁ p₂ p₃ : P} (h₂ : p₂ ≠ p₁) (h₃ : p₃ ≠ p₁) :
    (∠ p₁ p₂ p₃ + ∠ p₂ p₃ p₁ + ∠ p₃ p₁ p₂) * (180 / Real.pi) = 180 := by
  rw [triangle_angle_sum h₂ h₃]
  field_simp

/-! ## Verification -/

#check EuclideanGeometry.angle_add_angle_add_angle_eq_pi
#check triangle_angle_sum
#check right_triangle_acute_sum
#check exterior_angle_theorem

end TriangleAngleSum
