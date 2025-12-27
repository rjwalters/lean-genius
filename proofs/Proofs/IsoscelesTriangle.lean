import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic

/-!
# Isosceles Triangle Theorem (Pons Asinorum)

## What This Proves
In an isosceles triangle, the base angles are equal. This theorem, also known as
"Pons Asinorum" (Bridge of Asses), states:

**Forward Direction**: If AB = AC (two sides are equal), then angle ABC = angle ACB.

**Converse**: If angle ABC = angle ACB (base angles are equal), then AB = AC.

The Latin name "Pons Asinorum" comes from its role as the first serious test of
mathematical reasoning for students in Euclid's Elements (Proposition I.5).

## Wiedijk 100 Theorems: #65
This is entry #65 in Freek Wiedijk's list of 100 famous theorems.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `EuclideanGeometry.angle_eq_angle_of_dist_eq`
  and `EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi` from
  `Geometry.Euclidean.Triangle`.
- **Key Insight:** The forward direction follows from the symmetry of an isosceles
  triangle when reflected across the perpendicular bisector of the base.
- **Proof Techniques Demonstrated:** Euclidean geometry in inner product spaces,
  angle definitions via inner products, metric properties.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] Proves extensions/corollaries
- [x] Pedagogical examples

## Mathlib Dependencies
- `EuclideanGeometry.angle` : Angle at a point in Euclidean space
- `EuclideanGeometry.angle_eq_angle_of_dist_eq` : Forward direction (Pons Asinorum)
- `EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi` : Converse
- `InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq` : Vector form

## Historical Note
This theorem appears as Proposition 5 in Book I of Euclid's Elements (c. 300 BCE).
The name "Pons Asinorum" arose in medieval times because this proposition served
as a bridge that "asses" (poor students) could not cross - it was the first proof
requiring non-trivial reasoning beyond direct application of axioms. Euclid's
original proof involved an auxiliary construction; Pappus later gave a simpler
proof by considering the triangle congruent to itself.
-/

open EuclideanGeometry

namespace IsoscelesTriangle

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-! ## Forward Direction: Equal Sides Imply Equal Angles

The classic Isosceles Triangle Theorem. -/

/-- **Isosceles Triangle Theorem (Wiedijk #65) - Forward Direction**

In a triangle with vertices A, B, C, if the distance from A to B equals
the distance from A to C, then the angle at B equals the angle at C.

In symbols: If dist(A, B) = dist(A, C), then ∠ABC = ∠ACB.

This is Pons Asinorum: the base angles of an isosceles triangle are equal. -/
theorem base_angles_equal_of_sides_equal {A B C : P}
    (h : dist A B = dist A C) :
    ∠ A B C = ∠ A C B :=
  EuclideanGeometry.angle_eq_angle_of_dist_eq h

/-! ## Converse: Equal Angles Imply Equal Sides

The converse requires a non-degeneracy condition. -/

/-- **Isosceles Triangle Theorem (Wiedijk #65) - Converse**

If the base angles of a triangle are equal (and the apex angle is not π),
then the two adjacent sides are equal.

In symbols: If ∠ABC = ∠ACB and ∠BAC ≠ π, then dist(A, B) = dist(A, C).

The condition ∠BAC ≠ π excludes degenerate triangles where A, B, C are collinear. -/
theorem sides_equal_of_base_angles_equal {A B C : P}
    (h : ∠ A B C = ∠ A C B)
    (hnd : ∠ B A C ≠ Real.pi) :
    dist A B = dist A C :=
  EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi h hnd

/-! ## Biconditional Statement

Combining both directions into an iff statement. -/

/-- **Isosceles Triangle Theorem - Biconditional Form**

For a non-degenerate triangle (apex angle ≠ π), the base angles are equal
if and only if the two sides adjacent to the apex are equal.

This combines Pons Asinorum with its converse. -/
theorem isosceles_triangle_iff {A B C : P}
    (hnd : ∠ B A C ≠ Real.pi) :
    dist A B = dist A C ↔ ∠ A B C = ∠ A C B :=
  ⟨base_angles_equal_of_sides_equal, fun h => sides_equal_of_base_angles_equal h hnd⟩

/-! ## Vector Form

The theorem also has a natural formulation in terms of vectors. -/

/-- **Isosceles Triangle Theorem - Vector Form**

For vectors x and y with equal norms, the angles they make with (x - y)
and (y - x) respectively are equal.

This is Pons Asinorum stated in terms of position vectors from the apex. -/
theorem angle_eq_of_norm_eq {x y : V} (h : ‖x‖ = ‖y‖) :
    InnerProductGeometry.angle x (x - y) = InnerProductGeometry.angle y (y - x) :=
  InnerProductGeometry.angle_sub_eq_angle_sub_rev_of_norm_eq h

/-! ## Verification -/

#check base_angles_equal_of_sides_equal
#check sides_equal_of_base_angles_equal
#check isosceles_triangle_iff
#check angle_eq_of_norm_eq

end IsoscelesTriangle
