import Mathlib.Geometry.Euclidean.Sphere.Ptolemy
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Ptolemy's Theorem

## What This Proves
Ptolemy's Theorem states that for a cyclic quadrilateral (four points on a circle),
the product of the diagonals equals the sum of the products of opposite sides:

  AC · BD = AB · CD + BC · DA

This is Wiedijk's 100 Theorems #95.

## Historical Context
Ptolemy of Alexandria (c. 100-170 AD) proved this theorem in his astronomical treatise
"Almagest" where it was used to compute chord lengths for trigonometric tables.
The theorem is fundamental to classical geometry and has deep connections to
the Law of Cosines and complex number multiplication.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`
  which proves Ptolemy's theorem for cospherical points in any Euclidean space.
- **Cospherical Points:** Four points lie on a common sphere (circle in 2D).
- **Angle Condition:** The diagonals intersect at a point p where ∠apc = π and ∠bpd = π,
  meaning p lies on both diagonals with the vertices on opposite sides.

## Status
- [x] Complete proof
- [x] Uses Mathlib's Ptolemy theorem
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical` : Main theorem
- `Cospherical` : Predicate for points on a common sphere
- `∠` : Angle measurement between three points

Historical Note: Ptolemy's theorem appears in Book I, Chapter 10 of the Almagest.
It was used to derive the chord of the sum of two arcs from the chords of the
individual arcs, essentially providing a formula for sin(α + β).
-/

set_option linter.unusedVariables false

open scoped EuclideanGeometry RealInnerProductSpace Real
open EuclideanGeometry

-- ============================================================
-- PART 1: Setup and Definitions
-- ============================================================

-- We work in a general Euclidean space with inner product
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

-- For the Euclidean plane specifically
abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

-- ============================================================
-- PART 2: Ptolemy's Theorem from Mathlib
-- ============================================================

/-- **Ptolemy's Theorem** (Wiedijk #95)

For four points A, B, C, D on a circle (cospherical), if the diagonals AC and BD
intersect at point P (expressed via the angle conditions ∠apc = π and ∠bpd = π), then:

  dist(A,B) · dist(C,D) + dist(B,C) · dist(D,A) = dist(A,C) · dist(B,D)

This is the classic form of Ptolemy's theorem: the sum of the products of
opposite sides equals the product of the diagonals.

The Mathlib formulation uses:
- `Cospherical` to express that points lie on a common sphere
- Angle conditions `∠ a p c = π` and `∠ b p d = π` meaning p is the diagonal intersection -/
theorem ptolemys_theorem {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π)
    (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d :=
  mul_dist_add_mul_dist_eq_mul_dist_of_cospherical h hapc hbpd

-- ============================================================
-- PART 3: Alternative Formulations
-- ============================================================

/-- Ptolemy's theorem can be stated with distances in different order.
    This version emphasizes the diagonal products on the right side. -/
theorem ptolemys_theorem_diagonals {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π)
    (hbpd : ∠ b p d = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d :=
  ptolemys_theorem h hapc hbpd

/-- The symmetric form: the diagonal product equals the sum of opposite side products -/
theorem ptolemys_theorem_symmetric {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π)
    (hbpd : ∠ b p d = π) :
    dist a c * dist b d = dist a b * dist c d + dist b c * dist d a := by
  rw [ptolemys_theorem h hapc hbpd]

/-- Commutativity of multiplication allows rearrangement -/
theorem ptolemys_theorem_rearranged {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π)
    (hbpd : ∠ b p d = π) :
    dist b d * dist a c = dist a b * dist c d + dist b c * dist d a := by
  rw [mul_comm, ptolemys_theorem h hapc hbpd]

-- ============================================================
-- PART 4: Corollaries and Special Cases
-- ============================================================

/-- For a cyclic quadrilateral, the diagonal product can be computed
    from the side lengths. -/
theorem diagonal_product_from_sides {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P))
    (hapc : ∠ a p c = π)
    (hbpd : ∠ b p d = π) :
    dist a c * dist b d = dist a b * dist c d + dist b c * dist d a :=
  ptolemys_theorem_symmetric h hapc hbpd

-- ============================================================
-- PART 5: Connection to Other Theorems
-- ============================================================

/-!
### Relationship to Law of Cosines

Ptolemy's theorem can be derived from the Law of Cosines applied to the
triangles formed by the diagonals. Conversely, the Law of Cosines can be
derived as a limiting case of Ptolemy's theorem.

### Relationship to Product of Segments

For a cyclic quadrilateral with diagonals intersecting at P:
- PA · PC (Product of segments of diagonal AC)
- PB · PD (Product of segments of diagonal BD)
These are related by the power of point P with respect to the circumcircle.

### Complex Number Proof

Ptolemy's theorem has an elegant proof using complex numbers:
If A, B, C, D lie on a circle and are represented as complex numbers,
then (A-C)(B-D) = (A-B)(C-D) + (A-D)(B-C) holds when the points are
appropriately ordered on the circle.

### Applications

1. **Trigonometry**: Derivation of sum and difference formulas
2. **Astronomy**: Computing chord tables (historical use)
3. **Optics**: Analysis of reflections in curved mirrors
4. **Architecture**: Design of cyclic shapes and arches
-/

-- ============================================================
-- PART 6: Numerical Examples
-- ============================================================

/-- Example: Rectangle inscribed in a circle (degenerate case)

For a rectangle with sides a and b, diagonals have length √(a² + b²).
Ptolemy: d² = ab + ab = 2ab, but d = √(a² + b²), so d² = a² + b².
This is the Pythagorean theorem! Ptolemy generalizes it.

For a rectangle with sides 3 and 4:
- Sides: AB = CD = 4, BC = DA = 3
- Diagonals: AC = BD = 5 (by Pythagorean theorem)
- Ptolemy: 4·4 + 3·3 = 16 + 9 = 25 = 5·5 ✓ -/
example : (4 : ℝ) * 4 + 3 * 3 = 5 * 5 := by norm_num

/-- Example: Regular inscribed quadrilateral (square)

For a square with side s inscribed in a circle:
- All sides equal: AB = BC = CD = DA = s
- Diagonals: AC = BD = s√2

Ptolemy: s·s + s·s = (s√2)·(s√2)
         2s² = 2s² ✓ -/
example (s : ℝ) (hs : 0 < s) :
    s * s + s * s = (s * Real.sqrt 2) * (s * Real.sqrt 2) := by
  rw [mul_mul_mul_comm]
  rw [Real.mul_self_sqrt (by linarith : (2 : ℝ) ≥ 0)]
  ring

/-- Example: Specific cyclic quadrilateral

Consider a cyclic quadrilateral with:
- AB = 5, CD = 5
- BC = 6, DA = 6
- (This is an isosceles trapezoid inscribed in a circle)

If AC = BD = 7 (the diagonals are equal for isosceles trapezoid),
Ptolemy gives: 5·5 + 6·6 = 25 + 36 = 61
But 7·7 = 49, so this doesn't satisfy Ptolemy exactly -
the actual diagonals would be √61 ≈ 7.81 -/
example : (5 : ℝ) * 5 + 6 * 6 = 61 := by norm_num

/-- The diagonal length for an isosceles trapezoid: √(ab + cd) -/
example : Real.sqrt ((5 : ℝ) * 5 + 6 * 6) = Real.sqrt 61 := by norm_num

-- ============================================================
-- PART 7: The Converse (Characterization of Cyclic Quadrilaterals)
-- ============================================================

/-!
### Converse of Ptolemy's Theorem

The converse is also true: if four points satisfy Ptolemy's equality:
  AC · BD = AB · CD + AD · BC
then the four points lie on a common circle (are concyclic).

This provides a characterization: Ptolemy's equality holds
if and only if the quadrilateral is cyclic.

### Ptolemy's Inequality

For arbitrary four points (not necessarily on a circle):
  AC · BD ≤ AB · CD + AD · BC

with equality if and only if the points are concyclic AND form a convex
quadrilateral in the correct order. This is sometimes called
"Ptolemy's inequality" and characterizes cyclic quadrilaterals.
-/

-- ============================================================
-- PART 8: Historical Context
-- ============================================================

/-!
### The Almagest

Ptolemy's theorem was proved in the Almagest (c. 150 AD) as part of
developing a table of chords, which served the same purpose as modern
trigonometric tables.

The theorem was used to derive:
- chord(α + β) from chord(α) and chord(β)
- chord(α - β) from chord(α) and chord(β)

These are equivalent to the modern formulas:
- sin(α + β) = sin(α)cos(β) + cos(α)sin(β)
- cos(α + β) = cos(α)cos(β) - sin(α)sin(β)

### Legacy

Ptolemy's theorem remained a fundamental tool in astronomy and navigation
until the development of modern trigonometry. It's now considered one of
the 100 most important theorems in mathematics (Wiedijk's list #95).
-/

-- ============================================================
-- Export main results
-- ============================================================

#check @ptolemys_theorem
#check @ptolemys_theorem_diagonals
#check @ptolemys_theorem_symmetric
#check @ptolemys_theorem_rearranged
#check @diagonal_product_from_sides
