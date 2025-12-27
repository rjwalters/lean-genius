import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Archive.Wiedijk100Theorems.HeronsFormula

/-!
# Heron's Formula

## What This Proves
Heron's Formula computes the area of a triangle given only its three side lengths.
For a triangle with sides a, b, c and semi-perimeter s = (a + b + c) / 2:

  Area = √(s(s-a)(s-b)(s-c))

Named after Hero of Alexandria (c. 10-70 AD), though the formula was known earlier.

## Approach
- **Foundation (from Mathlib):** We use `Theorems100.heron` from the Mathlib Archive,
  which proves that the trigonometric area formula (½ab·sin(C)) equals the Heron
  formula for the same triangle.
- **Original Contributions:** We provide the statement in multiple forms: for
  abstract inner product spaces (following Mathlib), for explicit side lengths,
  and with computational examples.
- **Proof Techniques Demonstrated:** Working with Euclidean geometry, the `dist`
  function, and angle measures from `EuclideanGeometry`.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Theorems100.heron` : The main Heron's formula theorem from Archive
- `EuclideanGeometry.angle` : Angle between three points
- `dist` : Euclidean distance function
- `Real.sqrt`, `Real.sin` : Square root and sine functions

Historical Note: Hero of Alexandria described this formula in his work "Metrica"
(c. 60 AD). The formula allows computing triangle area without needing heights
or angles, making it practical for surveying and navigation.

This is #57 on Wiedijk's list of 100 theorems.
-/

set_option linter.unusedVariables false

namespace HeronsFormula

open EuclideanGeometry Real

-- ============================================================
-- PART 1: The Main Theorem from Mathlib
-- ============================================================

/-!
### Heron's Formula (Mathlib Archive)

The Mathlib Archive contains the proof of Heron's formula. It establishes that
for a triangle with vertices p₁, p₂, p₃:

  (1/2) · a · b · sin(∠p₁p₂p₃) = √(s(s-a)(s-b)(s-c))

where:
- a = dist p₁ p₂ (side length)
- b = dist p₃ p₂ (side length)
- c = dist p₁ p₃ (side length)
- s = (a + b + c) / 2 (semi-perimeter)

The left side is the standard trigonometric area formula, and the right side
is Heron's formula.
-/

-- Reference to the main Heron theorem from Mathlib Archive
-- Theorems100.heron proves the equivalence of the sine formula and Heron's formula

-- ============================================================
-- PART 2: Restatement for Accessibility
-- ============================================================

/-- **Heron's Formula (Wiedijk #57)**

For a triangle with vertices p₁, p₂, p₃ (with p₁ ≠ p₂ and p₃ ≠ p₂),
the area computed via the sine formula equals Heron's formula:

  (1/2) · a · b · sin(∠p₁p₂p₃) = √(s(s-a)(s-b)(s-c))

where a, b, c are the side lengths and s is the semi-perimeter. -/
theorem heron_formula {V : Type*} {P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p₁ p₂ p₃ : P} (h₁ : p₁ ≠ p₂) (h₂ : p₃ ≠ p₂) :
    let a := dist p₁ p₂
    let b := dist p₃ p₂
    let c := dist p₁ p₃
    let s := (a + b + c) / 2
    1 / 2 * a * b * sin (angle p₁ p₂ p₃) = sqrt (s * (s - a) * (s - b) * (s - c)) :=
  Theorems100.heron h₁ h₂

-- ============================================================
-- PART 3: Understanding the Formula
-- ============================================================

/-!
### Understanding the Semi-perimeter

The semi-perimeter s = (a + b + c) / 2 is half the triangle's perimeter.
The quantities (s - a), (s - b), (s - c) are always non-negative for
valid triangles due to the triangle inequality.

For a triangle with sides a, b, c:
- s - a = (b + c - a) / 2 ≥ 0  (since b + c ≥ a by triangle inequality)
- s - b = (a + c - b) / 2 ≥ 0  (since a + c ≥ b by triangle inequality)
- s - c = (a + b - c) / 2 ≥ 0  (since a + b ≥ c by triangle inequality)
-/

/-- The semi-perimeter of a triangle with sides a, b, c -/
noncomputable def semiperimeter (a b c : ℝ) : ℝ := (a + b + c) / 2

/-- Heron's product s(s-a)(s-b)(s-c) -/
noncomputable def heron_product (a b c : ℝ) : ℝ :=
  let s := semiperimeter a b c
  s * (s - a) * (s - b) * (s - c)

-- ============================================================
-- PART 4: Algebraic Identity
-- ============================================================

/-- **Heron's Product Expansion**

The product s(s-a)(s-b)(s-c) can be expanded to an expression
involving only the side lengths. This is useful for computation. -/
theorem heron_product_expand (a b c : ℝ) :
    heron_product a b c =
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c) / 16 := by
  unfold heron_product semiperimeter
  ring

/-- Alternative expansion using the difference of squares -/
theorem heron_product_expand_alt (a b c : ℝ) :
    heron_product a b c =
    ((a + b + c) * (a + b - c) * (a - b + c) * (-a + b + c)) / 16 := by
  unfold heron_product semiperimeter
  ring

-- ============================================================
-- PART 5: Specific Examples
-- ============================================================

/-!
### Worked Examples

We verify Heron's formula for some classic triangles.
-/

/-- **3-4-5 Right Triangle**

For the 3-4-5 right triangle:
- Semi-perimeter: s = (3 + 4 + 5) / 2 = 6
- Heron's product: 6 · 3 · 2 · 1 = 36
- Area: √36 = 6

This matches the direct calculation: (1/2) · 3 · 4 = 6 -/
theorem heron_345_triangle :
    heron_product 3 4 5 = 36 := by
  unfold heron_product semiperimeter
  norm_num

theorem area_345_triangle :
    sqrt (heron_product 3 4 5) = 6 := by
  rw [heron_345_triangle]
  have h : (6 : ℝ)^2 = 36 := by norm_num
  rw [← h, sqrt_sq (by norm_num : (6 : ℝ) ≥ 0)]

/-- **Equilateral Triangle with Side 2**

For an equilateral triangle with side 2:
- Semi-perimeter: s = (2 + 2 + 2) / 2 = 3
- Heron's product: 3 · 1 · 1 · 1 = 3
- Area: √3

This matches the formula for equilateral triangles: (√3/4) · side² = √3 -/
theorem heron_equilateral_2 :
    heron_product 2 2 2 = 3 := by
  unfold heron_product semiperimeter
  norm_num

theorem area_equilateral_2 :
    sqrt (heron_product 2 2 2) = sqrt 3 := by
  rw [heron_equilateral_2]

/-- **5-12-13 Right Triangle**

For the 5-12-13 right triangle:
- Semi-perimeter: s = 15
- Heron's product: 15 · 10 · 3 · 2 = 900
- Area: √900 = 30

Direct calculation: (1/2) · 5 · 12 = 30 ✓ -/
theorem heron_5_12_13_triangle :
    heron_product 5 12 13 = 900 := by
  unfold heron_product semiperimeter
  norm_num

theorem area_5_12_13_triangle :
    sqrt (heron_product 5 12 13) = 30 := by
  rw [heron_5_12_13_triangle]
  have h : (30 : ℝ)^2 = 900 := by norm_num
  rw [← h, sqrt_sq (by norm_num : (30 : ℝ) ≥ 0)]

-- ============================================================
-- PART 6: Triangle Inequality Connection
-- ============================================================

/-!
### Valid Triangles

Heron's formula only makes sense for valid triangles, i.e., when the
side lengths satisfy the triangle inequality. When they do, the
product s(s-a)(s-b)(s-c) is non-negative.
-/

/-- For side lengths satisfying the triangle inequality, Heron's product is non-negative -/
theorem heron_product_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ heron_product a b c := by
  unfold heron_product semiperimeter
  have hs : 0 < (a + b + c) / 2 := by linarith
  have hsa : 0 < (a + b + c) / 2 - a := by linarith
  have hsb : 0 < (a + b + c) / 2 - b := by linarith
  have hsc : 0 < (a + b + c) / 2 - c := by linarith
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  all_goals linarith

-- ============================================================
-- PART 7: Applications
-- ============================================================

/-!
### Applications of Heron's Formula

1. **Surveying**: Calculate land area from measured side lengths
2. **Computer Graphics**: Compute triangle areas from vertex coordinates
3. **Navigation**: Determine distances and areas from GPS coordinates
4. **Engineering**: Structural analysis of triangular components

Heron's formula is particularly useful when the height is unknown or
difficult to measure directly.
-/

/-- Area of a triangle given three side lengths -/
noncomputable def triangle_area (a b c : ℝ) : ℝ :=
  sqrt (heron_product a b c)

/-- Triangle area is non-negative for valid triangles -/
theorem triangle_area_nonneg {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    0 ≤ triangle_area a b c := by
  unfold triangle_area
  exact sqrt_nonneg _

-- Export main results
#check @heron_formula
#check @heron_product
#check @heron_product_expand
#check @heron_345_triangle
#check @triangle_area

end HeronsFormula
