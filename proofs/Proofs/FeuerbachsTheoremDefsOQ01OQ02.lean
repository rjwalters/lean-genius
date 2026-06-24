/-
  Feuerbach's Theorem DefsOQ01OQ02: The Altitude-Length Law

  ## The Open Question

  The sibling file `FeuerbachsTheoremDefsOQ01` pins down each altitude foot by its
  *defining* properties — collinearity with the opposite side and perpendicularity
  of the altitude — and records the Pythagorean split at the foot.  What it never
  computes is the **length of the altitude itself**, the quantity `h_a = |A Hₐ|`
  that classical geometry packages as `Area = ½·|BC|·h_a`.

  Without a length law the foot is characterized only by direction; the metric
  content — how *far* the vertex sits from its opposite side — is missing.

  ## What This File Proves

  For each altitude foot of a non-degenerate triangle we prove a single
  **Lagrange identity** relating the squared altitude length, the squared base,
  and the squared signed area `Δ = (B−A)×(C−A)`:

  ### The altitude-length law (one identity per foot)
  `foot_a_altitude_length_sq` : `|A Hₐ|² · |BC|² = Δ²`
  `foot_b_altitude_length_sq` : `|B H_b|² · |CA|² = Δ²`
  `foot_c_altitude_length_sq` : `|C H_c|² · |AB|² = Δ²`

  Each is a pure polynomial identity: the projection denominator cancels and the
  Lagrange/Cauchy–Binet identity `|u|²|v|² − (u·v)² = (u×v)²` collapses the result
  to the *same* signed area squared, regardless of which side is taken as base.

  ### Connection to the area function
  `foot_a_altitude_area` : `|A Hₐ|² · |BC|² = (2·Area)²` and the b, c analogues.
  Since `Area = |Δ|/2`, the signed area squared is exactly `(2·Area)²`.

  ### Base-independence capstone
  `altitude_length_base_independent` bundles all three: every
  `(altitude length)² · (base length)²` equals the common value `(2·Area)²`,
  so the three altitude–base products agree.  This is the coordinate proof that
  `½·base·height` is well-defined — the area does not depend on the chosen base.

  ### Worked example
  `triangle_345_altitude_a_sq` : for the 3-4-5 triangle the altitude from A onto
  the hypotenuse BC has squared length `144/25` (i.e. `h_a = 12/5`), matching
  `Area = 6` via `6 = ½·5·(12/5)`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ02

open FeuerbachsTheorem

-- ============================================================
-- Part I: The altitude-length law (Lagrange identity per foot)
-- ============================================================

/-- **Altitude-length law at A.** The squared length of the altitude from A times
    the squared base `|BC|²` equals the squared signed area `Δ²`.  Purely
    algebraic: the projection denominator cancels and Lagrange's identity
    `|u|²|v|² − (u·v)² = (u×v)²` reduces the left side to the signed area squared. -/
theorem foot_a_altitude_length_sq (T : Triangle) :
    dist2_sq T.A T.foot_a * ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)
      = ((T.B.1 - T.A.1) * (T.C.2 - T.A.2)
          - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) ^ 2 := by
  unfold dist2_sq Triangle.foot_a
  simp only []
  have hbc : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := bc_sq_ne_zero T
  field_simp
  ring

/-- **Altitude-length law at B.** `|B H_b|² · |CA|² = Δ²`, the same signed area
    squared obtained from a different base. -/
theorem foot_b_altitude_length_sq (T : Triangle) :
    dist2_sq T.B T.foot_b * ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)
      = ((T.B.1 - T.A.1) * (T.C.2 - T.A.2)
          - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) ^ 2 := by
  unfold dist2_sq Triangle.foot_b
  simp only []
  have hca : (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := ca_sq_ne_zero T
  field_simp
  ring

/-- **Altitude-length law at C.** `|C H_c|² · |AB|² = Δ²`. -/
theorem foot_c_altitude_length_sq (T : Triangle) :
    dist2_sq T.C T.foot_c * ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)
      = ((T.B.1 - T.A.1) * (T.C.2 - T.A.2)
          - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) ^ 2 := by
  unfold dist2_sq Triangle.foot_c
  simp only []
  have hab : (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := ab_sq_ne_zero T
  field_simp
  ring

-- ============================================================
-- Part II: Connection to the area function
-- ============================================================

/-- The squared signed area `Δ²` equals `(2·Area)²`, since `Area = |Δ|/2`. -/
theorem two_area_sq (T : Triangle) :
    (2 * T.area) ^ 2
      = ((T.B.1 - T.A.1) * (T.C.2 - T.A.2)
          - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)) ^ 2 := by
  unfold Triangle.area
  rw [show (2 : ℝ) * (|(T.B.1 - T.A.1) * (T.C.2 - T.A.2)
        - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)| / 2)
      = |(T.B.1 - T.A.1) * (T.C.2 - T.A.2)
        - (T.C.1 - T.A.1) * (T.B.2 - T.A.2)| from by ring]
  rw [sq_abs]

/-- Altitude from A in terms of the area: `|A Hₐ|² · |BC|² = (2·Area)²`. -/
theorem foot_a_altitude_area (T : Triangle) :
    dist2_sq T.A T.foot_a * ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)
      = (2 * T.area) ^ 2 := by
  rw [foot_a_altitude_length_sq, two_area_sq]

/-- Altitude from B in terms of the area: `|B H_b|² · |CA|² = (2·Area)²`. -/
theorem foot_b_altitude_area (T : Triangle) :
    dist2_sq T.B T.foot_b * ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)
      = (2 * T.area) ^ 2 := by
  rw [foot_b_altitude_length_sq, two_area_sq]

/-- Altitude from C in terms of the area: `|C H_c|² · |AB|² = (2·Area)²`. -/
theorem foot_c_altitude_area (T : Triangle) :
    dist2_sq T.C T.foot_c * ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)
      = (2 * T.area) ^ 2 := by
  rw [foot_c_altitude_length_sq, two_area_sq]

-- ============================================================
-- Part III: Base-independence capstone
-- ============================================================

/-- **Area is base-independent.** Each of the three products
    `(altitude length)² · (base length)²` equals the common value `(2·Area)²`,
    hence they are all equal to one another.  This is the coordinate proof that
    `½·base·height` does not depend on which side is chosen as the base. -/
theorem altitude_length_base_independent (T : Triangle) :
    dist2_sq T.A T.foot_a * ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2)
      = (2 * T.area) ^ 2 ∧
    dist2_sq T.B T.foot_b * ((T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2)
      = (2 * T.area) ^ 2 ∧
    dist2_sq T.C T.foot_c * ((T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2)
      = (2 * T.area) ^ 2 :=
  ⟨foot_a_altitude_area T, foot_b_altitude_area T, foot_c_altitude_area T⟩

-- ============================================================
-- Part IV: Worked example
-- ============================================================

/-- Worked example: for the 3-4-5 triangle (A = (0,0), B = (3,0), C = (0,4)) the
    altitude from A onto the hypotenuse BC has squared length `144/25`, i.e.
    `h_a = 12/5`.  This matches `Area = 6` via `6 = ½·|BC|·h_a = ½·5·(12/5)`. -/
theorem triangle_345_altitude_a_sq :
    dist2_sq triangle_345.A triangle_345.foot_a = 144 / 25 := by
  unfold triangle_345 dist2_sq Triangle.foot_a
  norm_num

/-- The altitude-length law instantiated at the 3-4-5 triangle: with base
    `|BC|² = 25` and area `6`, the law reads `(144/25)·25 = 144 = (2·6)²`. -/
theorem triangle_345_altitude_law :
    dist2_sq triangle_345.A triangle_345.foot_a
        * ((triangle_345.C.1 - triangle_345.B.1) ^ 2
          + (triangle_345.C.2 - triangle_345.B.2) ^ 2)
      = (2 * triangle_345.area) ^ 2 :=
  foot_a_altitude_area triangle_345

end FeuerbachsTheoremDefsOQ01OQ02
