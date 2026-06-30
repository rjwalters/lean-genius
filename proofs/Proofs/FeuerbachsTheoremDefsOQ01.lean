/-
  Feuerbach's Theorem DefsOQ01: The Defining Lemmas of the Altitude Feet

  ## The Open Question

  The parent file `FeuerbachsTheoremDefs` defines the foot of each altitude as an
  explicit orthogonal-projection formula and proves the deep fact that all three
  feet lie on the nine-point circle.  But it never verifies the *defining*
  characterization of an altitude foot, namely that

    1. the foot lies on the opposite side line (collinearity), and
    2. the segment from the vertex to the foot is perpendicular to that side.

  These two facts are exactly what makes the point an "altitude foot."  Without
  them the on-circle membership theorem is a statement about an opaque formula.

  ## What This File Proves

  For each altitude foot Hₐ, H_b, H_c of a non-degenerate triangle:

  ### Collinearity (the foot lies on the opposite side)
  `foot_a_collinear` : Hₐ, B, C are collinear (signed-area / cross product = 0).
  This is a pure algebraic identity: Hₐ − B is a scalar multiple of C − B, so the
  denominator cancels and no non-degeneracy hypothesis is needed.

  ### Perpendicularity (the altitude is orthogonal to the side)
  `foot_a_perp` : (Hₐ − A) · (C − B) = 0.
  Here the side length must be non-zero, supplied by the parent lemma.

  ### Pythagoras at the foot
  `foot_a_pythagoras` : |A Hₐ|² + |Hₐ B|² = |A B|².
  The right angle at the foot gives an exact Pythagorean split of the side toward B.

  ### Uniqueness
  `foot_a_unique` : the foot is the *only* point on line BC whose join to A is
  perpendicular to BC.

  ### Capstone and example
  `altitude_feet_characterization` bundles collinearity + perpendicularity for all
  three feet; `triangle_345_foot_a` evaluates Hₐ = (48/25, 36/25) for the 3-4-5
  right triangle.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01

open FeuerbachsTheorem

-- ============================================================
-- Part I: Collinearity of each foot with the opposite side
-- ============================================================

/-- The foot of the altitude from A is collinear with B and C: the signed area of
    the triangle (Hₐ, B, C) vanishes.  Purely algebraic — Hₐ − B is a scalar
    multiple of C − B, so the projection denominator cancels. -/
theorem foot_a_collinear (T : Triangle) :
    (T.foot_a.1 - T.B.1) * (T.C.2 - T.B.2)
      - (T.foot_a.2 - T.B.2) * (T.C.1 - T.B.1) = 0 := by
  unfold Triangle.foot_a
  simp only []
  ring

/-- The foot of the altitude from B is collinear with C and A. -/
theorem foot_b_collinear (T : Triangle) :
    (T.foot_b.1 - T.C.1) * (T.A.2 - T.C.2)
      - (T.foot_b.2 - T.C.2) * (T.A.1 - T.C.1) = 0 := by
  unfold Triangle.foot_b
  simp only []
  ring

/-- The foot of the altitude from C is collinear with A and B. -/
theorem foot_c_collinear (T : Triangle) :
    (T.foot_c.1 - T.A.1) * (T.B.2 - T.A.2)
      - (T.foot_c.2 - T.A.2) * (T.B.1 - T.A.1) = 0 := by
  unfold Triangle.foot_c
  simp only []
  ring

-- ============================================================
-- Part II: Perpendicularity of each altitude to its side
-- ============================================================

/-- The altitude AHₐ is perpendicular to side BC: (Hₐ − A) · (C − B) = 0. -/
theorem foot_a_perp (T : Triangle) :
    (T.foot_a.1 - T.A.1) * (T.C.1 - T.B.1)
      + (T.foot_a.2 - T.A.2) * (T.C.2 - T.B.2) = 0 := by
  unfold Triangle.foot_a
  simp only []
  have hbc : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := bc_sq_ne_zero T
  field_simp
  ring

/-- The altitude BH_b is perpendicular to side CA: (H_b − B) · (A − C) = 0. -/
theorem foot_b_perp (T : Triangle) :
    (T.foot_b.1 - T.B.1) * (T.A.1 - T.C.1)
      + (T.foot_b.2 - T.B.2) * (T.A.2 - T.C.2) = 0 := by
  unfold Triangle.foot_b
  simp only []
  have hca : (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := ca_sq_ne_zero T
  field_simp
  ring

/-- The altitude CH_c is perpendicular to side AB: (H_c − C) · (B − A) = 0. -/
theorem foot_c_perp (T : Triangle) :
    (T.foot_c.1 - T.C.1) * (T.B.1 - T.A.1)
      + (T.foot_c.2 - T.C.2) * (T.B.2 - T.A.2) = 0 := by
  unfold Triangle.foot_c
  simp only []
  have hab : (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := ab_sq_ne_zero T
  field_simp
  ring

-- ============================================================
-- Part III: Pythagoras at the foot
-- ============================================================

/-- Right angle at the foot Hₐ gives a Pythagorean split toward B:
    |A Hₐ|² + |Hₐ B|² = |A B|² (all squared distances, no `sqrt`). -/
theorem foot_a_pythagoras (T : Triangle) :
    dist2_sq T.A T.foot_a + dist2_sq T.foot_a T.B = dist2_sq T.A T.B := by
  unfold dist2_sq Triangle.foot_a
  simp only []
  have hbc : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := bc_sq_ne_zero T
  field_simp
  ring

/-- Pythagorean split at H_b toward C: |B H_b|² + |H_b C|² = |B C|². -/
theorem foot_b_pythagoras (T : Triangle) :
    dist2_sq T.B T.foot_b + dist2_sq T.foot_b T.C = dist2_sq T.B T.C := by
  unfold dist2_sq Triangle.foot_b
  simp only []
  have hca : (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := ca_sq_ne_zero T
  field_simp
  ring

/-- Pythagorean split at H_c toward A: |C H_c|² + |H_c A|² = |C A|². -/
theorem foot_c_pythagoras (T : Triangle) :
    dist2_sq T.C T.foot_c + dist2_sq T.foot_c T.A = dist2_sq T.C T.A := by
  unfold dist2_sq Triangle.foot_c
  simp only []
  have hab : (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := ab_sq_ne_zero T
  field_simp
  ring

-- ============================================================
-- Part IV: Uniqueness of the foot on its side line
-- ============================================================

/-- The foot Hₐ is the *unique* point on line BC whose join to A is perpendicular
    to BC.  Any point `P = B + s·(C − B)` with `(P − A) · (C − B) = 0` equals Hₐ. -/
theorem foot_a_unique (T : Triangle) (s : ℝ)
    (hperp : (T.B.1 + s * (T.C.1 - T.B.1) - T.A.1) * (T.C.1 - T.B.1)
        + (T.B.2 + s * (T.C.2 - T.B.2) - T.A.2) * (T.C.2 - T.B.2) = 0) :
    (T.B.1 + s * (T.C.1 - T.B.1), T.B.2 + s * (T.C.2 - T.B.2)) = T.foot_a := by
  have hbc : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := bc_sq_ne_zero T
  -- The perpendicularity constraint pins down the parameter s.
  have hs : s = ((T.A.1 - T.B.1) * (T.C.1 - T.B.1)
      + (T.A.2 - T.B.2) * (T.C.2 - T.B.2))
      / ((T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2) := by
    field_simp
    nlinarith [hperp]
  unfold Triangle.foot_a
  simp only []
  rw [hs]

-- ============================================================
-- Part V: Capstone and worked example
-- ============================================================

/-- **The defining characterization of the three altitude feet.**
    Each foot lies on the opposite side (collinearity) and the altitude through it
    is perpendicular to that side. -/
theorem altitude_feet_characterization (T : Triangle) :
    -- foot from A
    ((T.foot_a.1 - T.B.1) * (T.C.2 - T.B.2)
        - (T.foot_a.2 - T.B.2) * (T.C.1 - T.B.1) = 0 ∧
      (T.foot_a.1 - T.A.1) * (T.C.1 - T.B.1)
        + (T.foot_a.2 - T.A.2) * (T.C.2 - T.B.2) = 0) ∧
    -- foot from B
    ((T.foot_b.1 - T.C.1) * (T.A.2 - T.C.2)
        - (T.foot_b.2 - T.C.2) * (T.A.1 - T.C.1) = 0 ∧
      (T.foot_b.1 - T.B.1) * (T.A.1 - T.C.1)
        + (T.foot_b.2 - T.B.2) * (T.A.2 - T.C.2) = 0) ∧
    -- foot from C
    ((T.foot_c.1 - T.A.1) * (T.B.2 - T.A.2)
        - (T.foot_c.2 - T.A.2) * (T.B.1 - T.A.1) = 0 ∧
      (T.foot_c.1 - T.C.1) * (T.B.1 - T.A.1)
        + (T.foot_c.2 - T.C.2) * (T.B.2 - T.A.2) = 0) :=
  ⟨⟨foot_a_collinear T, foot_a_perp T⟩,
   ⟨foot_b_collinear T, foot_b_perp T⟩,
   ⟨foot_c_collinear T, foot_c_perp T⟩⟩

/-- Worked example: for the 3-4-5 right triangle (A = (0,0), B = (3,0), C = (0,4))
    the foot of the altitude from A onto BC is (48/25, 36/25). -/
theorem triangle_345_foot_a : triangle_345.foot_a = (48 / 25, 36 / 25) := by
  unfold triangle_345 Triangle.foot_a
  norm_num
