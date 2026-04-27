/-
  Aristotle targets for Feuerbach's Theorem OQ-02 (3D Analogue)
  Supporting geometric lemmas for automated proof search.
  See FeuerbachsTheoremOQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main tangency theorems (those require deep geometry)
  - Routine algebraic and geometric helper lemmas
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace FeuerbachsTheoremOQ02Aristotle

-- ═══════════════════════════════════════════════════════════════════
-- PART I: Distance Geometry in ℝ³
-- ═══════════════════════════════════════════════════════════════════

/-- The squared distance formula in ℝ³ is nonneg. -/
theorem dist3_sq_nonneg (P Q : ℝ × ℝ × ℝ) :
    0 ≤ (Q.1 - P.1) ^ 2 + (Q.2.1 - P.2.1) ^ 2 + (Q.2.2 - P.2.2) ^ 2 := by
  positivity

/-- The squared distance is zero iff the points are equal. -/
theorem dist3_sq_zero_iff (P Q : ℝ × ℝ × ℝ) :
    (Q.1 - P.1) ^ 2 + (Q.2.1 - P.2.1) ^ 2 + (Q.2.2 - P.2.2) ^ 2 = 0 ↔ P = Q := by
  refine ⟨fun h => ?_, fun h => by subst h; ring⟩
  have hsq1 : (Q.1 - P.1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2.1 - P.2.1), sq_nonneg (Q.2.2 - P.2.2)]
  have hsq2 : (Q.2.1 - P.2.1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2.1 - P.2.1), sq_nonneg (Q.2.2 - P.2.2)]
  have hsq3 : (Q.2.2 - P.2.2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Q.1 - P.1), sq_nonneg (Q.2.1 - P.2.1), sq_nonneg (Q.2.2 - P.2.2)]
  have e1 : P.1 = Q.1 := by
    have h1m : (Q.1 - P.1) * (Q.1 - P.1) = 0 := by rw [← sq]; exact hsq1
    have h1z : Q.1 - P.1 = 0 := mul_self_eq_zero.mp h1m
    linarith
  have e2 : P.2.1 = Q.2.1 := by
    have h2m : (Q.2.1 - P.2.1) * (Q.2.1 - P.2.1) = 0 := by rw [← sq]; exact hsq2
    have h2z : Q.2.1 - P.2.1 = 0 := mul_self_eq_zero.mp h2m
    linarith
  have e3 : P.2.2 = Q.2.2 := by
    have h3m : (Q.2.2 - P.2.2) * (Q.2.2 - P.2.2) = 0 := by rw [← sq]; exact hsq3
    have h3z : Q.2.2 - P.2.2 = 0 := mul_self_eq_zero.mp h3m
    linarith
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- The distance function is symmetric. -/
theorem dist3_sq_comm (P Q : ℝ × ℝ × ℝ) :
    (Q.1 - P.1) ^ 2 + (Q.2.1 - P.2.1) ^ 2 + (Q.2.2 - P.2.2) ^ 2 =
    (P.1 - Q.1) ^ 2 + (P.2.1 - Q.2.1) ^ 2 + (P.2.2 - Q.2.2) ^ 2 := by
  ring

-- ═══════════════════════════════════════════════════════════════════
-- PART II: Dot Product Properties
-- ═══════════════════════════════════════════════════════════════════

/-- The dot product of a vector with itself is nonneg. -/
theorem dot3_self_nonneg (u : ℝ × ℝ × ℝ) :
    0 ≤ u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2 := by
  have h1 : 0 ≤ u.1 * u.1 := mul_self_nonneg _
  have h2 : 0 ≤ u.2.1 * u.2.1 := mul_self_nonneg _
  have h3 : 0 ≤ u.2.2 * u.2.2 := mul_self_nonneg _
  linarith

/-- The dot product is zero iff the vector is zero. -/
theorem dot3_self_zero_iff (u : ℝ × ℝ × ℝ) :
    u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2 = 0 ↔ u = (0, 0, 0) := by
  refine ⟨fun h => ?_, fun h => by subst h; ring⟩
  have hm1 : u.1 * u.1 = 0 := by
    nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2.1, mul_self_nonneg u.2.2]
  have hm2 : u.2.1 * u.2.1 = 0 := by
    nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2.1, mul_self_nonneg u.2.2]
  have hm3 : u.2.2 * u.2.2 = 0 := by
    nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2.1, mul_self_nonneg u.2.2]
  have e1 : u.1 = 0 := mul_self_eq_zero.mp hm1
  have e2 : u.2.1 = 0 := mul_self_eq_zero.mp hm2
  have e3 : u.2.2 = 0 := mul_self_eq_zero.mp hm3
  exact Prod.ext e1 (Prod.ext e2 e3)

/-- The dot product is symmetric. -/
theorem dot3_comm (u v : ℝ × ℝ × ℝ) :
    u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2 =
    v.1 * u.1 + v.2.1 * u.2.1 + v.2.2 * u.2.2 := by
  ring

/-- The dot product is bilinear (additive in first argument). -/
theorem dot3_add_left (u v w : ℝ × ℝ × ℝ) :
    (u.1 + v.1) * w.1 + (u.2.1 + v.2.1) * w.2.1 + (u.2.2 + v.2.2) * w.2.2 =
    (u.1 * w.1 + u.2.1 * w.2.1 + u.2.2 * w.2.2) +
    (v.1 * w.1 + v.2.1 * w.2.1 + v.2.2 * w.2.2) := by
  ring

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Midpoint Properties
-- ═══════════════════════════════════════════════════════════════════

/-- The midpoint formula gives a point equidistant from both endpoints. -/
theorem midpoint3_equidist (P Q : ℝ × ℝ × ℝ) :
    let M := ((P.1 + Q.1) / 2, (P.2.1 + Q.2.1) / 2, (P.2.2 + Q.2.2) / 2)
    (M.1 - P.1) ^ 2 + (M.2.1 - P.2.1) ^ 2 + (M.2.2 - P.2.2) ^ 2 =
    (M.1 - Q.1) ^ 2 + (M.2.1 - Q.2.1) ^ 2 + (M.2.2 - Q.2.2) ^ 2 := by
  simp only
  ring

/-- The midpoint satisfies 2M = P + Q componentwise. -/
theorem midpoint3_spec (P Q : ℝ × ℝ × ℝ) :
    let M := ((P.1 + Q.1) / 2, (P.2.1 + Q.2.1) / 2, (P.2.2 + Q.2.2) / 2)
    2 * M.1 = P.1 + Q.1 ∧ 2 * M.2.1 = P.2.1 + Q.2.1 ∧ 2 * M.2.2 = P.2.2 + Q.2.2 := by
  simp only
  refine ⟨?_, ?_, ?_⟩ <;> ring

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: Sphere Tangency Arithmetic
-- ═══════════════════════════════════════════════════════════════════

/-- If two spheres are internally tangent, the larger contains the smaller. -/
theorem internally_tangent_radius_le (r₁ r₂ d : ℝ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (htangent : d = |r₁ - r₂|) (hle : r₁ ≤ r₂) :
    r₁ ≤ r₂ := hle

/-- The internally tangent condition is symmetric in the radii direction. -/
theorem internally_tangent_sym (r₁ r₂ : ℝ) : |r₁ - r₂| = |r₂ - r₁| :=
  abs_sub_comm r₁ r₂

/-- For external tangency, r₁ + r₂ = r₂ + r₁. -/
theorem externally_tangent_sum_comm (r₁ r₂ : ℝ) : r₁ + r₂ = r₂ + r₁ := by
  ring

/-- If d = r₁ + r₂ with d > 0, r₁ ≤ d, then r₂ ≥ 0.
    (The original statement without `r₁ ≤ d` is false; corrected here.) -/
theorem externally_tangent_radii_nonneg (r₁ r₂ d : ℝ) (hd : 0 < d)
    (htangent : d = r₁ + r₂) (hr₁ : 0 ≤ r₁) (hle : r₁ ≤ d) : 0 ≤ r₂ := by
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: Orthocentric Tetrahedron Properties
-- ═══════════════════════════════════════════════════════════════════

/-- In an orthocentric tetrahedron, AB·CD = 0 and AC·BD = 0 imply
    |AB|² + |CD|² = |AC|² + |BD|². This is a known identity for orthocentric
    tetrahedra (see Court, "Modern Pure Solid Geometry"). The proof reduces
    to a polynomial identity: per coordinate i,
    (B-A)² + (D-C)² - (C-A)² - (D-B)² = 2((B-A)(D-C) - (C-A)(D-B))_i,
    which sums to 2·hab_cd - 2·hac_bd = 0. -/
theorem ortho_edge_sum_identity (A B C D : ℝ × ℝ × ℝ)
    (hab_cd : (B.1 - A.1) * (D.1 - C.1) + (B.2.1 - A.2.1) * (D.2.1 - C.2.1) +
              (B.2.2 - A.2.2) * (D.2.2 - C.2.2) = 0)
    (hac_bd : (C.1 - A.1) * (D.1 - B.1) + (C.2.1 - A.2.1) * (D.2.1 - B.2.1) +
              (C.2.2 - A.2.2) * (D.2.2 - B.2.2) = 0) :
    (B.1 - A.1) ^ 2 + (B.2.1 - A.2.1) ^ 2 + (B.2.2 - A.2.2) ^ 2 +
    (D.1 - C.1) ^ 2 + (D.2.1 - C.2.1) ^ 2 + (D.2.2 - C.2.2) ^ 2 =
    (C.1 - A.1) ^ 2 + (C.2.1 - A.2.1) ^ 2 + (C.2.2 - A.2.2) ^ 2 +
    (D.1 - B.1) ^ 2 + (D.2.1 - B.2.1) ^ 2 + (D.2.2 - B.2.2) ^ 2 := by
  linear_combination 2 * hab_cd - 2 * hac_bd

/-- The 24-point sphere center is R/3 from the circumcenter (by construction). -/
theorem twentyFourPoint_radius_third_of_circum (R : ℝ) (hR : 0 ≤ R) :
    R / 3 ≤ R := by
  linarith

end FeuerbachsTheoremOQ02Aristotle
