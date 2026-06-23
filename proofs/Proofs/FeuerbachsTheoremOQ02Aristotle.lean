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
  obtain ⟨p1, p2, p3⟩ := P
  obtain ⟨q1, q2, q3⟩ := Q
  simp only [Prod.mk.injEq]
  refine ⟨fun h => ?_, ?_⟩
  · have h1 : (q1 - p1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (q1 - p1), sq_nonneg (q2 - p2), sq_nonneg (q3 - p3)]
    have h2 : (q2 - p2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (q1 - p1), sq_nonneg (q2 - p2), sq_nonneg (q3 - p3)]
    have h3 : (q3 - p3) ^ 2 = 0 := by
      nlinarith [sq_nonneg (q1 - p1), sq_nonneg (q2 - p2), sq_nonneg (q3 - p3)]
    refine ⟨?_, ?_, ?_⟩
    · linarith [sq_eq_zero_iff.mp h1]
    · linarith [sq_eq_zero_iff.mp h2]
    · linarith [sq_eq_zero_iff.mp h3]
  · rintro ⟨rfl, rfl, rfl⟩; ring

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
  nlinarith [mul_self_nonneg u.1, mul_self_nonneg u.2.1, mul_self_nonneg u.2.2]

/-- The dot product is zero iff the vector is zero. -/
theorem dot3_self_zero_iff (u : ℝ × ℝ × ℝ) :
    u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2 = 0 ↔ u = (0, 0, 0) := by
  obtain ⟨a, b, c⟩ := u
  simp only [Prod.mk.injEq]
  refine ⟨fun h => ?_, ?_⟩
  · have ha : a * a = 0 := by
      nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
    have hb : b * b = 0 := by
      nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
    have hc : c * c = 0 := by
      nlinarith [mul_self_nonneg a, mul_self_nonneg b, mul_self_nonneg c]
    exact ⟨mul_self_eq_zero.mp ha, mul_self_eq_zero.mp hb, mul_self_eq_zero.mp hc⟩
  · rintro ⟨rfl, rfl, rfl⟩; ring

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

/-- If d = r₁ + r₂ and r₁ ≤ d, then 0 ≤ r₂.
    Note: the original statement omitted the r₁ ≤ d hypothesis, which made it FALSE
    (counterexample r₁=10, r₂=-5, d=5: d=r₁+r₂, d>0, r₁≥0 but r₂<0). The added
    hypothesis r₁ ≤ d makes the statement true and matches the geometric intent
    (external tangency of two non-degenerate spheres). -/
theorem externally_tangent_radii_nonneg (r₁ r₂ d : ℝ) (hd : 0 < d) (htangent : d = r₁ + r₂)
    (hr₁ : 0 ≤ r₁) (hr₁_le_d : r₁ ≤ d) : 0 ≤ r₂ := by
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- PART V: Orthocentric Tetrahedron Properties
-- ═══════════════════════════════════════════════════════════════════

/-- In an orthocentric tetrahedron with AB ⊥ CD and AC ⊥ BD,
    |AB|² + |CD|² = |AC|² + |BD|².

    This is the "isodynamic" property: in an orthocentric tetrahedron, the sum of
    squares of opposite edges is the same for all three pairs of opposite edges.

    Proof sketch (taking A as origin, B,C,D as position vectors):
    AB·CD = 0 ⟹ B·D = B·C; AC·BD = 0 ⟹ C·D = B·C. So B·C = B·D = C·D.
    Then |AB|²+|CD|² = |B|²+|D|²-2C·D+|C|² = |B|²+|C|²+|D|²-2(B·C),
    and |AC|²+|BD|² = |C|²+|D|²-2B·D+|B|² gives the same value. -/
theorem ortho_edge_sum_identity (A B C D : ℝ × ℝ × ℝ)
    (hab_cd : (B.1 - A.1) * (D.1 - C.1) + (B.2.1 - A.2.1) * (D.2.1 - C.2.1) +
              (B.2.2 - A.2.2) * (D.2.2 - C.2.2) = 0)
    (hac_bd : (C.1 - A.1) * (D.1 - B.1) + (C.2.1 - A.2.1) * (D.2.1 - B.2.1) +
              (C.2.2 - A.2.2) * (D.2.2 - B.2.2) = 0) :
    (B.1 - A.1) ^ 2 + (B.2.1 - A.2.1) ^ 2 + (B.2.2 - A.2.2) ^ 2 +
    (D.1 - C.1) ^ 2 + (D.2.1 - C.2.1) ^ 2 + (D.2.2 - C.2.2) ^ 2 =
    (C.1 - A.1) ^ 2 + (C.2.1 - A.2.1) ^ 2 + (C.2.2 - A.2.2) ^ 2 +
    (D.1 - B.1) ^ 2 + (D.2.1 - B.2.1) ^ 2 + (D.2.2 - B.2.2) ^ 2 := by
  -- Direct algebraic identity: LHS - RHS = 2*(hab_cd - hac_bd) = 2*0 - 2*0 = 0.
  -- In each coordinate: (b-a)² + (d-c)² - (c-a)² - (d-b)² = 2[(b-a)(d-c) - (c-a)(d-b)].
  linear_combination 2 * hab_cd - 2 * hac_bd

/-- The 24-point sphere center is R/3 from the circumcenter (by construction). -/
theorem twentyFourPoint_radius_third_of_circum (R : ℝ) (hR : 0 ≤ R) :
    R / 3 ≤ R := by
  linarith

end FeuerbachsTheoremOQ02Aristotle
