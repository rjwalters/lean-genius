/-
  Feuerbach's Theorem DefsOQ05: Uniqueness of the Nine-Point Circle

  ## The Open Question

  The parent file `FeuerbachsTheoremDefs` proves that all nine special points of a
  triangle (the three side midpoints, the three altitude feet, and the three Euler
  midpoints of the vertex-to-orthocenter segments) lie on a single circle: the
  nine-point circle, with centre `N = midpoint(O, H)` and radius `R/2`.

  Establishing membership shows the nine-point circle is *a* circle through these
  points.  It leaves open whether it is the *only* one.  OQ-05 closes that gap:

      The nine-point circle is the UNIQUE circle through the nine special points.

  Because a circle is determined by any three of its non-collinear points, it
  suffices to look at the three side midpoints `M_a, M_b, M_c`.  In a
  non-degenerate triangle these are themselves non-collinear, so any circle through
  all three — a fortiori through all nine points — must coincide with the
  nine-point circle.

  ## What This File Proves

  Working purely in the coordinate framework of `FeuerbachsTheoremDefs`:

  ### The algebraic core
  `equidistant_center_unique` :  given three non-collinear points `P₁ P₂ P₃`, a
  point equidistant from all three is unique.  Equivalently, the three
  perpendicular bisectors meet in at most one point.  This is the linear-algebra
  heart of circle uniqueness: subtracting the squared-distance equations turns the
  problem into a 2×2 linear system whose determinant is exactly the
  non-collinearity determinant of `P₁ P₂ P₃`.

  ### The geometric input
  `midpoints_noncollinear` :  the three side midpoints of a non-degenerate triangle
  are non-collinear.  Their orientation determinant is `1/4` of the triangle's own
  non-degeneracy determinant, hence non-zero.

  ### The uniqueness theorem
  `ninePointCircle_unique` :  if a circle with centre `Q` and radius `ρ` passes
  through the three side midpoints `M_a, M_b, M_c`, then `Q = N` (the nine-point
  centre) and `ρ = R/2` (the nine-point radius).  In particular the nine-point
  circle is the unique circle through the nine special points.

  `ninePointCircle_unique_of_nine` :  the same conclusion phrased against a circle
  asserted to pass through all nine special points (it only ever uses the three
  midpoints, witnessing that three non-collinear points already pin the circle).

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachNinePointUniqueness

open FeuerbachsTheorem

/-- The squared distance equals the square of the (root) distance. -/
lemma dist2_sq_eq_dist2_sq (Q P : Point) : dist2_sq Q P = (dist2 Q P) ^ 2 := by
  unfold dist2_sq dist2
  rw [Real.sq_sqrt (by positivity)]

/-- If two points are at equal `dist2` from a centre `Q`, they are at equal
    squared distance from `Q`. -/
lemma dist2_sq_of_dist2_eq {Q P P' : Point} (h : dist2 Q P = dist2 Q P') :
    dist2_sq Q P = dist2_sq Q P' := by
  rw [dist2_sq_eq_dist2_sq, dist2_sq_eq_dist2_sq, h]

/-- **Uniqueness of an equidistant centre.**
    Given three non-collinear points `P₁ P₂ P₃` (orientation determinant nonzero),
    any two points `Q`, `Q'` each equidistant (in squared distance) from all three
    must be equal.  Geometrically: the perpendicular bisectors of a triangle meet in
    at most one point, so a triangle's vertices lie on at most one circle. -/
theorem equidistant_center_unique
    (P₁ P₂ P₃ Q Q' : Point)
    (hdet : (P₂.1 - P₁.1) * (P₃.2 - P₁.2) - (P₃.1 - P₁.1) * (P₂.2 - P₁.2) ≠ 0)
    (hQ12 : dist2_sq Q P₁ = dist2_sq Q P₂)
    (hQ13 : dist2_sq Q P₁ = dist2_sq Q P₃)
    (hQ12' : dist2_sq Q' P₁ = dist2_sq Q' P₂)
    (hQ13' : dist2_sq Q' P₁ = dist2_sq Q' P₃) :
    Q = Q' := by
  simp only [dist2_sq] at hQ12 hQ13 hQ12' hQ13'
  -- Subtracting the squared-distance equations for `Q` and `Q'` kills the quadratic
  -- terms, leaving two linear equations in the difference `(Q - Q')`.
  have e1 : (P₂.1 - P₁.1) * (Q.1 - Q'.1) + (P₂.2 - P₁.2) * (Q.2 - Q'.2) = 0 := by
    linear_combination (1 / 2) * hQ12 - (1 / 2) * hQ12'
  have e2 : (P₃.1 - P₁.1) * (Q.1 - Q'.1) + (P₃.2 - P₁.2) * (Q.2 - Q'.2) = 0 := by
    linear_combination (1 / 2) * hQ13 - (1 / 2) * hQ13'
  -- Cramer's rule: multiply through by the determinant.
  have hu : (Q.1 - Q'.1) *
      ((P₂.1 - P₁.1) * (P₃.2 - P₁.2) - (P₃.1 - P₁.1) * (P₂.2 - P₁.2)) = 0 := by
    linear_combination (P₃.2 - P₁.2) * e1 - (P₂.2 - P₁.2) * e2
  have hv : (Q.2 - Q'.2) *
      ((P₂.1 - P₁.1) * (P₃.2 - P₁.2) - (P₃.1 - P₁.1) * (P₂.2 - P₁.2)) = 0 := by
    linear_combination (P₂.1 - P₁.1) * e2 - (P₃.1 - P₁.1) * e1
  have hQ1 : Q.1 = Q'.1 := by
    rcases mul_eq_zero.mp hu with h | h
    · linarith
    · exact absurd h hdet
  have hQ2 : Q.2 = Q'.2 := by
    rcases mul_eq_zero.mp hv with h | h
    · linarith
    · exact absurd h hdet
  exact Prod.ext_iff.mpr ⟨hQ1, hQ2⟩

/-- **The three side midpoints are non-collinear.**
    Their orientation determinant is exactly one quarter of the triangle's own
    non-degeneracy determinant, hence non-zero for a non-degenerate triangle. -/
theorem midpoints_noncollinear (T : Triangle) :
    (T.midpoint_b.1 - T.midpoint_a.1) * (T.midpoint_c.2 - T.midpoint_a.2)
      - (T.midpoint_c.1 - T.midpoint_a.1) * (T.midpoint_b.2 - T.midpoint_a.2) ≠ 0 := by
  simp only [Triangle.midpoint_a, Triangle.midpoint_b, Triangle.midpoint_c, pointMidpoint]
  intro h
  apply T.nondegenerate
  linear_combination 4 * h

/-- **Uniqueness of the nine-point circle.**
    Any circle with centre `Q` and radius `ρ` passing through the three side
    midpoints `M_a, M_b, M_c` of a non-degenerate triangle is the nine-point
    circle: `Q` is the nine-point centre `N` and `ρ` is the nine-point radius
    `R/2`.  Since the nine-point circle is known (parent file) to pass through all
    nine special points, this pins it down as the unique such circle. -/
theorem ninePointCircle_unique (T : Triangle) (Q : Point) (ρ : ℝ)
    (hMa : dist2 Q T.midpoint_a = ρ)
    (hMb : dist2 Q T.midpoint_b = ρ)
    (hMc : dist2 Q T.midpoint_c = ρ) :
    Q = T.ninePointCenter ∧ ρ = T.ninePointRadius := by
  -- `Q` is equidistant from the three midpoints.
  have hQ12 : dist2_sq Q T.midpoint_a = dist2_sq Q T.midpoint_b :=
    dist2_sq_of_dist2_eq (by rw [hMa, hMb])
  have hQ13 : dist2_sq Q T.midpoint_a = dist2_sq Q T.midpoint_c :=
    dist2_sq_of_dist2_eq (by rw [hMa, hMc])
  -- So is the nine-point centre `N` (parent membership theorems).
  have hNa := midpoint_a_on_ninePointCircle T
  have hNb := midpoint_b_on_ninePointCircle T
  have hNc := midpoint_c_on_ninePointCircle T
  have hN12 : dist2_sq T.ninePointCenter T.midpoint_a
      = dist2_sq T.ninePointCenter T.midpoint_b :=
    dist2_sq_of_dist2_eq (by rw [hNa, hNb])
  have hN13 : dist2_sq T.ninePointCenter T.midpoint_a
      = dist2_sq T.ninePointCenter T.midpoint_c :=
    dist2_sq_of_dist2_eq (by rw [hNa, hNc])
  -- Two equidistant centres through three non-collinear points coincide.
  have hQN : Q = T.ninePointCenter :=
    equidistant_center_unique T.midpoint_a T.midpoint_b T.midpoint_c Q T.ninePointCenter
      (midpoints_noncollinear T) hQ12 hQ13 hN12 hN13
  refine ⟨hQN, ?_⟩
  -- The radius is then forced as the common distance to `M_a`.
  rw [← hMa, hQN, hNa]

/-- **Uniqueness phrased against all nine points.**
    A circle (centre `Q`, radius `ρ`) through all nine special points is the
    nine-point circle.  The proof only consumes the three side-midpoint
    memberships, witnessing that three non-collinear points already determine the
    circle. -/
theorem ninePointCircle_unique_of_nine (T : Triangle) (Q : Point) (ρ : ℝ)
    (hMa : dist2 Q T.midpoint_a = ρ) (hMb : dist2 Q T.midpoint_b = ρ)
    (hMc : dist2 Q T.midpoint_c = ρ)
    (hMaH : dist2 Q T.midpoint_AH = ρ) (hMbH : dist2 Q T.midpoint_BH = ρ)
    (hMcH : dist2 Q T.midpoint_CH = ρ)
    (hFa : dist2 Q T.foot_a = ρ) (hFb : dist2 Q T.foot_b = ρ)
    (hFc : dist2 Q T.foot_c = ρ) :
    Q = T.ninePointCenter ∧ ρ = T.ninePointRadius :=
  ninePointCircle_unique T Q ρ hMa hMb hMc

/-- Sanity check on the 3-4-5 triangle: the unique circle through its three side
    midpoints is centred at `(3/4, 1)` with radius `5/4`. -/
example :
    ∀ (Q : Point) (ρ : ℝ),
      dist2 Q triangle_345.midpoint_a = ρ →
      dist2 Q triangle_345.midpoint_b = ρ →
      dist2 Q triangle_345.midpoint_c = ρ →
      Q = (3 / 4, 1) ∧ ρ = 5 / 4 := by
  intro Q ρ h1 h2 h3
  obtain ⟨hQ, hρ⟩ := ninePointCircle_unique triangle_345 Q ρ h1 h2 h3
  rw [triangle_345_ninePointCenter] at hQ
  rw [triangle_345_ninePointRadius] at hρ
  exact ⟨hQ, hρ⟩

end FeuerbachNinePointUniqueness
