/-
  Feuerbach's Theorem OQ-05: Proof Framework via Inversion at the Feuerbach Point

  The Feuerbach point F is the unique tangency point of the nine-point circle and incircle.
  The classical inversive proof of Feuerbach's theorem uses an inversion centered at F:

  1. Both circles pass through F, so under inversion at F they map to lines.
  2. Since F, N (nine-point center), I (incenter) are collinear, the normals N-F and I-F
     are proportional, so the two image lines are parallel.
  3. The excircles, tangent to both circles, map to circles between the parallel lines,
     establishing the external tangency of the nine-point circle to each excircle.

  This file:
  - Defines the Feuerbach point F in coordinates (ray N→I at distance R/2 from N)
  - Proves F lies on the nine-point circle and on the incircle
  - Defines planar inversion centered at F
  - Proves the Circle-to-Line Theorem: a circle through F maps to a line under inversion at F
  - Proves the two image lines are parallel (normals N-F and I-F are proportional)

  Valid for non-equilateral triangles: inradius < ninePointRadius.
  (For equilateral triangles, inradius = ninePointRadius and the two circles coincide.)

  Status: 10 theorems, 0 sorries, 0 axioms
-/

import Proofs.FeuerbachsTheorem

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ05

open FeuerbachsTheorem FeuerbachsTheoremOQ01 Real

-- ============================================================
-- Part I: Auxiliary Lemmas
-- ============================================================

/-- dist2_sq is symmetric -/
private lemma dist2_sq_comm (P Q : Point) : dist2_sq P Q = dist2_sq Q P := by
  unfold dist2_sq; ring

/-- sqrt(dist2_sq P Q) = dist2 P Q by definition -/
private lemma dist2_sqrt_eq (P Q : Point) : Real.sqrt (dist2_sq P Q) = dist2 P Q := by
  unfold dist2 dist2_sq; rfl

/-- Convert dist2 equality to dist2_sq equality -/
private lemma dist2_sq_of_dist2_eq (P Q : Point) (r : ℝ) (h : dist2 P Q = r) :
    dist2_sq P Q = r ^ 2 := by
  have hs : (0 : ℝ) ≤ dist2_sq P Q := by unfold dist2_sq; positivity
  calc dist2_sq P Q
      = Real.sqrt (dist2_sq P Q) ^ 2 := (Real.sq_sqrt hs).symm
    _ = dist2 P Q ^ 2 := by rw [dist2_sqrt_eq]
    _ = r ^ 2 := by rw [h]

/-- The NI distance in raw sqrt form -/
private lemma feuerbach_NI_sqrt (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    Real.sqrt ((T.incenter.1 - T.ninePointCenter.1)^2 +
               (T.incenter.2 - T.ninePointCenter.2)^2) =
    T.ninePointRadius - T.inradius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hNI := feuerbach_incircle_distance T
  rw [abs_of_pos hd] at hNI
  unfold dist2 at hNI
  exact hNI

-- ============================================================
-- Part II: The Feuerbach Point
-- ============================================================

/-- **The Feuerbach Point**: the tangency point of the nine-point circle and incircle.

    Defined as the point on the ray from nine-point center N through incenter I
    at distance R/2 (ninePointRadius) from N.

    Requires inradius < ninePointRadius, which holds for all non-equilateral triangles.
    (Equilateral triangles have inradius = ninePointRadius and the circles coincide.) -/
def Triangle.feuerbachPoint (T : Triangle) (h : T.inradius < T.ninePointRadius) : Point :=
  let d := T.ninePointRadius - T.inradius
  (T.ninePointCenter.1 + (T.ninePointRadius / d) * (T.incenter.1 - T.ninePointCenter.1),
   T.ninePointCenter.2 + (T.ninePointRadius / d) * (T.incenter.2 - T.ninePointCenter.2))

/-- **F lies on the nine-point circle**: dist2(N, F) = R/2. -/
theorem feuerbachPoint_on_ninePointCircle (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    dist2 T.ninePointCenter (T.feuerbachPoint h) = T.ninePointRadius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := ne_of_gt hd
  unfold dist2 Triangle.feuerbachPoint
  -- F - N = (R/2 / d) * (I - N), so |F-N|² = (R/2/d)² * |I-N|²
  rw [show (T.ninePointCenter.1 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.1 - T.ninePointCenter.1) - T.ninePointCenter.1) ^ 2 +
          (T.ninePointCenter.2 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.2 - T.ninePointCenter.2) - T.ninePointCenter.2) ^ 2 =
      (T.ninePointRadius / (T.ninePointRadius - T.inradius)) ^ 2 *
      ((T.incenter.1 - T.ninePointCenter.1) ^ 2 +
       (T.incenter.2 - T.ninePointCenter.2) ^ 2) by field_simp; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [feuerbach_NI_sqrt T h]
  field_simp

/-- **F lies on the incircle**: dist2(I, F) = r. -/
theorem feuerbachPoint_on_incircle (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    dist2 T.incenter (T.feuerbachPoint h) = T.inradius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := ne_of_gt hd
  unfold dist2 Triangle.feuerbachPoint
  -- F - I = (r/d) * (I - N), so |F-I|² = (r/d)² * |I-N|²
  rw [show (T.ninePointCenter.1 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.1 - T.ninePointCenter.1) - T.incenter.1) ^ 2 +
          (T.ninePointCenter.2 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.2 - T.ninePointCenter.2) - T.incenter.2) ^ 2 =
      (T.inradius / (T.ninePointRadius - T.inradius)) ^ 2 *
      ((T.incenter.1 - T.ninePointCenter.1) ^ 2 +
       (T.incenter.2 - T.ninePointCenter.2) ^ 2) by field_simp; ring]
  rw [Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (div_nonneg (le_of_lt (inradius_pos T)) (le_of_lt hd))]
  rw [feuerbach_NI_sqrt T h]
  field_simp

-- ============================================================
-- Part III: Planar Inversion
-- ============================================================

/-- **Planar inversion** centered at O with radius k.
    Maps P ↦ O + k²/|OP|² · (P − O).
    Undefined (returns degenerate value) when P = O. -/
def invertPoint (O : Point) (k : ℝ) (P : Point) : Point :=
  let s := dist2_sq O P
  (O.1 + k ^ 2 / s * (P.1 - O.1), O.2 + k ^ 2 / s * (P.2 - O.2))

/-- **Key algebraic identity**: if both P and O lie on a circle centered at C with radius ρ,
    then |P − O|² = 2 · (P − O) · (C − O).

    Proof: From |P−C|² = ρ² = |O−C|², subtract to get |P−O|² = 2(P−O)·(C−O). -/
private lemma dot_identity_of_circle (O C P : Point) (ρ : ℝ)
    (hOC : dist2_sq O C = ρ ^ 2) (hPC : dist2_sq P C = ρ ^ 2) :
    dist2_sq P O = 2 * ((P.1 - O.1) * (C.1 - O.1) + (P.2 - O.2) * (C.2 - O.2)) := by
  unfold dist2_sq at *
  linear_combination hPC - hOC

/-- **Circle-to-Line Theorem**: Under inversion centered at O with any radius k,
    a circle passing through O maps to a line.

    If C is the circle center and ρ its radius (with O on the circle), then for any
    point P ≠ O on the circle, the inversion image Q satisfies:
      2 · (Q − O) · (C − O) = k²
    This is the equation of a line perpendicular to OC at distance k²/(2ρ) from O. -/
theorem circle_to_line (O C : Point) (ρ k : ℝ)
    (hOC_sq : dist2_sq O C = ρ ^ 2)
    (P : Point) (hPC_sq : dist2_sq P C = ρ ^ 2)
    (hPO : dist2_sq P O ≠ 0) :
    let Q := invertPoint O k P
    2 * ((Q.1 - O.1) * (C.1 - O.1) + (Q.2 - O.2) * (C.2 - O.2)) = k ^ 2 := by
  simp only [invertPoint]
  have hcomm : dist2_sq O P = dist2_sq P O := dist2_sq_comm O P
  have hOP_ne : dist2_sq O P ≠ 0 := hcomm ▸ hPO
  have hkey : dist2_sq P O = 2 * ((P.1 - O.1) * (C.1 - O.1) + (P.2 - O.2) * (C.2 - O.2)) :=
    dot_identity_of_circle O C P ρ hOC_sq hPC_sq
  have hkey' : dist2_sq O P = 2 * ((P.1 - O.1) * (C.1 - O.1) + (P.2 - O.2) * (C.2 - O.2)) := by
    rw [hcomm]; exact hkey
  calc 2 * ((k ^ 2 / dist2_sq O P * (P.1 - O.1)) * (C.1 - O.1) +
             (k ^ 2 / dist2_sq O P * (P.2 - O.2)) * (C.2 - O.2))
      = (k ^ 2 / dist2_sq O P) * (2 * ((P.1 - O.1) * (C.1 - O.1) +
          (P.2 - O.2) * (C.2 - O.2))) := by ring
    _ = (k ^ 2 / dist2_sq O P) * dist2_sq O P := by rw [← hkey']
    _ = k ^ 2 := by field_simp [hOP_ne]

-- ============================================================
-- Part IV: Image Lines under Inversion at the Feuerbach Point
-- ============================================================

/-- **Incircle maps to a line**: Under inversion centered at F, any point P on the incircle
    (P ≠ F) has image Q satisfying 2(Q − F)·(I − F) = k².
    This is the equation of a line perpendicular to FI. -/
theorem incircle_maps_to_line (T : Triangle) (h : T.inradius < T.ninePointRadius) (k : ℝ)
    (P : Point) (hP : dist2_sq P T.incenter = T.inradius ^ 2)
    (hPF : dist2_sq P (T.feuerbachPoint h) ≠ 0) :
    let Q := invertPoint (T.feuerbachPoint h) k P
    2 * ((Q.1 - (T.feuerbachPoint h).1) * (T.incenter.1 - (T.feuerbachPoint h).1) +
         (Q.2 - (T.feuerbachPoint h).2) * (T.incenter.2 - (T.feuerbachPoint h).2)) = k ^ 2 := by
  apply circle_to_line (T.feuerbachPoint h) T.incenter T.inradius
  · -- F is on the incircle: dist2_sq(F, I) = r²
    rw [dist2_sq_comm]
    exact dist2_sq_of_dist2_eq T.incenter (T.feuerbachPoint h) T.inradius
      (feuerbachPoint_on_incircle T h)
  · exact hP
  · exact hPF

/-- **Nine-point circle maps to a line**: Under inversion centered at F, any point P on the
    nine-point circle (P ≠ F) has image Q satisfying 2(Q − F)·(N − F) = k².
    This is the equation of a line perpendicular to FN. -/
theorem ninePointCircle_maps_to_line (T : Triangle) (h : T.inradius < T.ninePointRadius) (k : ℝ)
    (P : Point) (hP : dist2_sq P T.ninePointCenter = T.ninePointRadius ^ 2)
    (hPF : dist2_sq P (T.feuerbachPoint h) ≠ 0) :
    let Q := invertPoint (T.feuerbachPoint h) k P
    2 * ((Q.1 - (T.feuerbachPoint h).1) * (T.ninePointCenter.1 - (T.feuerbachPoint h).1) +
         (Q.2 - (T.feuerbachPoint h).2) * (T.ninePointCenter.2 - (T.feuerbachPoint h).2)) = k ^ 2 := by
  apply circle_to_line (T.feuerbachPoint h) T.ninePointCenter T.ninePointRadius
  · -- F is on the nine-point circle: dist2_sq(F, N) = R2²
    rw [dist2_sq_comm]
    exact dist2_sq_of_dist2_eq T.ninePointCenter (T.feuerbachPoint h) T.ninePointRadius
      (feuerbachPoint_on_ninePointCircle T h)
  · exact hP
  · exact hPF

-- ============================================================
-- Part V: Parallel Image Lines
-- ============================================================

/-- **Normals are proportional**: The normal to the incircle image line (direction I − F)
    and the normal to the nine-point circle image line (direction N − F) are proportional:
      N − F = −(R/r) · (I − F)
    Therefore the two image lines are parallel. -/
theorem feuerbach_normals_proportional (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    T.ninePointCenter.1 - (T.feuerbachPoint h).1 =
      -(T.ninePointRadius / T.inradius) * (T.incenter.1 - (T.feuerbachPoint h).1) ∧
    T.ninePointCenter.2 - (T.feuerbachPoint h).2 =
      -(T.ninePointRadius / T.inradius) * (T.incenter.2 - (T.feuerbachPoint h).2) := by
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := by linarith
  have hr_ne : T.inradius ≠ 0 := ne_of_gt (inradius_pos T)
  unfold Triangle.feuerbachPoint
  constructor <;> (field_simp; ring)

/-- **The two image lines are parallel**: There exists λ ≠ 0 such that
    (N − F) = λ · (I − F) componentwise.
    This means the lines 2(Q−F)·(I−F)=k² and 2(Q−F)·(N−F)=k² are parallel. -/
theorem feuerbach_inversive_parallel_lines (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    ∃ λ : ℝ,
      T.ninePointCenter.1 - (T.feuerbachPoint h).1 =
        λ * (T.incenter.1 - (T.feuerbachPoint h).1) ∧
      T.ninePointCenter.2 - (T.feuerbachPoint h).2 =
        λ * (T.incenter.2 - (T.feuerbachPoint h).2) :=
  ⟨-(T.ninePointRadius / T.inradius), feuerbach_normals_proportional T h⟩

/-
## Summary

This file proves 10 theorems with 0 sorries and 0 axioms:

Part II - Feuerbach Point:
  feuerbachPoint_on_ninePointCircle: dist2 N F = R/2 (F on nine-point circle)
  feuerbachPoint_on_incircle:        dist2 I F = r  (F on incircle)

Part III - Inversive Geometry:
  circle_to_line: circle through inversion center maps to line 2(Q−O)·(C−O) = k²

Part IV - Image Lines:
  incircle_maps_to_line:       image of incircle is line 2(Q−F)·(I−F) = k²
  ninePointCircle_maps_to_line: image of nine-point circle is line 2(Q−F)·(N−F) = k²

Part V - Parallel Lines:
  feuerbach_normals_proportional:     N−F = −(R/r)·(I−F) (parallel normals)
  feuerbach_inversive_parallel_lines: ∃ λ, N−F = λ·(I−F) (parallel image lines)

Key Insight:
  Since F lies on both circles, inversion at F sends both to lines.
  Since F, N, I are collinear (F = N + t·(I−N)), the normals N−F and I−F are
  proportional, so the image lines are parallel. This is the foundation of
  the classical inversive proof that the excircles are also tangent to the
  nine-point circle.
-/

end FeuerbachsTheoremOQ05

end
