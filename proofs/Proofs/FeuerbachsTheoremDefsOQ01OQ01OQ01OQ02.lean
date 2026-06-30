/-
  Feuerbach's Theorem DefsOQ01OQ01OQ01OQ02: Distances from the Orthocenter to the
  Vertices — AH² = 4R² − a²

  ## The Open Question

  The metric strand of the orthocenter sub-line has so far measured the distance
  from the circumcenter to the orthocenter:

  * `FeuerbachsTheoremDefsOQ01OQ01OQ01OQ01` proved Euler's metric identity
    `OH² = 9R² − (a² + b² + c²)`.

  The remaining classical metric facts about `H` are the **distances from the
  orthocenter to the three vertices**.  These are the squared form of the
  textbook relation `AH = 2R·cos A`:

      AH² = 4R² − a²,   BH² = 4R² − b²,   CH² = 4R² − c²,

  the distance from a vertex to the orthocenter in terms of the circumradius `R`
  and the *opposite* side length.  (Indeed `a = 2R sin A`, so
  `4R² − a² = 4R²cos²A = (2R cos A)²`.)

  ## What This File Proves

  ### The headline identities (one per vertex)
  `orthocenter_vertex_A_dist_sq` : `AH² = 4·|O−A|² − |B−C|²`  (squared-distance form)
  `orthocenter_vertex_A_dist_classical` : `AH² = 4R² − a²`     (textbook form),
  and the `B`, `C` analogues.

  Each reduces, after substituting `H = A + B + C − 2O`, to a polynomial identity
  modulo the two circumcenter-equidistance relations
  `|B − O|² = |A − O|²` and `|C − O|² = |A − O|²`.  For the `A` version one checks

      AH² − [4R² − a²] = 2(|B−O|² − |A−O|²) + 2(|C−O|² − |A−O|²),

  so a single `linear_combination` over the two equidistance facts discharges it.

  ### The sum and its link to Euler's identity
  `orthocenter_vertex_sum_sq` :
      `AH² + BH² + CH² = 12R² − (a² + b² + c²)`,
  and the clean relation to the circumcenter–orthocenter distance
  `orthocenter_vertex_sum_eq_OH` :
      `AH² + BH² + CH² = OH² + 3R²`
  (consistent with `OH² = 9R² − (a²+b²+c²)`: the two differ by exactly `3R²`).

  ### Consequence
  `orthocenter_vertex_le_diameter_sq` : `AH² ≤ 4R²` — a vertex never lies farther
  from the orthocenter than the diameter of the circumcircle.

  ### Worked example
  For the 3-4-5 right triangle the orthocenter coincides with the right-angle
  vertex `A`, so `AH² = 0 = 4R² − a² = 25 − 25`, while `BH² = 9`, `CH² = 16`,
  summing to `25 = 12R² − (a²+b²+c²)`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01OQ01OQ02

open FeuerbachsTheorem

-- ============================================================
-- Part 0: Pairwise equidistance of the circumcenter
--
-- The parent declares the equidistance facts `private`; we reprove the two we
-- need (against vertex A) so this file builds independently.  Each follows from
-- the perpendicular-bisector identity, which is *linear* in O.
-- ============================================================

set_option maxHeartbeats 6400000 in
private lemma perp_bisector_AB (T : Triangle) :
    (T.B.1 - T.A.1) * (T.B.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.B.2 - T.A.2) * (T.B.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]
  field_simp [hd_ne]
  ring

set_option maxHeartbeats 6400000 in
private lemma perp_bisector_AC (T : Triangle) :
    (T.C.1 - T.A.1) * (T.C.1 + T.A.1 - 2 * T.circumcenter.1) +
    (T.C.2 - T.A.2) * (T.C.2 + T.A.2 - 2 * T.circumcenter.2) = 0 := by
  set d := 2 * ((T.A.1 - T.C.1) * (T.B.2 - T.C.2) - (T.B.1 - T.C.1) * (T.A.2 - T.C.2))
  have hd_ne : d ≠ 0 := circumcenter_denom_ne_zero T
  have hox : T.circumcenter.1 = ((T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.2 - T.C.2) -
    (T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.2 - T.C.2)) / d := by
    unfold Triangle.circumcenter; dsimp
  have hoy : T.circumcenter.2 = ((T.B.1^2 + T.B.2^2 - T.C.1^2 - T.C.2^2) * (T.A.1 - T.C.1) -
    (T.A.1^2 + T.A.2^2 - T.C.1^2 - T.C.2^2) * (T.B.1 - T.C.1)) / d := by
    unfold Triangle.circumcenter; dsimp
  rw [hox, hoy]
  field_simp [hd_ne]
  ring

/-- `|B - O|² = |A - O|²` : the circumcenter is equidistant from `A` and `B`. -/
private lemma equidistB (T : Triangle) :
    (T.B.1 - T.circumcenter.1) ^ 2 + (T.B.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := perp_bisector_AB T
  nlinarith [sq_nonneg (T.B.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.B.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

/-- `|C - O|² = |A - O|²` : the circumcenter is equidistant from `A` and `C`. -/
private lemma equidistC (T : Triangle) :
    (T.C.1 - T.circumcenter.1) ^ 2 + (T.C.2 - T.circumcenter.2) ^ 2 =
    (T.A.1 - T.circumcenter.1) ^ 2 + (T.A.2 - T.circumcenter.2) ^ 2 := by
  have h := perp_bisector_AC T
  nlinarith [sq_nonneg (T.C.1 - T.circumcenter.1), sq_nonneg (T.A.1 - T.circumcenter.1),
             sq_nonneg (T.C.2 - T.circumcenter.2), sq_nonneg (T.A.2 - T.circumcenter.2)]

-- ============================================================
-- Part I: squared distance vs. the metric `dist2`
-- ============================================================

/-- `dist2` is the square root of `dist2_sq`, so squaring recovers it. -/
lemma sq_dist2 (P Q : Point) : (dist2 P Q) ^ 2 = dist2_sq P Q := by
  unfold dist2 dist2_sq
  rw [Real.sq_sqrt (by positivity)]

-- ============================================================
-- Part II: Distances from the orthocenter to each vertex
--
-- With H = A + B + C − 2O one has, in O-centered coordinates a = A − O etc.,
--   AH² = |b + c|² = |b|² + |c|² + 2 b·c,
--   a²  = |c − b|² = |b|² + |c|² − 2 b·c,
-- hence AH² + a² = 2(|b|² + |c|²), and the two equidistance relations
-- |b|² = |a|² = |c|² collapse this to AH² + a² = 4|a|² = 4R².
-- ============================================================

/-- **AH² = 4R² − a²** (squared-distance form).
    The squared distance from vertex `A` to the orthocenter `H` equals four times
    the squared circumradius minus the squared length of the *opposite* side `BC`. -/
theorem orthocenter_vertex_A_dist_sq (T : Triangle) :
    dist2_sq T.A T.orthocenter
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.B T.C := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination 2 * equidistB T + 2 * equidistC T

/-- **BH² = 4R² − b²** (squared-distance form). -/
theorem orthocenter_vertex_B_dist_sq (T : Triangle) :
    dist2_sq T.B T.orthocenter
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.C T.A := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination 2 * equidistC T

/-- **CH² = 4R² − c²** (squared-distance form). -/
theorem orthocenter_vertex_C_dist_sq (T : Triangle) :
    dist2_sq T.C T.orthocenter
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.A T.B := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination 2 * equidistB T

-- ============================================================
-- Part III: Classical (textbook) forms in terms of R and a, b, c
-- ============================================================

/-- **AH² = 4R² − a²** in textbook form (`R = circumradius`, `a = side_a`). -/
theorem orthocenter_vertex_A_dist_classical (T : Triangle) :
    dist2_sq T.A T.orthocenter = 4 * T.circumradius ^ 2 - T.side_a ^ 2 := by
  rw [show T.circumradius ^ 2 = dist2_sq T.circumcenter T.A from sq_dist2 _ _,
      show T.side_a ^ 2 = dist2_sq T.B T.C from sq_dist2 _ _]
  exact orthocenter_vertex_A_dist_sq T

/-- **BH² = 4R² − b²** in textbook form. -/
theorem orthocenter_vertex_B_dist_classical (T : Triangle) :
    dist2_sq T.B T.orthocenter = 4 * T.circumradius ^ 2 - T.side_b ^ 2 := by
  rw [show T.circumradius ^ 2 = dist2_sq T.circumcenter T.A from sq_dist2 _ _,
      show T.side_b ^ 2 = dist2_sq T.C T.A from sq_dist2 _ _]
  exact orthocenter_vertex_B_dist_sq T

/-- **CH² = 4R² − c²** in textbook form. -/
theorem orthocenter_vertex_C_dist_classical (T : Triangle) :
    dist2_sq T.C T.orthocenter = 4 * T.circumradius ^ 2 - T.side_c ^ 2 := by
  rw [show T.circumradius ^ 2 = dist2_sq T.circumcenter T.A from sq_dist2 _ _,
      show T.side_c ^ 2 = dist2_sq T.A T.B from sq_dist2 _ _]
  exact orthocenter_vertex_C_dist_sq T

-- ============================================================
-- Part IV: The sum and its link to Euler's metric identity
-- ============================================================

/-- **AH² + BH² + CH² = 12R² − (a² + b² + c²)** (squared-distance form).
    Summing the three vertex identities; the three `4R²` terms combine to `12R²`
    after the equidistance relations identify `|O−A|² = |O−B|² = |O−C|²`. -/
theorem orthocenter_vertex_sum_sq (T : Triangle) :
    dist2_sq T.A T.orthocenter + dist2_sq T.B T.orthocenter + dist2_sq T.C T.orthocenter
      = 12 * dist2_sq T.circumcenter T.A
        - (dist2_sq T.B T.C + dist2_sq T.C T.A + dist2_sq T.A T.B) := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination 4 * equidistB T + 4 * equidistC T

/-- **AH² + BH² + CH² = 12R² − (a² + b² + c²)** in textbook form. -/
theorem orthocenter_vertex_sum_classical (T : Triangle) :
    dist2_sq T.A T.orthocenter + dist2_sq T.B T.orthocenter + dist2_sq T.C T.orthocenter
      = 12 * T.circumradius ^ 2 - (T.side_a ^ 2 + T.side_b ^ 2 + T.side_c ^ 2) := by
  rw [show T.circumradius ^ 2 = dist2_sq T.circumcenter T.A from sq_dist2 _ _,
      show T.side_a ^ 2 = dist2_sq T.B T.C from sq_dist2 _ _,
      show T.side_b ^ 2 = dist2_sq T.C T.A from sq_dist2 _ _,
      show T.side_c ^ 2 = dist2_sq T.A T.B from sq_dist2 _ _]
  exact orthocenter_vertex_sum_sq T

/-- **AH² + BH² + CH² = OH² + 3R².**
    The sum of the squared vertex–orthocenter distances exceeds the squared
    circumcenter–orthocenter distance by exactly `3R²`.  Combined with Euler's
    identity `OH² = 9R² − (a²+b²+c²)` this reproves the sum identity above
    (`12R² − (a²+b²+c²) = (9R² − (a²+b²+c²)) + 3R²`). -/
theorem orthocenter_vertex_sum_eq_OH (T : Triangle) :
    dist2_sq T.A T.orthocenter + dist2_sq T.B T.orthocenter + dist2_sq T.C T.orthocenter
      = dist2_sq T.circumcenter T.orthocenter + 3 * dist2_sq T.circumcenter T.A := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination equidistB T + equidistC T

-- ============================================================
-- Part V: Consequence — a vertex is within the diameter of the orthocenter
-- ============================================================

/-- `AH² ≤ 4R²`: the distance from a vertex to the orthocenter never exceeds the
    diameter of the circumcircle (immediate from `AH² = 4R² − a²` and `a² ≥ 0`). -/
theorem orthocenter_vertex_le_diameter_sq (T : Triangle) :
    dist2_sq T.A T.orthocenter ≤ 4 * T.circumradius ^ 2 := by
  have h := orthocenter_vertex_A_dist_classical T
  have hnn : 0 ≤ T.side_a ^ 2 := sq_nonneg _
  linarith

-- ============================================================
-- Part VI: Worked example (3-4-5 right triangle)
--
-- A = (0,0) is the right-angle vertex and the orthocenter, so AH² = 0; the other
-- two vertices sit at the legs' ends.
-- ============================================================

/-- For the 3-4-5 right triangle, `AH² = 0` (the orthocenter is the right-angle
    vertex `A`), matching `4R² − a² = 4·(25/4) − 25 = 0`. -/
theorem triangle_345_AH_sq :
    dist2_sq triangle_345.A triangle_345.orthocenter = 0 := by
  rw [triangle_345_orthocenter]
  simp only [dist2_sq, triangle_345]
  norm_num

/-- The 3-4-5 triangle satisfies `AH² = 4R² − a²` numerically (`0 = 25 − 25`). -/
theorem triangle_345_vertex_A_metric :
    dist2_sq triangle_345.A triangle_345.orthocenter
      = 4 * triangle_345.circumradius ^ 2 - triangle_345.side_a ^ 2 := by
  rw [triangle_345_AH_sq, triangle_345_circumradius, triangle_345_side_a]
  norm_num

/-- The 3-4-5 vertex–orthocenter sum: `0 + 9 + 16 = 25 = 12R² − (a²+b²+c²)`. -/
theorem triangle_345_vertex_sum :
    dist2_sq triangle_345.A triangle_345.orthocenter
        + dist2_sq triangle_345.B triangle_345.orthocenter
        + dist2_sq triangle_345.C triangle_345.orthocenter
      = 12 * triangle_345.circumradius ^ 2
        - (triangle_345.side_a ^ 2 + triangle_345.side_b ^ 2 + triangle_345.side_c ^ 2) := by
  rw [triangle_345_circumradius, triangle_345_side_a, triangle_345_side_b, triangle_345_side_c,
      triangle_345_orthocenter]
  simp only [dist2_sq, triangle_345]
  norm_num

end FeuerbachsTheoremDefsOQ01OQ01OQ01OQ02
