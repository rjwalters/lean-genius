/-
  Feuerbach's Theorem DefsOQ01OQ01OQ01OQ02OQ01: A Vertex–Orthocenter segment is
  twice the Circumcenter–Opposite-Midpoint segment — AH = 2·OM_a

  ## The Open Question

  The parent file `FeuerbachsTheoremDefsOQ01OQ01OQ01OQ02` proved the metric
  identity for the distance from a vertex to the orthocenter,

      AH² = 4R² − a²,   BH² = 4R² − b²,   CH² = 4R² − c².

  A classical companion expresses the *same* quantity geometrically: the distance
  from a vertex to the orthocenter equals **twice** the distance from the
  circumcenter `O` to the midpoint `M_a` of the opposite side `BC`:

      AH = 2·OM_a,   BH = 2·OM_b,   CH = 2·OM_c.

  Indeed `OM_a = R·cos A` (`O` projects orthogonally onto `BC` at `M_a`, and the
  right triangle `O M_a B` gives `OM_a² = R² − (a/2)²`), so `2·OM_a = 2R·cos A = AH`.

  ## What This File Proves

  ### The exact vector identity (no circle hypothesis needed)
  `vertexA_orthocenter_vec` :  `A − H = 2·(O − M_a)`  (componentwise).

  Substituting `H = A + B + C − 2O` and `M_a = (B + C)/2` makes both sides equal
  to `2O − B − C` — a *purely affine* identity, independent of the circumcenter's
  equidistance property.  In particular the segment `HA` is parallel to `OM_a`.

  ### Squared-length consequence (still no circle hypothesis)
  `orthocenter_vertexA_eq_four_OMa_sq` :  `AH² = 4·OM_a²`,
  immediate by squaring the vector identity.

  ### The circumcenter–midpoint distance (uses equidistance)
  `circumcenter_midpoint_a_sq` :  `4·OM_a² = 4R² − a²`,  i.e. `OM_a² = R² − (a/2)²`.
  Here `M_a` lies on the perpendicular bisector of `BC`, so the two equidistance
  relations `|B−O|² = |A−O|²`, `|C−O|² = |A−O|²` collapse `4·OM_a²` to `4R² − a²`.

  ### Putting them together
  `orthocenter_vertexA_eq_four_OMa_classical` re-derives `AH² = 4R² − a²` from the
  two pieces above (a cross-check of the parent, proved here independently), and
  `orthocenter_vertexA_dist_eq_two_OMa` gives the textbook **`AH = 2·OM_a`** as an
  identity of actual (square-root) distances.

  ### Perpendicularity of the altitude
  `altitude_A_perp_BC` :  `(A − H) · (C − B) = 0`.  Because `A − H ∥ O − M_a` and
  `O` is equidistant from `B`, `C`, the line `HA` is perpendicular to `BC`; this
  recovers the defining property of the altitude through `A`.

  ### The sum identity
  `circumcenter_midpoint_sum_sq` :
      `4·(OM_a² + OM_b² + OM_c²) = 12R² − (a² + b² + c²)`,
  so `OM_a² + OM_b² + OM_c² = ¼(AH² + BH² + CH²)`.

  ### Worked example (3-4-5 right triangle)
  `O = (3/2, 2)`, `M_a = (3/2, 2)` so `OM_a = 0 = AH/2` (the orthocenter is the
  right-angle vertex `A`), while `OM_b² = 9/4` (`BH = 3 = 2·OM_b`) and
  `OM_c² = 4` (`CH = 4 = 2·OM_c`).

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01OQ01OQ02OQ01

open FeuerbachsTheorem

-- ============================================================
-- Part 0: Pairwise equidistance of the circumcenter
--
-- The parent declares the equidistance facts `private`; we reprove the three we
-- need (A–B, A–C, and the derived B–C) so this file builds independently.  Each
-- follows from the perpendicular-bisector identity, which is *linear* in O.
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
-- Part II: The exact vector identity  A − H = 2·(O − M_a)
--
-- With H = A + B + C − 2O and M_a = (B + C)/2 both sides equal 2O − B − C.
-- This is purely affine — it needs no equidistance / circle hypothesis.
-- ============================================================

/-- **`A − H = 2·(O − M_a)`** (componentwise).  The directed segment from the
    orthocenter to vertex `A` is exactly twice the directed segment from the
    midpoint `M_a` of `BC` to the circumcenter `O`; in particular `HA ∥ OM_a`. -/
theorem vertexA_orthocenter_vec (T : Triangle) :
    (T.A.1 - T.orthocenter.1, T.A.2 - T.orthocenter.2)
      = (2 * (T.circumcenter.1 - T.midpoint_a.1),
         2 * (T.circumcenter.2 - T.midpoint_a.2)) := by
  unfold Triangle.orthocenter Triangle.midpoint_a pointMidpoint
  exact Prod.ext (by dsimp; ring) (by dsimp; ring)

/-- **`B − H = 2·(O − M_b)`** (componentwise). -/
theorem vertexB_orthocenter_vec (T : Triangle) :
    (T.B.1 - T.orthocenter.1, T.B.2 - T.orthocenter.2)
      = (2 * (T.circumcenter.1 - T.midpoint_b.1),
         2 * (T.circumcenter.2 - T.midpoint_b.2)) := by
  unfold Triangle.orthocenter Triangle.midpoint_b pointMidpoint
  exact Prod.ext (by dsimp; ring) (by dsimp; ring)

/-- **`C − H = 2·(O − M_c)`** (componentwise). -/
theorem vertexC_orthocenter_vec (T : Triangle) :
    (T.C.1 - T.orthocenter.1, T.C.2 - T.orthocenter.2)
      = (2 * (T.circumcenter.1 - T.midpoint_c.1),
         2 * (T.circumcenter.2 - T.midpoint_c.2)) := by
  unfold Triangle.orthocenter Triangle.midpoint_c pointMidpoint
  exact Prod.ext (by dsimp; ring) (by dsimp; ring)

-- ============================================================
-- Part III: Squared lengths  AH² = 4·OM_a²  (still circle-free)
--
-- Squaring the vector identity; a pure `ring` identity in the coordinates.
-- ============================================================

/-- **`AH² = 4·OM_a²`**: the squared vertex–orthocenter distance is four times the
    squared circumcenter–midpoint distance.  Immediate from the vector identity. -/
theorem orthocenter_vertexA_eq_four_OMa_sq (T : Triangle) :
    dist2_sq T.A T.orthocenter = 4 * dist2_sq T.circumcenter T.midpoint_a := by
  simp only [dist2_sq, Triangle.orthocenter, Triangle.midpoint_a, pointMidpoint]
  ring

/-- **`BH² = 4·OM_b²`**. -/
theorem orthocenter_vertexB_eq_four_OMb_sq (T : Triangle) :
    dist2_sq T.B T.orthocenter = 4 * dist2_sq T.circumcenter T.midpoint_b := by
  simp only [dist2_sq, Triangle.orthocenter, Triangle.midpoint_b, pointMidpoint]
  ring

/-- **`CH² = 4·OM_c²`**. -/
theorem orthocenter_vertexC_eq_four_OMc_sq (T : Triangle) :
    dist2_sq T.C T.orthocenter = 4 * dist2_sq T.circumcenter T.midpoint_c := by
  simp only [dist2_sq, Triangle.orthocenter, Triangle.midpoint_c, pointMidpoint]
  ring

-- ============================================================
-- Part IV: The circumcenter–midpoint distance  4·OM_a² = 4R² − a²
--
-- M_a is on the perpendicular bisector of BC, so the two equidistance relations
-- |b|² = |a|² = |c|² (O-centered) collapse 4·OM_a² = |b + c|² to 4R² − a².
-- ============================================================

/-- **`4·OM_a² = 4R² − a²`**, i.e. `OM_a² = R² − (a/2)²` (squared-distance form).
    The squared circumcenter–to–`BC`-midpoint distance is `R² − (a/2)²`. -/
theorem circumcenter_midpoint_a_sq (T : Triangle) :
    4 * dist2_sq T.circumcenter T.midpoint_a
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.B T.C := by
  simp only [dist2_sq, Triangle.midpoint_a, pointMidpoint]
  linear_combination 2 * equidistB T + 2 * equidistC T

/-- **`4·OM_b² = 4R² − b²`**. -/
theorem circumcenter_midpoint_b_sq (T : Triangle) :
    4 * dist2_sq T.circumcenter T.midpoint_b
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.C T.A := by
  simp only [dist2_sq, Triangle.midpoint_b, pointMidpoint]
  linear_combination 2 * equidistC T

/-- **`4·OM_c² = 4R² − c²`**. -/
theorem circumcenter_midpoint_c_sq (T : Triangle) :
    4 * dist2_sq T.circumcenter T.midpoint_c
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.A T.B := by
  simp only [dist2_sq, Triangle.midpoint_c, pointMidpoint]
  linear_combination 2 * equidistB T

/-- **`OM_a² = R² − (a/2)²`** in textbook form (`R = circumradius`, `a = side_a`). -/
theorem circumcenter_midpoint_a_classical (T : Triangle) :
    dist2_sq T.circumcenter T.midpoint_a
      = T.circumradius ^ 2 - (T.side_a / 2) ^ 2 := by
  have h := circumcenter_midpoint_a_sq T
  have hR : T.circumradius ^ 2 = dist2_sq T.circumcenter T.A := sq_dist2 _ _
  have ha : T.side_a ^ 2 = dist2_sq T.B T.C := sq_dist2 _ _
  have hhalf : (T.side_a / 2) ^ 2 = dist2_sq T.B T.C / 4 := by rw [div_pow, ha]; norm_num
  rw [hR, hhalf]
  linarith [h]

-- ============================================================
-- Part V: Putting them together — AH² = 4R² − a² and AH = 2·OM_a
-- ============================================================

/-- **`AH² = 4R² − a²`** (squared-distance form), re-derived here from the vector
    identity (`AH² = 4·OM_a²`) and the circumcenter–midpoint distance
    (`4·OM_a² = 4R² − a²`).  An independent cross-check of the parent result. -/
theorem orthocenter_vertexA_eq_four_OMa_classical (T : Triangle) :
    dist2_sq T.A T.orthocenter
      = 4 * dist2_sq T.circumcenter T.A - dist2_sq T.B T.C := by
  rw [orthocenter_vertexA_eq_four_OMa_sq T, circumcenter_midpoint_a_sq T]

/-- **`AH = 2·OM_a`** (true distances): the vertex–orthocenter distance equals
    twice the circumcenter–opposite-midpoint distance.  From `AH² = 4·OM_a²` with
    both distances non-negative. -/
theorem orthocenter_vertexA_dist_eq_two_OMa (T : Triangle) :
    dist2 T.A T.orthocenter = 2 * dist2 T.circumcenter T.midpoint_a := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _)
    (mul_nonneg (by norm_num) (dist2_nonneg _ _))
  rw [mul_pow, sq_dist2, sq_dist2]
  have h := orthocenter_vertexA_eq_four_OMa_sq T
  linarith [h]

/-- **`BH = 2·OM_b`** (true distances). -/
theorem orthocenter_vertexB_dist_eq_two_OMb (T : Triangle) :
    dist2 T.B T.orthocenter = 2 * dist2 T.circumcenter T.midpoint_b := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _)
    (mul_nonneg (by norm_num) (dist2_nonneg _ _))
  rw [mul_pow, sq_dist2, sq_dist2]
  have h := orthocenter_vertexB_eq_four_OMb_sq T
  linarith [h]

/-- **`CH = 2·OM_c`** (true distances). -/
theorem orthocenter_vertexC_dist_eq_two_OMc (T : Triangle) :
    dist2 T.C T.orthocenter = 2 * dist2 T.circumcenter T.midpoint_c := by
  apply eq_of_sq_eq_of_nonneg (dist2_nonneg _ _)
    (mul_nonneg (by norm_num) (dist2_nonneg _ _))
  rw [mul_pow, sq_dist2, sq_dist2]
  have h := orthocenter_vertexC_eq_four_OMc_sq T
  linarith [h]

-- ============================================================
-- Part VI: Perpendicularity of the altitude
--
-- A − H ∥ O − M_a, and O − M_a ⊥ BC (perp bisector), so HA ⊥ BC.  The dot
-- product (A − H)·(C − B) collapses to |B − O|² − |C − O|² = equidistB − equidistC.
-- ============================================================

/-- **`(A − H) · (C − B) = 0`**: the segment `HA` is perpendicular to `BC`.
    Recovers the defining property of the altitude through `A` from the parallel
    segment `OM_a` (which bisects `BC` perpendicularly). -/
theorem altitude_A_perp_BC (T : Triangle) :
    (T.A.1 - T.orthocenter.1) * (T.C.1 - T.B.1)
      + (T.A.2 - T.orthocenter.2) * (T.C.2 - T.B.2) = 0 := by
  simp only [Triangle.orthocenter]
  linear_combination equidistB T - equidistC T

-- ============================================================
-- Part VII: The sum identity
-- ============================================================

/-- **`4·(OM_a² + OM_b² + OM_c²) = 12R² − (a² + b² + c²)`**, hence
    `OM_a² + OM_b² + OM_c² = ¼(AH² + BH² + CH²)`.  Summing the three
    circumcenter–midpoint identities. -/
theorem circumcenter_midpoint_sum_sq (T : Triangle) :
    4 * (dist2_sq T.circumcenter T.midpoint_a
          + dist2_sq T.circumcenter T.midpoint_b
          + dist2_sq T.circumcenter T.midpoint_c)
      = 12 * dist2_sq T.circumcenter T.A
        - (dist2_sq T.B T.C + dist2_sq T.C T.A + dist2_sq T.A T.B) := by
  have ha := circumcenter_midpoint_a_sq T
  have hb := circumcenter_midpoint_b_sq T
  have hc := circumcenter_midpoint_c_sq T
  linarith [ha, hb, hc]

-- ============================================================
-- Part VIII: Worked example (3-4-5 right triangle)
--
-- O = (3/2, 2), M_a = midpoint(B,C) = (3/2, 2) = O so OM_a = 0 = AH/2;
-- M_b = (0, 2) gives OM_b² = 9/4 (BH = 3 = 2·OM_b),
-- M_c = (3/2, 0) gives OM_c² = 4   (CH = 4 = 2·OM_c).
-- ============================================================

/-- For the 3-4-5 triangle, `OM_a² = 0` (the circumcenter is the hypotenuse
    midpoint `M_a`), matching `AH² = 0 = 4·OM_a²`. -/
theorem triangle_345_OMa_sq :
    dist2_sq triangle_345.circumcenter triangle_345.midpoint_a = 0 := by
  rw [triangle_345_circumcenter]
  simp only [dist2_sq, Triangle.midpoint_a, pointMidpoint, triangle_345]
  norm_num

/-- For the 3-4-5 triangle, `OM_b² = 9/4`, so `2·OM_b = 3 = BH`. -/
theorem triangle_345_OMb_sq :
    dist2_sq triangle_345.circumcenter triangle_345.midpoint_b = 9 / 4 := by
  rw [triangle_345_circumcenter]
  simp only [dist2_sq, Triangle.midpoint_b, pointMidpoint, triangle_345]
  norm_num

/-- For the 3-4-5 triangle, `OM_c² = 4`, so `2·OM_c = 4 = CH`. -/
theorem triangle_345_OMc_sq :
    dist2_sq triangle_345.circumcenter triangle_345.midpoint_c = 4 := by
  rw [triangle_345_circumcenter]
  simp only [dist2_sq, Triangle.midpoint_c, pointMidpoint, triangle_345]
  norm_num

/-- The 3-4-5 triangle satisfies `BH² = 4·OM_b²` numerically (`9 = 4·(9/4)`). -/
theorem triangle_345_vertexB_eq_four_OMb :
    dist2_sq triangle_345.B triangle_345.orthocenter
      = 4 * dist2_sq triangle_345.circumcenter triangle_345.midpoint_b := by
  rw [orthocenter_vertexB_eq_four_OMb_sq, triangle_345_OMb_sq]

end FeuerbachsTheoremDefsOQ01OQ01OQ01OQ02OQ01
