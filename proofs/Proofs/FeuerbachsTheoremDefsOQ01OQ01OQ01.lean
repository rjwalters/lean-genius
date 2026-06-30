/-
  Feuerbach's Theorem DefsOQ01OQ01OQ01: Reflections of the Orthocenter Lie on
  the Circumcircle

  ## The Open Question

  The sibling `FeuerbachsTheoremDefsOQ01OQ01` proved the *concurrency* of the
  three altitudes at the orthocenter `H = A + B + C - 2·O` (O the circumcenter).
  Its first open question asks to verify the classical companion fact that

    the reflection of the orthocenter across each side of the triangle
    lies on the circumcircle,

  a hallmark of the orthocentric configuration that the nine-point-circle
  development never establishes.

  ## What This File Proves

  ### Reflection over a side line
  For a point `H` and a line through `P` with direction `Q - P`, `reflectOverLine`
  is the mirror image of `H` across that line.  Writing `H'` for the reflection of
  the orthocenter across a side, the headline theorems are

  `reflectOrthoBC_on_circumcircle` : `dist(O, H'_BC) = R`
  `reflectOrthoCA_on_circumcircle` : `dist(O, H'_CA) = R`
  `reflectOrthoAB_on_circumcircle` : `dist(O, H'_AB) = R`

  where `R = circumradius`.  Each reflected orthocenter is at distance `R` from the
  circumcenter, hence on the circumcircle; `orthocenter_reflections_concyclic`
  bundles all three.

  The proof reduces, after clearing the projection denominator, to a single
  polynomial identity in the vertex/circumcenter coordinates that holds modulo the
  two equidistance relations `|B - O|² = |A - O|²` and `|C - O|² = |A - O|²`
  (the `reflect_core` lemma, discharged by an explicit `linear_combination`).

  ### Reflection over a side midpoint (antipode)
  `reflectOrthoMidBC_eq_antipode` : the reflection of `H` across the midpoint of
  `BC` is the point `2·O - A`, the antipode of `A` on the circumcircle; hence
  `reflectOrthoMidBC_on_circumcircle` places it on the circumcircle as well.

  ### Worked example
  `triangle_345_reflectOrthoMidBC` : for the 3-4-5 right triangle the reflection of
  the orthocenter (= `A = (0,0)`) over the midpoint of `BC` is `(3, 4)`, the
  antipode of `A` on the circumcircle of radius `5/2` centred at `(3/2, 2)`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01OQ01

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
-- Part I: Reflection of a point over a line
-- ============================================================

/-- The reflection of point `H` over the line through `P` with direction `Q - P`.
    With `t` the projection parameter of `H` onto the line, the foot is
    `P + t·(Q - P)` and the reflection is `2·foot - H`. -/
def reflectOverLine (H P Q : Point) : Point :=
  let dx := Q.1 - P.1
  let dy := Q.2 - P.2
  let dd := dx ^ 2 + dy ^ 2
  let t := ((H.1 - P.1) * dx + (H.2 - P.2) * dy) / dd
  (2 * P.1 + 2 * t * dx - H.1, 2 * P.2 + 2 * t * dy - H.2)

-- ============================================================
-- Part II: The core polynomial identity
--
-- After clearing the projection denominator `dd = |Q - P|²`, the squared distance
-- from O to the reflected orthocenter (numerator `N1² + N2²`) equals `|V - O|²·dd²`
-- modulo the two equidistance relations, where V is the vertex opposite the line.
-- The cofactors are explicit (found by ideal membership over the equidistance
-- generators); `linear_combination` discharges the identity by `ring`.
-- ============================================================

set_option maxHeartbeats 25600000 in
private lemma reflect_core (ox oy vx vy px py qx qy : ℝ)
    (hP : (px - ox) ^ 2 + (py - oy) ^ 2 = (vx - ox) ^ 2 + (vy - oy) ^ 2)
    (hQ : (qx - ox) ^ 2 + (qy - oy) ^ 2 = (vx - ox) ^ 2 + (vy - oy) ^ 2) :
    (-3*ox*px^2 + 6*ox*px*qx + ox*py^2 - 2*ox*py*qy - 3*ox*qx^2 + ox*qy^2 - 4*oy*px*py + 4*oy*px*qy + 4*oy*py*qx - 4*oy*qx*qy + px^3 - px^2*qx + px^2*vx + px*py^2 + 2*px*py*vy - px*qx^2 - 2*px*qx*vx - px*qy^2 - 2*px*qy*vy - py^2*qx - py^2*vx - 2*py*qx*vy + 2*py*qy*vx + qx^3 + qx^2*vx + qx*qy^2 + 2*qx*qy*vy - qy^2*vx) ^ 2 + (-4*ox*px*py + 4*ox*px*qy + 4*ox*py*qx - 4*ox*qx*qy + oy*px^2 - 2*oy*px*qx - 3*oy*py^2 + 6*oy*py*qy + oy*qx^2 - 3*oy*qy^2 + px^2*py - px^2*qy - px^2*vy + 2*px*py*vx + 2*px*qx*vy - 2*px*qy*vx + py^3 - py^2*qy + py^2*vy - py*qx^2 - 2*py*qx*vx - py*qy^2 - 2*py*qy*vy + qx^2*qy - qx^2*vy + 2*qx*qy*vx + qy^3 + qy^2*vy) ^ 2
      = ((vx - ox) ^ 2 + (vy - oy) ^ 2) * ((qx - px) ^ 2 + (qy - py) ^ 2) ^ 2 := by
  linear_combination (-4*ox^2*px*qx + 4*ox^2*px*vx + 8*ox^2*qx^2 - 12*ox^2*qx*vx + 4*ox^2*vx^2 - 8*ox*oy^2*qx + 8*ox*oy^2*vx - 4*ox*oy*px*qy + 4*ox*oy*px*vy - 4*ox*oy*py*qx + 4*ox*oy*py*vx + 24*ox*oy*qx*qy - 4*ox*oy*qx*vy - 20*ox*oy*qy*vx - 4*ox*px^3 + 14*ox*px^2*qx - 2*ox*px^2*vx - 4*ox*px*py^2 + 8*ox*px*py*qy - 14*ox*px*qx^2 + 8*ox*px*qx*vx - 2*ox*px*qy^2 - 6*ox*px*vx^2 - 2*ox*px*vy^2 + 6*ox*py^2*qx - 2*ox*py^2*vx - 12*ox*py*qx*qy + 4*ox*py*qx*vy + 4*ox*py*qy*vx - 4*ox*py*vx*vy - 2*ox*qx^2*vx - 12*ox*qx*qy*vy + 10*ox*qx*vx^2 + 6*ox*qx*vy^2 + 2*ox*qy^2*vx + 12*ox*qy*vx*vy - 4*ox*vx^3 - 4*ox*vx*vy^2 - 8*oy^3*qy + 8*oy^3*vy - 4*oy^2*py*qy + 4*oy^2*py*vy + 4*oy^2*qx^2 + 20*oy^2*qy^2 - 12*oy^2*qy*vy - 4*oy^2*vx^2 - 8*oy^2*vy^2 - 4*oy*px^2*py + 6*oy*px^2*qy - 2*oy*px^2*vy + 8*oy*px*py*qx - 12*oy*px*qx*qy + 4*oy*px*qx*vy + 4*oy*px*qy*vx - 4*oy*px*vx*vy - 4*oy*py^3 + 14*oy*py^2*qy - 2*oy*py^2*vy - 2*oy*py*qx^2 - 14*oy*py*qy^2 + 8*oy*py*qy*vy - 2*oy*py*vx^2 - 6*oy*py*vy^2 - 4*oy*qx^2*qy - 2*oy*qx^2*vy - 4*oy*qx*qy*vx + 4*oy*qx*vx*vy - 4*oy*qy^3 - 14*oy*qy^2*vy + 10*oy*qy*vx^2 + 22*oy*qy*vy^2 + px^4 - 2*px^3*qx + 2*px^3*vx + 2*px^2*py^2 - 2*px^2*py*qy + 2*px^2*py*vy - px^2*qx^2 - 6*px^2*qx*vx - px^2*qy^2 - 2*px^2*qy*vy + px^2*vx^2 + px^2*vy^2 - 2*px*py^2*qx + 2*px*py^2*vx - 4*px*py*qx*vy - 4*px*py*qy*vx + 4*px*qx^3 + 4*px*qx^2*vx + 4*px*qx*qy^2 + 4*px*qx*qy*vy - 2*px*qx*vx^2 - 2*px*qx*vy^2 + 2*px*vx^3 + 2*px*vx*vy^2 + py^4 - 2*py^3*qy + 2*py^3*vy - py^2*qx^2 - 2*py^2*qx*vx - py^2*qy^2 - 6*py^2*qy*vy + py^2*vx^2 + py^2*vy^2 + 4*py*qx^2*qy + 4*py*qx*qy*vx + 4*py*qy^3 + 4*py*qy^2*vy - 2*py*qy*vx^2 - 2*py*qy*vy^2 + 2*py*vx^2*vy + 2*py*vy^3 - qx^4 - 2*qx^2*qy^2 + 4*qx^2*qy*vy - qx^2*vx^2 - qx^2*vy^2 - 2*qx*vx^3 - 2*qx*vx*vy^2 - qy^4 + 4*qy^3*vy - qy^2*vx^2 - qy^2*vy^2 - 6*qy*vx^2*vy - 6*qy*vy^3 + vx^4 + 2*vx^2*vy^2 + vy^4) * hP + (4*ox^2*px^2 - 8*ox^2*px*qx + 8*ox^2*qx*vx - 4*ox^2*vx^2 + 8*ox*oy^2*px - 8*ox*oy^2*vx + 8*ox*oy*px*py - 16*ox*oy*px*qy - 8*ox*oy*px*vy - 8*ox*oy*py*qx + 8*ox*oy*qx*vy + 16*ox*oy*qy*vx - 4*ox*px^2*qx - 4*ox*px^2*vx - 4*ox*px*py*qy - 4*ox*px*py*vy + 12*ox*px*qx^2 + 4*ox*px*qy^2 + 12*ox*px*qy*vy + 4*ox*px*vx^2 + 8*ox*py*qx*qy - 4*ox*py*qy*vx + 4*ox*py*vx*vy - 4*ox*qx^3 - 4*ox*qx*qy^2 - 8*ox*qx*vx^2 - 4*ox*qx*vy^2 - 12*ox*qy*vx*vy + 4*ox*vx^3 + 4*ox*vx*vy^2 + 8*oy^3*py - 8*oy^3*vy - 4*oy^2*px^2 - 16*oy^2*py*qy - 8*oy^2*py*vy + 16*oy^2*qy*vy + 4*oy^2*vx^2 + 8*oy^2*vy^2 + 4*oy*px^2*qy + 4*oy*px^2*vy - 4*oy*px*py*qx - 4*oy*px*py*vx + 8*oy*px*qx*qy - 4*oy*px*qx*vy + 4*oy*px*vx*vy + 4*oy*py*qx^2 + 4*oy*py*qx*vx + 12*oy*py*qy^2 + 8*oy*py*qy*vy + 4*oy*py*vy^2 - 4*oy*qx^2*qy - 4*oy*qx*vx*vy - 4*oy*qy^3 - 8*oy*qy*vx^2 - 20*oy*qy*vy^2 + 4*px^2*qx*vx - 4*px^2*qy*vy + 4*px*py*qx*vy + 4*px*py*qy*vx - 2*px*qx^3 - 6*px*qx^2*vx - 2*px*qx*qy^2 - 4*px*qx*qy*vy + 2*px*qx*vx^2 + 2*px*qx*vy^2 - 2*px*qy^2*vx - 2*px*vx^3 - 2*px*vx*vy^2 - 2*py*qx^2*qy - 2*py*qx^2*vy - 4*py*qx*qy*vx - 2*py*qy^3 - 6*py*qy^2*vy + 2*py*qy*vx^2 + 2*py*qy*vy^2 - 2*py*vx^2*vy - 2*py*vy^3 + qx^4 + 2*qx^3*vx + 2*qx^2*qy^2 + 2*qx^2*qy*vy + 2*qx*qy^2*vx + 2*qx*vx^3 + 2*qx*vx*vy^2 + qy^4 + 2*qy^3*vy + 6*qy*vx^2*vy + 6*qy*vy^3 - vx^4 - 2*vx^2*vy^2 - vy^4) * hQ

-- ============================================================
-- Part III: Generic distance lemma for the reflected orthocenter
-- ============================================================

set_option maxHeartbeats 25600000 in
/-- If `H = V + P + Q - 2·O` (the orthocenter, with `V` the vertex opposite the
    side `PQ`) and `O` is equidistant from `V, P, Q`, then the reflection of `H`
    over line `PQ` is at distance `|V - O|` from `O`: it lies on the circumcircle. -/
lemma reflectOverLine_orthocenter_dist_sq
    (ox oy vx vy px py qx qy hx hy : ℝ)
    (hHx : hx = vx + px + qx - 2 * ox) (hHy : hy = vy + py + qy - 2 * oy)
    (hP : (px - ox) ^ 2 + (py - oy) ^ 2 = (vx - ox) ^ 2 + (vy - oy) ^ 2)
    (hQ : (qx - ox) ^ 2 + (qy - oy) ^ 2 = (vx - ox) ^ 2 + (vy - oy) ^ 2)
    (hdd : (qx - px) ^ 2 + (qy - py) ^ 2 ≠ 0) :
    dist2_sq (ox, oy) (reflectOverLine (hx, hy) (px, py) (qx, qy))
      = dist2_sq (ox, oy) (vx, vy) := by
  subst hHx hHy
  have hcore := reflect_core ox oy vx vy px py qx qy hP hQ
  have hdd2 : ((qx - px) ^ 2 + (qy - py) ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hdd
  rw [show dist2_sq (ox, oy) (vx, vy) = (vx - ox) ^ 2 + (vy - oy) ^ 2 from rfl]
  have expand : dist2_sq (ox, oy)
        (reflectOverLine (vx + px + qx - 2 * ox, vy + py + qy - 2 * oy) (px, py) (qx, qy))
      = ((-3*ox*px^2 + 6*ox*px*qx + ox*py^2 - 2*ox*py*qy - 3*ox*qx^2 + ox*qy^2 - 4*oy*px*py + 4*oy*px*qy + 4*oy*py*qx - 4*oy*qx*qy + px^3 - px^2*qx + px^2*vx + px*py^2 + 2*px*py*vy - px*qx^2 - 2*px*qx*vx - px*qy^2 - 2*px*qy*vy - py^2*qx - py^2*vx - 2*py*qx*vy + 2*py*qy*vx + qx^3 + qx^2*vx + qx*qy^2 + 2*qx*qy*vy - qy^2*vx) ^ 2 + (-4*ox*px*py + 4*ox*px*qy + 4*ox*py*qx - 4*ox*qx*qy + oy*px^2 - 2*oy*px*qx - 3*oy*py^2 + 6*oy*py*qy + oy*qx^2 - 3*oy*qy^2 + px^2*py - px^2*qy - px^2*vy + 2*px*py*vx + 2*px*qx*vy - 2*px*qy*vx + py^3 - py^2*qy + py^2*vy - py*qx^2 - 2*py*qx*vx - py*qy^2 - 2*py*qy*vy + qx^2*qy - qx^2*vy + 2*qx*qy*vx + qy^3 + qy^2*vy) ^ 2) / ((qx - px) ^ 2 + (qy - py) ^ 2) ^ 2 := by
    unfold dist2_sq reflectOverLine
    simp only []
    field_simp
    ring
  rw [expand, div_eq_iff hdd2]
  linear_combination hcore

-- ============================================================
-- Part IV: The three side reflections
-- ============================================================

/-- Reflection of the orthocenter across side `BC`. -/
def reflectOrthoBC (T : Triangle) : Point := reflectOverLine T.orthocenter T.B T.C

/-- Reflection of the orthocenter across side `CA`. -/
def reflectOrthoCA (T : Triangle) : Point := reflectOverLine T.orthocenter T.C T.A

/-- Reflection of the orthocenter across side `AB`. -/
def reflectOrthoAB (T : Triangle) : Point := reflectOverLine T.orthocenter T.A T.B

theorem reflectOrthoBC_dist_sq (T : Triangle) :
    dist2_sq T.circumcenter (reflectOrthoBC T) = dist2_sq T.circumcenter T.A := by
  unfold reflectOrthoBC
  exact reflectOverLine_orthocenter_dist_sq T.circumcenter.1 T.circumcenter.2
    T.A.1 T.A.2 T.B.1 T.B.2 T.C.1 T.C.2 T.orthocenter.1 T.orthocenter.2
    (by unfold Triangle.orthocenter; ring) (by unfold Triangle.orthocenter; ring)
    (equidistB T) (equidistC T) (bc_sq_ne_zero T)

theorem reflectOrthoCA_dist_sq (T : Triangle) :
    dist2_sq T.circumcenter (reflectOrthoCA T) = dist2_sq T.circumcenter T.B := by
  unfold reflectOrthoCA
  exact reflectOverLine_orthocenter_dist_sq T.circumcenter.1 T.circumcenter.2
    T.B.1 T.B.2 T.C.1 T.C.2 T.A.1 T.A.2 T.orthocenter.1 T.orthocenter.2
    (by unfold Triangle.orthocenter; ring) (by unfold Triangle.orthocenter; ring)
    ((equidistC T).trans (equidistB T).symm) (equidistB T).symm (ca_sq_ne_zero T)

theorem reflectOrthoAB_dist_sq (T : Triangle) :
    dist2_sq T.circumcenter (reflectOrthoAB T) = dist2_sq T.circumcenter T.C := by
  unfold reflectOrthoAB
  exact reflectOverLine_orthocenter_dist_sq T.circumcenter.1 T.circumcenter.2
    T.C.1 T.C.2 T.A.1 T.A.2 T.B.1 T.B.2 T.orthocenter.1 T.orthocenter.2
    (by unfold Triangle.orthocenter; ring) (by unfold Triangle.orthocenter; ring)
    ((equidistC T).symm) ((equidistB T).trans (equidistC T).symm) (ab_sq_ne_zero T)

-- ============================================================
-- Part V: On the circumcircle (distance = circumradius)
-- ============================================================

/-- The reflection of the orthocenter across `BC` lies on the circumcircle. -/
theorem reflectOrthoBC_on_circumcircle (T : Triangle) :
    dist2 T.circumcenter (reflectOrthoBC T) = T.circumradius := by
  unfold Triangle.circumradius dist2
  congr 1
  exact reflectOrthoBC_dist_sq T

/-- The reflection of the orthocenter across `CA` lies on the circumcircle. -/
theorem reflectOrthoCA_on_circumcircle (T : Triangle) :
    dist2 T.circumcenter (reflectOrthoCA T) = T.circumradius := by
  unfold Triangle.circumradius dist2
  congr 1
  show dist2_sq T.circumcenter (reflectOrthoCA T) = dist2_sq T.circumcenter T.A
  rw [reflectOrthoCA_dist_sq T]
  exact equidistB T

/-- The reflection of the orthocenter across `AB` lies on the circumcircle. -/
theorem reflectOrthoAB_on_circumcircle (T : Triangle) :
    dist2 T.circumcenter (reflectOrthoAB T) = T.circumradius := by
  unfold Triangle.circumradius dist2
  congr 1
  show dist2_sq T.circumcenter (reflectOrthoAB T) = dist2_sq T.circumcenter T.A
  rw [reflectOrthoAB_dist_sq T]
  exact equidistC T

/-- **The reflections of the orthocenter across the three sides are concyclic**,
    all lying on the circumcircle. -/
theorem orthocenter_reflections_concyclic (T : Triangle) :
    dist2 T.circumcenter (reflectOrthoBC T) = T.circumradius ∧
    dist2 T.circumcenter (reflectOrthoCA T) = T.circumradius ∧
    dist2 T.circumcenter (reflectOrthoAB T) = T.circumradius :=
  ⟨reflectOrthoBC_on_circumcircle T, reflectOrthoCA_on_circumcircle T,
   reflectOrthoAB_on_circumcircle T⟩

-- ============================================================
-- Part VI: Reflection over a side midpoint is the antipode
-- ============================================================

/-- Reflection of the orthocenter across the midpoint of `BC`
    (`= 2·midpoint(BC) - H = (B + C) - H`). -/
def reflectOrthoMidBC (T : Triangle) : Point :=
  (T.B.1 + T.C.1 - T.orthocenter.1, T.B.2 + T.C.2 - T.orthocenter.2)

/-- The reflection of the orthocenter across the midpoint of `BC` is `2·O - A`,
    the antipode of `A` on the circumcircle. -/
theorem reflectOrthoMidBC_eq_antipode (T : Triangle) :
    reflectOrthoMidBC T
      = (2 * T.circumcenter.1 - T.A.1, 2 * T.circumcenter.2 - T.A.2) := by
  unfold reflectOrthoMidBC Triangle.orthocenter
  simp only [Prod.mk.injEq]
  constructor <;> ring

/-- The reflection of the orthocenter across the midpoint of `BC` lies on the
    circumcircle (it is the antipode of `A`). -/
theorem reflectOrthoMidBC_on_circumcircle (T : Triangle) :
    dist2 T.circumcenter (reflectOrthoMidBC T) = T.circumradius := by
  unfold Triangle.circumradius dist2
  congr 1
  unfold reflectOrthoMidBC Triangle.orthocenter
  simp only []
  ring

-- ============================================================
-- Part VII: Worked example (3-4-5 right triangle)
-- ============================================================

/-- For the 3-4-5 right triangle the reflection of the orthocenter (`= A = (0,0)`)
    across the midpoint of `BC` is `(3, 4)`, the antipode of `A` on the
    circumcircle of radius `5/2` centred at `(3/2, 2)`. -/
theorem triangle_345_reflectOrthoMidBC :
    reflectOrthoMidBC triangle_345 = (3, 4) := by
  unfold reflectOrthoMidBC
  rw [triangle_345_orthocenter]
  unfold triangle_345
  simp only [Prod.mk.injEq]
  constructor <;> norm_num

end FeuerbachsTheoremDefsOQ01OQ01OQ01
