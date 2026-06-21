/-
  Feuerbach's Theorem DefsOQ01OQ01OQ01OQ01: Euler's Metric Identity for the
  Orthocenter — OH² = 9R² − (a² + b² + c²)

  ## The Open Question

  The orthocenter sub-line of this development has so far been *qualitative*:

  * `FeuerbachsTheoremDefsOQ01OQ01` — the three altitudes are concurrent at
    `H = A + B + C − 2·O`;
  * `FeuerbachsTheoremDefsOQ01OQ01OQ01` — the reflections of `H` across the
    three sides (and across the side midpoints) lie on the circumcircle.

  The grandparent `FeuerbachsTheoremDefs` records the *Euler line* as the
  collinearity `G = (2O + H)/3` and the nine-point centre `N = (O + H)/2`, but
  never measures the distance `OH` itself.  The natural open question closing
  the orthocenter line is the classical **metric** identity

      OH² = 9R² − (a² + b² + c²),

  the distance from the circumcenter to the orthocenter in terms of the
  circumradius `R` and the three side lengths `a, b, c`.  It is the metric
  companion of the qualitative reflection facts and the quantitative root of
  Euler's inequality `OH ≥ 0 ⟹ a² + b² + c² ≤ 9R²`.

  ## What This File Proves

  ### The headline identity
  `orthocenter_circumcenter_dist_sq` :
      `dist²(O, H) = 9·dist²(O, A) − (dist²(B,C) + dist²(C,A) + dist²(A,B))`
  the squared-distance form, and
  `orthocenter_circumcenter_dist_classical` :
      `dist²(O, H) = 9R² − (a² + b² + c²)`
  the textbook form in terms of `R = circumradius` and `a, b, c = side lengths`.

  The proof reduces (after substituting `H = A + B + C − 2O`) to a polynomial
  identity that holds modulo the two circumcenter-equidistance relations
  `|B − O|² = |A − O|²` and `|C − O|² = |A − O|²`; one checks by hand that

      OH² − [9R² − (a²+b²+c²)] = −3(|A−O|² − |B−O|²) − 3(|A−O|² − |C−O|²),

  so a single `linear_combination 3·equidistB + 3·equidistC` discharges it.

  ### Metric form of the Euler line
  Because `G − O = (H − O)/3` and `H − G = (2/3)(H − O)`, the same kernel yields
  `centroid_circumcenter_dist_sq` : `OH² = 9·OG²`,
  `centroid_orthocenter_dist_sq`  : `4·OH² = 9·GH²`  (so `OG : GH : OH = 1 : 2 : 3`),
  and the centroid version of Euler's identity
  `centroid_circumcenter_dist_classical` : `OG² = R² − (a²+b²+c²)/9`.

  ### Worked example
  `triangle_345_OH_sq` : for the 3-4-5 right triangle `OH² = 25/4` (so `OH = 5/2`
  = R, since the orthocenter is the right-angle vertex), matching
  `9R² − (a²+b²+c²) = 9·(25/4) − 50 = 25/4`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01OQ01OQ01

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
-- Part II: Euler's metric identity OH² = 9R² − (a²+b²+c²)
-- ============================================================

/-- **Euler's metric identity (squared-distance form).**
    The squared distance from the circumcenter `O` to the orthocenter `H` is

      `OH² = 9·|O−A|²  −  (|B−C|² + |C−A|² + |A−B|²)`.

    With `H = A + B + C − 2O`, the difference of the two sides equals
    `−3(|A−O|² − |B−O|²) − 3(|A−O|² − |C−O|²)`, which vanishes because the
    circumcenter is equidistant from the three vertices. -/
theorem orthocenter_circumcenter_dist_sq (T : Triangle) :
    dist2_sq T.circumcenter T.orthocenter
      = 9 * dist2_sq T.circumcenter T.A
        - (dist2_sq T.B T.C + dist2_sq T.C T.A + dist2_sq T.A T.B) := by
  simp only [dist2_sq, Triangle.orthocenter]
  linear_combination 3 * equidistB T + 3 * equidistC T

/-- **Euler's metric identity (classical form).**
    `OH² = 9R² − (a² + b² + c²)` where `R = circumradius` and `a, b, c` are the
    three side lengths.  Obtained from the squared-distance form by replacing
    each squared distance with the corresponding squared length. -/
theorem orthocenter_circumcenter_dist_classical (T : Triangle) :
    dist2_sq T.circumcenter T.orthocenter
      = 9 * T.circumradius ^ 2 - (T.side_a ^ 2 + T.side_b ^ 2 + T.side_c ^ 2) := by
  rw [show T.circumradius ^ 2 = dist2_sq T.circumcenter T.A from sq_dist2 _ _,
      show T.side_a ^ 2 = dist2_sq T.B T.C from sq_dist2 _ _,
      show T.side_b ^ 2 = dist2_sq T.C T.A from sq_dist2 _ _,
      show T.side_c ^ 2 = dist2_sq T.A T.B from sq_dist2 _ _]
  exact orthocenter_circumcenter_dist_sq T

/-- Euler's inequality precursor: `a² + b² + c² ≤ 9R²`, immediate from the
    metric identity and `OH² ≥ 0`. -/
theorem sum_sq_sides_le_nine_circumradius_sq (T : Triangle) :
    T.side_a ^ 2 + T.side_b ^ 2 + T.side_c ^ 2 ≤ 9 * T.circumradius ^ 2 := by
  have h := orthocenter_circumcenter_dist_classical T
  have hnn : 0 ≤ dist2_sq T.circumcenter T.orthocenter := by
    unfold dist2_sq; positivity
  linarith

-- ============================================================
-- Part III: Metric form of the Euler line
--
-- O, G, H are collinear with G − O = (H − O)/3 and H − G = (2/3)(H − O).
-- Squaring gives OH² = 9·OG² and 4·OH² = 9·GH², i.e. OG : GH : OH = 1 : 2 : 3.
-- These need no equidistance — they are pure consequences of the definitions.
-- ============================================================

/-- `OH² = 9·OG²`: the circumcenter–orthocenter distance is three times the
    circumcenter–centroid distance (the `1 : 3` leg of the Euler-line ratio). -/
theorem centroid_circumcenter_dist_sq (T : Triangle) :
    dist2_sq T.circumcenter T.orthocenter = 9 * dist2_sq T.circumcenter T.centroid := by
  simp only [dist2_sq, Triangle.orthocenter, Triangle.centroid]
  ring

/-- `4·OH² = 9·GH²`: the centroid–orthocenter distance is two thirds of `OH`
    (the `2 : 3` leg of the Euler-line ratio). -/
theorem centroid_orthocenter_dist_sq (T : Triangle) :
    4 * dist2_sq T.circumcenter T.orthocenter = 9 * dist2_sq T.centroid T.orthocenter := by
  simp only [dist2_sq, Triangle.orthocenter, Triangle.centroid]
  ring

/-- The centroid form of Euler's identity: `OG² = R² − (a² + b² + c²)/9`. -/
theorem centroid_circumcenter_dist_classical (T : Triangle) :
    dist2_sq T.circumcenter T.centroid
      = T.circumradius ^ 2 - (T.side_a ^ 2 + T.side_b ^ 2 + T.side_c ^ 2) / 9 := by
  have h9 : (9 : ℝ) * dist2_sq T.circumcenter T.centroid
      = 9 * T.circumradius ^ 2 - (T.side_a ^ 2 + T.side_b ^ 2 + T.side_c ^ 2) := by
    rw [← centroid_circumcenter_dist_sq T]
    exact orthocenter_circumcenter_dist_classical T
  linarith

-- ============================================================
-- Part IV: Worked example (3-4-5 right triangle)
-- ============================================================

/-- For the 3-4-5 right triangle the orthocenter is the right-angle vertex
    `A = (0,0)` and the circumcenter is `(3/2, 2)`, so `OH² = (3/2)² + 2² = 25/4`
    and `OH = 5/2 = R`. -/
theorem triangle_345_OH_sq :
    dist2_sq triangle_345.circumcenter triangle_345.orthocenter = 25 / 4 := by
  rw [triangle_345_circumcenter, triangle_345_orthocenter]
  unfold dist2_sq; norm_num

/-- The 3-4-5 triangle satisfies Euler's metric identity numerically:
    `9R² − (a² + b² + c²) = 9·(25/4) − (25 + 16 + 9) = 25/4 = OH²`. -/
theorem triangle_345_euler_metric :
    dist2_sq triangle_345.circumcenter triangle_345.orthocenter
      = 9 * triangle_345.circumradius ^ 2
        - (triangle_345.side_a ^ 2 + triangle_345.side_b ^ 2 + triangle_345.side_c ^ 2) := by
  rw [triangle_345_OH_sq, triangle_345_circumradius, triangle_345_side_a,
      triangle_345_side_b, triangle_345_side_c]
  norm_num

end FeuerbachsTheoremDefsOQ01OQ01OQ01OQ01
