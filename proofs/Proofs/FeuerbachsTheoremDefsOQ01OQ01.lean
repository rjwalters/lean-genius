/-
  Feuerbach's Theorem DefsOQ01OQ01: The Orthocenter Lies on All Three Altitudes
  (Concurrency of the Altitudes)

  ## The Open Question

  The parent file `FeuerbachsTheoremDefs` *defines* the orthocenter by the Euler
  formula `H = A + B + C − 2·O` (O the circumcenter) and uses it throughout the
  nine-point–circle proof.  The sibling `FeuerbachsTheoremDefsOQ01` verified the
  *defining* characterization of the three altitude **feet** (each foot lies on the
  opposite side and the vertex-to-foot segment is perpendicular to that side).

  Neither file ever verifies the *defining* characterization of the orthocenter
  itself, namely that

    H lies on all three altitudes,

  i.e. that the three altitudes are **concurrent** at H.  Until this is shown,
  "orthocenter" is just a name attached to an opaque circumcenter-based formula.

  ## What This File Proves

  ### The orthocenter is on each altitude (perpendicularity)
  `orthocenter_perp_a` : (H − A) · (C − B) = 0   — AH ⊥ BC
  `orthocenter_perp_b` : (H − B) · (A − C) = 0   — BH ⊥ CA
  `orthocenter_perp_c` : (H − C) · (B − A) = 0   — CH ⊥ AB

  Each is the perpendicular-bisector identity for the opposite side: writing
  H − A = (B − O) + (C − O), the dot product with C − B telescopes to
  |C − O|² − |B − O|², which vanishes because O is equidistant from B and C.
  The condition is *linear* in O, so after substituting the circumcenter formula
  it closes by `field_simp; ring`.

  ### Concurrency capstone
  `altitudes_concurrent` bundles the three facts: the three altitudes all pass
  through the single point H.

  ### The orthocenter is on each altitude *line through the foot* (collinearity)
  `orthocenter_collinear_a/b/c` : H, the vertex, and the corresponding altitude
  foot (`foot_a/b/c` of the parent) are collinear — the orthocenter sits on
  the very line determined by a vertex and its altitude foot.  Proved cleanly from
  the two perpendicularity facts via a plane-geometry lemma (two vectors
  perpendicular to a common nonzero vector are parallel).

  ### Uniqueness
  `orthocenter_unique` : H is the *only* point lying on two of the altitudes; the
  intersection of any two altitudes already determines the orthocenter (and the
  third altitude then passes through it).

  ### Worked example
  `triangle_345_orthocenter_eq_A` : for the right triangle the orthocenter
  coincides with the right-angle vertex A.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01

open FeuerbachsTheorem

-- ============================================================
-- Part 0: Altitude-foot perpendicularity (self-contained copies)
--
-- These restate the defining perpendicularity of each altitude foot
-- (also proved in the sibling `FeuerbachsTheoremDefsOQ01`).  They are
-- reproved here so this file builds independently against the parent.
-- ============================================================

set_option maxHeartbeats 6400000 in
/-- The altitude `A Hₐ` is perpendicular to side BC: `(Hₐ − A) · (C − B) = 0`. -/
private lemma foot_a_perp (T : Triangle) :
    (T.foot_a.1 - T.A.1) * (T.C.1 - T.B.1)
      + (T.foot_a.2 - T.A.2) * (T.C.2 - T.B.2) = 0 := by
  unfold Triangle.foot_a
  simp only []
  have hbc : (T.C.1 - T.B.1) ^ 2 + (T.C.2 - T.B.2) ^ 2 ≠ 0 := bc_sq_ne_zero T
  field_simp
  ring

/-- The altitude `B H_b` is perpendicular to side CA: `(H_b − B) · (A − C) = 0`. -/
private lemma foot_b_perp (T : Triangle) :
    (T.foot_b.1 - T.B.1) * (T.A.1 - T.C.1)
      + (T.foot_b.2 - T.B.2) * (T.A.2 - T.C.2) = 0 := by
  unfold Triangle.foot_b
  simp only []
  have hca : (T.A.1 - T.C.1) ^ 2 + (T.A.2 - T.C.2) ^ 2 ≠ 0 := ca_sq_ne_zero T
  field_simp
  ring

/-- The altitude `C H_c` is perpendicular to side AB: `(H_c − C) · (B − A) = 0`. -/
private lemma foot_c_perp (T : Triangle) :
    (T.foot_c.1 - T.C.1) * (T.B.1 - T.A.1)
      + (T.foot_c.2 - T.C.2) * (T.B.2 - T.A.2) = 0 := by
  unfold Triangle.foot_c
  simp only []
  have hab : (T.B.1 - T.A.1) ^ 2 + (T.B.2 - T.A.2) ^ 2 ≠ 0 := ab_sq_ne_zero T
  field_simp
  ring

-- ============================================================
-- Part I: The orthocenter lies on each altitude (perpendicularity)
-- ============================================================

set_option maxHeartbeats 6400000 in
/-- The altitude through the orthocenter from A is perpendicular to side BC:
    `(H − A) · (C − B) = 0`.  Since `H − A = (B − O) + (C − O)`, the dot product
    with `C − B = (C − O) − (B − O)` telescopes to `|C − O|² − |B − O|² = 0`. -/
theorem orthocenter_perp_a (T : Triangle) :
    (T.orthocenter.1 - T.A.1) * (T.C.1 - T.B.1)
      + (T.orthocenter.2 - T.A.2) * (T.C.2 - T.B.2) = 0 := by
  unfold Triangle.orthocenter
  simp only []
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
/-- The altitude through the orthocenter from B is perpendicular to side CA:
    `(H − B) · (A − C) = 0`. -/
theorem orthocenter_perp_b (T : Triangle) :
    (T.orthocenter.1 - T.B.1) * (T.A.1 - T.C.1)
      + (T.orthocenter.2 - T.B.2) * (T.A.2 - T.C.2) = 0 := by
  unfold Triangle.orthocenter
  simp only []
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
/-- The altitude through the orthocenter from C is perpendicular to side AB:
    `(H − C) · (B − A) = 0`. -/
theorem orthocenter_perp_c (T : Triangle) :
    (T.orthocenter.1 - T.C.1) * (T.B.1 - T.A.1)
      + (T.orthocenter.2 - T.C.2) * (T.B.2 - T.A.2) = 0 := by
  unfold Triangle.orthocenter
  simp only []
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

-- ============================================================
-- Part II: Concurrency capstone
-- ============================================================

/-- **Concurrency of the altitudes.**  The orthocenter H lies on all three
    altitudes simultaneously: each altitude (the line through a vertex
    perpendicular to the opposite side) passes through H. -/
theorem altitudes_concurrent (T : Triangle) :
    ((T.orthocenter.1 - T.A.1) * (T.C.1 - T.B.1)
        + (T.orthocenter.2 - T.A.2) * (T.C.2 - T.B.2) = 0) ∧
    ((T.orthocenter.1 - T.B.1) * (T.A.1 - T.C.1)
        + (T.orthocenter.2 - T.B.2) * (T.A.2 - T.C.2) = 0) ∧
    ((T.orthocenter.1 - T.C.1) * (T.B.1 - T.A.1)
        + (T.orthocenter.2 - T.C.2) * (T.B.2 - T.A.2) = 0) :=
  ⟨orthocenter_perp_a T, orthocenter_perp_b T, orthocenter_perp_c T⟩

-- ============================================================
-- Part III: The orthocenter is on each altitude line through the foot
-- ============================================================

/-- Two plane vectors perpendicular to a common nonzero vector are parallel:
    if `u ⟂ w` and `v ⟂ w` with `w ≠ 0`, then the cross product `u × v` vanishes. -/
private lemma cross_eq_zero_of_perp_perp
    (u1 u2 v1 v2 w1 w2 : ℝ) (hw : w1 ^ 2 + w2 ^ 2 ≠ 0)
    (hu : u1 * w1 + u2 * w2 = 0) (hv : v1 * w1 + v2 * w2 = 0) :
    u1 * v2 - u2 * v1 = 0 := by
  have key : (u1 * v2 - u2 * v1) * (w1 ^ 2 + w2 ^ 2) = 0 := by
    linear_combination (w1 * v2 - w2 * v1) * hu + (w2 * u1 - w1 * u2) * hv
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h hw

/-- The orthocenter is collinear with A and the foot `foot_a` of the altitude from
    A: H lies on the line through A and its altitude foot.  Both `foot_a − A` and
    `H − A` are perpendicular to BC, hence parallel. -/
theorem orthocenter_collinear_a (T : Triangle) :
    (T.foot_a.1 - T.A.1) * (T.orthocenter.2 - T.A.2)
      - (T.foot_a.2 - T.A.2) * (T.orthocenter.1 - T.A.1) = 0 :=
  cross_eq_zero_of_perp_perp _ _ _ _ _ _ (bc_sq_ne_zero T)
    (foot_a_perp T) (orthocenter_perp_a T)

/-- The orthocenter is collinear with B and the foot `foot_b`. -/
theorem orthocenter_collinear_b (T : Triangle) :
    (T.foot_b.1 - T.B.1) * (T.orthocenter.2 - T.B.2)
      - (T.foot_b.2 - T.B.2) * (T.orthocenter.1 - T.B.1) = 0 :=
  cross_eq_zero_of_perp_perp _ _ _ _ _ _ (ca_sq_ne_zero T)
    (foot_b_perp T) (orthocenter_perp_b T)

/-- The orthocenter is collinear with C and the foot `foot_c`. -/
theorem orthocenter_collinear_c (T : Triangle) :
    (T.foot_c.1 - T.C.1) * (T.orthocenter.2 - T.C.2)
      - (T.foot_c.2 - T.C.2) * (T.orthocenter.1 - T.C.1) = 0 :=
  cross_eq_zero_of_perp_perp _ _ _ _ _ _ (ab_sq_ne_zero T)
    (foot_c_perp T) (orthocenter_perp_c T)

-- ============================================================
-- Part IV: Uniqueness — two altitudes already determine the orthocenter
-- ============================================================

/-- The determinant of the two altitude directions equals the (nonzero)
    nondegeneracy form, so the two altitudes from A and B are not parallel. -/
private lemma altitude_det_ne_zero (T : Triangle) :
    (T.C.1 - T.B.1) * (T.A.2 - T.C.2) - (T.C.2 - T.B.2) * (T.A.1 - T.C.1) ≠ 0 := by
  intro h
  apply T.nondegenerate
  linear_combination h

/-- **Uniqueness of the orthocenter.**  Any point P lying on the altitude from A
    (`(P − A) · (C − B) = 0`) and on the altitude from B
    (`(P − B) · (A − C) = 0`) equals the orthocenter H.  Thus two altitudes
    already determine H, and the third necessarily passes through it. -/
theorem orthocenter_unique (T : Triangle) (P : Point)
    (hpa : (P.1 - T.A.1) * (T.C.1 - T.B.1) + (P.2 - T.A.2) * (T.C.2 - T.B.2) = 0)
    (hpb : (P.1 - T.B.1) * (T.A.1 - T.C.1) + (P.2 - T.B.2) * (T.A.2 - T.C.2) = 0) :
    P = T.orthocenter := by
  have hdet := altitude_det_ne_zero T
  -- P − H is perpendicular to BC and to CA.
  have hd1 : (P.1 - T.orthocenter.1) * (T.C.1 - T.B.1)
      + (P.2 - T.orthocenter.2) * (T.C.2 - T.B.2) = 0 := by
    linear_combination hpa - orthocenter_perp_a T
  have hd2 : (P.1 - T.orthocenter.1) * (T.A.1 - T.C.1)
      + (P.2 - T.orthocenter.2) * (T.A.2 - T.C.2) = 0 := by
    linear_combination hpb - orthocenter_perp_b T
  -- Cramer: eliminate one coordinate at a time.
  have hD1 : (P.1 - T.orthocenter.1)
      * ((T.C.1 - T.B.1) * (T.A.2 - T.C.2) - (T.C.2 - T.B.2) * (T.A.1 - T.C.1)) = 0 := by
    linear_combination (T.A.2 - T.C.2) * hd1 - (T.C.2 - T.B.2) * hd2
  have hD2 : (P.2 - T.orthocenter.2)
      * ((T.C.1 - T.B.1) * (T.A.2 - T.C.2) - (T.C.2 - T.B.2) * (T.A.1 - T.C.1)) = 0 := by
    linear_combination -(T.A.1 - T.C.1) * hd1 + (T.C.1 - T.B.1) * hd2
  have h1 : P.1 - T.orthocenter.1 = 0 := by
    rcases mul_eq_zero.mp hD1 with h | h
    · exact h
    · exact absurd h hdet
  have h2 : P.2 - T.orthocenter.2 = 0 := by
    rcases mul_eq_zero.mp hD2 with h | h
    · exact h
    · exact absurd h hdet
  exact Prod.ext (by linarith) (by linarith)

-- ============================================================
-- Part V: Worked example
-- ============================================================

/-- For the 3-4-5 right triangle (A = (0,0), B = (3,0), C = (0,4)) the orthocenter
    coincides with the right-angle vertex A = (0,0), as the legs AB and AC are
    themselves two of the altitudes. -/
theorem triangle_345_orthocenter_eq_A :
    triangle_345.orthocenter = triangle_345.A := by
  rw [triangle_345_orthocenter]; rfl

end FeuerbachsTheoremDefsOQ01OQ01
