/-
  Feuerbach's Theorem DefsOQ01OQ01OQ02: The Orthocentric System
  — each of A, B, C, H is the orthocenter of the triangle on the other three.

  ## The Open Question

  The orthocenter sub-line established the *existence* of the orthocenter
  `H = A + B + C − 2O` (concurrency of the three altitudes) and then measured it
  metrically (`OH²`, `AH²`, `AH = 2·OM_a`).  All of this treats `H` as a derived
  point attached to a *fixed* base triangle `ABC`.

  The reflections file `FeuerbachsTheoremDefsOQ01OQ01OQ01` noted in passing that
  putting `H` on the circumcircle is "a hallmark of the **orthocentric
  configuration** that the nine-point-circle development never establishes."
  This file establishes that configuration.

  **Open question.** Is the four-point set `{A, B, C, H}` *symmetric* — does each
  of the four points play the role of the orthocenter of the triangle formed by
  the other three?  Equivalently: is `A` the orthocenter of `BCH`, `B` the
  orthocenter of `CAH`, and `C` the orthocenter of `ABH`?

  ## What This File Proves

  We characterize "`P` is an orthocenter of triangle `XYZ`" by the three
  altitude-perpendicularity conditions (`IsOrthocenterOf`) and show:

  ### The three perpendicularities of the configuration
  `orthocentric_perp_a` : `(A − H) ⊥ (B − C)`
  `orthocentric_perp_b` : `(B − H) ⊥ (C − A)`
  `orthocentric_perp_c` : `(C − H) ⊥ (A − B)`
  Each is a *linear* fact in the circumcenter `O`: after substituting
  `H = A + B + C − 2O` it is exactly one perpendicular-bisector relation.  These
  three "opposite connectors are perpendicular" statements ARE the orthocentric
  system.

  ### The four orthocenter memberships
  `orthocenter_of_ABC` : `H` is the orthocenter of `ABC` (consistency with the
      parent's `Triangle.orthocenter`),
  `orthocenter_of_BCH` : `A` is the orthocenter of `BCH`,
  `orthocenter_of_CAH` : `B` is the orthocenter of `CAH`,
  `orthocenter_of_ABH` : `C` is the orthocenter of `ABH`.
  Capstone `orthocentric_system` bundles all four.

  ### Uniqueness — "THE" orthocenter
  `isOrthocenterOf_unique` : for a non-degenerate triangle the perpendicularity
  characterization pins the orthocenter down uniquely (a `2×2` Cramer argument
  whose determinant is exactly the triangle's non-degeneracy determinant).  Hence
  on a non-degenerate sub-triangle the membership facts above identify *the*
  orthocenter (`orthocenter_of_BCH_unique`).

  ### Structural consequence: one shared nine-point circle
  `orthocentric_six_midpoints_concyclic` : the midpoints of all six connectors of
  `{A, B, C, H}` — the three sides `BC, CA, AB` and the three cevian segments
  `AH, BH, CH` — lie on a single circle (the common nine-point circle, centre
  `N`, radius `R/2`).  This repackages the parent's six nine-point theorems as a
  statement about the orthocentric system.

  ### Worked example
  For `A = (0,0)`, `B = (4,0)`, `C = (1,2)` the circumcenter is `(2, 1/4)` and the
  orthocenter is `H = (1, 3/2)`; the four points are genuinely distinct (an
  *acute* configuration, unlike the degenerate 3-4-5 right triangle where `H`
  collapses onto the right-angle vertex), and `A` is verified to be the
  orthocenter of `BCH`.

  Status: 0 sorries, 0 axioms.
-/

import Proofs.FeuerbachsTheoremDefs

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ01OQ01OQ02

open FeuerbachsTheorem

-- ============================================================
-- Part 0: Perpendicular-bisector relations for the circumcenter
--
-- The parent declares these `private`; we reprove the two against vertex A
-- (linear in O via `field_simp; ring`) and derive the BC relation as their
-- difference, so this file builds independently.
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

/-- The perpendicular bisector of `BC`: `(C − B) ⊥ (C + B − 2O)`.  Obtained as the
    difference of the `AC` and `AB` relations (equidistance is transitive). -/
private lemma perp_bisector_BC (T : Triangle) :
    (T.C.1 - T.B.1) * (T.C.1 + T.B.1 - 2 * T.circumcenter.1) +
    (T.C.2 - T.B.2) * (T.C.2 + T.B.2 - 2 * T.circumcenter.2) = 0 := by
  linear_combination perp_bisector_AC T - perp_bisector_AB T

-- ============================================================
-- Part 1: The orthocenter in coordinates
-- ============================================================

/-- The first coordinate of the orthocenter: `H₁ = A₁ + B₁ + C₁ − 2O₁`. -/
private lemma orthocenter_fst (T : Triangle) :
    T.orthocenter.1 = T.A.1 + T.B.1 + T.C.1 - 2 * T.circumcenter.1 := rfl

/-- The second coordinate of the orthocenter: `H₂ = A₂ + B₂ + C₂ − 2O₂`. -/
private lemma orthocenter_snd (T : Triangle) :
    T.orthocenter.2 = T.A.2 + T.B.2 + T.C.2 - 2 * T.circumcenter.2 := rfl

-- ============================================================
-- Part 2: The three perpendicularities of the orthocentric system
--
-- In an orthocentric system the three pairs of OPPOSITE connectors are
-- perpendicular:  AH ⊥ BC,  BH ⊥ CA,  CH ⊥ AB.  Each, after substituting
-- H = A + B + C − 2O, is exactly one perpendicular-bisector relation.
-- ============================================================

/-- `(A − H) ⊥ (B − C)`: the connector `AH` is perpendicular to side `BC`. -/
theorem orthocentric_perp_a (T : Triangle) :
    (T.A.1 - T.orthocenter.1) * (T.B.1 - T.C.1) +
    (T.A.2 - T.orthocenter.2) * (T.B.2 - T.C.2) = 0 := by
  rw [orthocenter_fst, orthocenter_snd]
  linear_combination perp_bisector_BC T

/-- `(B − H) ⊥ (C − A)`: the connector `BH` is perpendicular to side `CA`. -/
theorem orthocentric_perp_b (T : Triangle) :
    (T.B.1 - T.orthocenter.1) * (T.C.1 - T.A.1) +
    (T.B.2 - T.orthocenter.2) * (T.C.2 - T.A.2) = 0 := by
  rw [orthocenter_fst, orthocenter_snd]
  linear_combination -(perp_bisector_AC T)

/-- `(C − H) ⊥ (A − B)`: the connector `CH` is perpendicular to side `AB`. -/
theorem orthocentric_perp_c (T : Triangle) :
    (T.C.1 - T.orthocenter.1) * (T.A.1 - T.B.1) +
    (T.C.2 - T.orthocenter.2) * (T.A.2 - T.B.2) = 0 := by
  rw [orthocenter_fst, orthocenter_snd]
  linear_combination perp_bisector_AB T

/-- The three perpendicularities bundled: opposite connectors of `{A,B,C,H}` are
    perpendicular. -/
theorem orthocentric_perpendicularities (T : Triangle) :
    ((T.A.1 - T.orthocenter.1) * (T.B.1 - T.C.1) +
       (T.A.2 - T.orthocenter.2) * (T.B.2 - T.C.2) = 0) ∧
    ((T.B.1 - T.orthocenter.1) * (T.C.1 - T.A.1) +
       (T.B.2 - T.orthocenter.2) * (T.C.2 - T.A.2) = 0) ∧
    ((T.C.1 - T.orthocenter.1) * (T.A.1 - T.B.1) +
       (T.C.2 - T.orthocenter.2) * (T.A.2 - T.B.2) = 0) :=
  ⟨orthocentric_perp_a T, orthocentric_perp_b T, orthocentric_perp_c T⟩

-- ============================================================
-- Part 3: The orthocenter predicate and the four memberships
-- ============================================================

/-- `P` is *an* orthocenter of triangle `XYZ`: each connector from a vertex to `P`
    is perpendicular to the opposite side.  Stated coordinatewise; for a
    non-degenerate triangle `isOrthocenterOf_unique` shows `P` is unique. -/
def IsOrthocenterOf (P X Y Z : Point) : Prop :=
    ((P.1 - X.1) * (Y.1 - Z.1) + (P.2 - X.2) * (Y.2 - Z.2) = 0) ∧
    ((P.1 - Y.1) * (Z.1 - X.1) + (P.2 - Y.2) * (Z.2 - X.2) = 0) ∧
    ((P.1 - Z.1) * (X.1 - Y.1) + (P.2 - Z.2) * (X.2 - Y.2) = 0)

/-- Consistency: the parent's `Triangle.orthocenter` is an orthocenter of `ABC`
    in the perpendicularity sense — `H` lies on all three altitudes. -/
theorem orthocenter_of_ABC (T : Triangle) :
    IsOrthocenterOf T.orthocenter T.A T.B T.C := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination -(orthocentric_perp_a T)
  · linear_combination -(orthocentric_perp_b T)
  · linear_combination -(orthocentric_perp_c T)

/-- `A` is the orthocenter of triangle `BCH`. -/
theorem orthocenter_of_BCH (T : Triangle) :
    IsOrthocenterOf T.A T.B T.C T.orthocenter := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination orthocentric_perp_c T
  · linear_combination orthocentric_perp_b T
  · linear_combination orthocentric_perp_a T

/-- `B` is the orthocenter of triangle `CAH`. -/
theorem orthocenter_of_CAH (T : Triangle) :
    IsOrthocenterOf T.B T.C T.A T.orthocenter := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination orthocentric_perp_a T
  · linear_combination orthocentric_perp_c T
  · linear_combination orthocentric_perp_b T

/-- `C` is the orthocenter of triangle `ABH`. -/
theorem orthocenter_of_ABH (T : Triangle) :
    IsOrthocenterOf T.C T.A T.B T.orthocenter := by
  refine ⟨?_, ?_, ?_⟩
  · linear_combination orthocentric_perp_b T
  · linear_combination orthocentric_perp_a T
  · linear_combination orthocentric_perp_c T

/-- **The orthocentric system.**  Each of the four points `A, B, C, H` is the
    orthocenter of the triangle formed by the other three. -/
theorem orthocentric_system (T : Triangle) :
    IsOrthocenterOf T.orthocenter T.A T.B T.C ∧
    IsOrthocenterOf T.A T.B T.C T.orthocenter ∧
    IsOrthocenterOf T.B T.C T.A T.orthocenter ∧
    IsOrthocenterOf T.C T.A T.B T.orthocenter :=
  ⟨orthocenter_of_ABC T, orthocenter_of_BCH T, orthocenter_of_CAH T,
   orthocenter_of_ABH T⟩

-- ============================================================
-- Part 4: Uniqueness — pinning down "THE" orthocenter
-- ============================================================

/-- For a non-degenerate triangle `XYZ` the perpendicularity characterization
    determines the orthocenter uniquely.  The two altitude conditions form a
    `2×2` linear system in `P − P'` whose determinant is precisely the triangle's
    non-degeneracy determinant, so `P = P'`. -/
theorem isOrthocenterOf_unique (X Y Z P P' : Point)
    (hdet : (Y.1 - X.1) * (Z.2 - X.2) - (Z.1 - X.1) * (Y.2 - X.2) ≠ 0)
    (hP : IsOrthocenterOf P X Y Z) (hP' : IsOrthocenterOf P' X Y Z) :
    P = P' := by
  obtain ⟨hP1, hP2, _⟩ := hP
  obtain ⟨hP1', hP2', _⟩ := hP'
  -- Differences of the two altitude conditions: two linear equations in P − P'.
  have e1 : (P.1 - P'.1) * (Y.1 - Z.1) + (P.2 - P'.2) * (Y.2 - Z.2) = 0 := by
    linear_combination hP1 - hP1'
  have e2 : (P.1 - P'.1) * (Z.1 - X.1) + (P.2 - P'.2) * (Z.2 - X.2) = 0 := by
    linear_combination hP2 - hP2'
  -- Cramer: (P.1 − P'.1)·det = 0 and (P.2 − P'.2)·det = 0.
  have hx : (P.1 - P'.1) *
      ((Y.1 - X.1) * (Z.2 - X.2) - (Z.1 - X.1) * (Y.2 - X.2)) = 0 := by
    linear_combination (Z.2 - X.2) * e1 - (Y.2 - Z.2) * e2
  have hy : (P.2 - P'.2) *
      ((Y.1 - X.1) * (Z.2 - X.2) - (Z.1 - X.1) * (Y.2 - X.2)) = 0 := by
    linear_combination (Y.1 - Z.1) * e2 - (Z.1 - X.1) * e1
  have hx0 : P.1 - P'.1 = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact h
    · exact absurd h hdet
  have hy0 : P.2 - P'.2 = 0 := by
    rcases mul_eq_zero.mp hy with h | h
    · exact h
    · exact absurd h hdet
  have h1 : P.1 = P'.1 := by linarith
  have h2 : P.2 = P'.2 := by linarith
  calc P = (P.1, P.2) := rfl
    _ = (P'.1, P'.2) := by rw [h1, h2]
    _ = P' := rfl

/-- On a non-degenerate sub-triangle `BCH`, `A` is *the* orthocenter: any point
    satisfying the perpendicularity characterization coincides with `A`. -/
theorem orthocenter_of_BCH_unique (T : Triangle) (P : Point)
    (hdet : (T.C.1 - T.B.1) * (T.orthocenter.2 - T.B.2) -
            (T.orthocenter.1 - T.B.1) * (T.C.2 - T.B.2) ≠ 0)
    (hP : IsOrthocenterOf P T.B T.C T.orthocenter) :
    P = T.A :=
  isOrthocenterOf_unique T.B T.C T.orthocenter P T.A hdet hP (orthocenter_of_BCH T)

-- ============================================================
-- Part 5: Structural consequence — one shared nine-point circle
-- ============================================================

/-- **One shared nine-point circle.**  The midpoints of all six connectors of the
    orthocentric system `{A, B, C, H}` — the three sides `BC, CA, AB` and the
    three cevian segments `AH, BH, CH` — lie on a single circle, the common
    nine-point circle (centre `N`, radius `R/2`).  Repackages the parent's six
    nine-point membership theorems. -/
theorem orthocentric_six_midpoints_concyclic (T : Triangle) :
    dist2 T.ninePointCenter T.midpoint_a = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_b = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_c = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_AH = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_BH = T.ninePointRadius ∧
    dist2 T.ninePointCenter T.midpoint_CH = T.ninePointRadius :=
  ⟨midpoint_a_on_ninePointCircle T, midpoint_b_on_ninePointCircle T,
   midpoint_c_on_ninePointCircle T, midpoint_AH_on_ninePointCircle T,
   midpoint_BH_on_ninePointCircle T, midpoint_CH_on_ninePointCircle T⟩

-- ============================================================
-- Part 6: Worked example — a genuine (acute) orthocentric system
-- ============================================================

/-- An acute triangle `A=(0,0)`, `B=(4,0)`, `C=(1,2)` with four distinct points
    `A, B, C, H` (the 3-4-5 right triangle is degenerate as `H` collapses onto
    the right-angle vertex). -/
def exampleTriangle : Triangle where
  A := (0, 0)
  B := (4, 0)
  C := (1, 2)
  nondegenerate := by norm_num

theorem exampleTriangle_circumcenter :
    exampleTriangle.circumcenter = (2, 1/4) := by
  unfold Triangle.circumcenter exampleTriangle
  norm_num

theorem exampleTriangle_orthocenter :
    exampleTriangle.orthocenter = (1, 3/2) := by
  unfold Triangle.orthocenter
  rw [exampleTriangle_circumcenter]
  norm_num [exampleTriangle]

/-- The four points of the example are pairwise distinct: a genuine, non-collapsed
    orthocentric system. -/
theorem exampleTriangle_four_distinct :
    exampleTriangle.A ≠ exampleTriangle.B ∧
    exampleTriangle.A ≠ exampleTriangle.C ∧
    exampleTriangle.B ≠ exampleTriangle.C ∧
    exampleTriangle.orthocenter ≠ exampleTriangle.A ∧
    exampleTriangle.orthocenter ≠ exampleTriangle.B ∧
    exampleTriangle.orthocenter ≠ exampleTriangle.C := by
  rw [exampleTriangle_orthocenter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [exampleTriangle, ne_eq, Prod.mk.injEq, not_and] <;> norm_num

/-- In the example, `A = (0,0)` is the orthocenter of triangle `B C H`. -/
theorem exampleTriangle_A_orthocenter_of_BCH :
    IsOrthocenterOf exampleTriangle.A exampleTriangle.B exampleTriangle.C
      exampleTriangle.orthocenter :=
  orthocenter_of_BCH exampleTriangle

end FeuerbachsTheoremDefsOQ01OQ01OQ02
