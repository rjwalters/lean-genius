import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Desargues's Theorem via the homogeneous-coordinate determinant bracket

## What This Proves
Two triangles `A B C` and `A' B' C'` in the real projective plane are **perspective
from a point** (the three lines `A A'`, `B B'`, `C C'` are concurrent) **iff** they are
**perspective from a line** (the three intersection points of corresponding sides

  `P = BC ∩ B'C'`,  `Q = CA ∩ C'A'`,  `R = AB ∩ A'B'`

are collinear). This is **Desargues's theorem**, the foundational incidence theorem of
projective geometry.

Open question: `menelaus-theorem-oq-01-oq-02`.
Parent: `Proofs/MenelausTheorem.lean` (`menelaus-theorem-oq-01`), whose mathematical
heart is the *collinearity-via-determinant factorisation* `collinearDet_factor`. This
file reuses exactly that idea — encode incidence by the vanishing of a determinant — but
lifts it to **homogeneous coordinates** `ℝ³`, where the parallel-line degeneracies of the
affine plane disappear and the whole theorem collapses to a single polynomial identity.

## Approach
Work in `ℝ³` with the standard projective dictionary:

* a point is a nonzero vector `P : ℝ³`;
* `cross P Q` (the vector cross product) is simultaneously the **line through** two
  points and the **intersection** of two lines (point/line duality);
* three points/lines are **collinear/concurrent** iff their `3×3` determinant `det3`
  vanishes.

Under this dictionary the two perspectivity conditions are
`det3 (A×A') (B×B') (C×C') = 0` (concurrence) and `det3 P Q R = 0` (collinearity), and
the entire content of Desargues is the **bracket identity**

  `det3 P Q R = det3 A B C · det3 A' B' C' · det3 (A×A') (B×B') (C×C')`,

a pure degree-`12` polynomial identity in the `18` coordinates, discharged by `ring`
(`desargues_bracket_identity`). For non-degenerate triangles the two triangle brackets
`det3 A B C` and `det3 A' B' C'` are nonzero, so the collinearity determinant vanishes
**iff** the concurrence determinant does — which is Desargues, and is manifestly
**self-dual**.

## Status
- [x] Cross product / `3×3` determinant in homogeneous coordinates
- [x] The Desargues bracket identity (the geometric content)
- [x] Main equivalence: perspective from a point ↔ perspective from a line
- [x] Self-duality corollary and a concrete numerical instance
- [x] 0 sorries, 0 axioms

## Mathlib Dependencies
Real arithmetic, `ring`, `mul_eq_zero`. Desargues's theorem is **not** a named Mathlib
result, nor is the projective cross-product bracket calculus used here.
-/

namespace MenelausTheoremOQ01OQ02

set_option linter.unusedVariables false

/-- A homogeneous-coordinate vector in the real projective plane. Components are
    accessed as `P.1`, `P.2.1`, `P.2.2`. -/
abbrev Vec : Type := ℝ × ℝ × ℝ

/-- The vector cross product. In the projective dictionary it is **both** the line
    joining two points **and** the intersection of two lines (point/line duality). -/
def cross (P Q : Vec) : Vec :=
  (P.2.1 * Q.2.2 - P.2.2 * Q.2.1,
   P.2.2 * Q.1 - P.1 * Q.2.2,
   P.1 * Q.2.1 - P.2.1 * Q.1)

/-- The `3×3` determinant (scalar triple product) `P · (Q × R)`. It vanishes exactly
    when the three points are collinear / the three lines are concurrent. -/
def det3 (P Q R : Vec) : ℝ :=
  P.1 * (Q.2.1 * R.2.2 - Q.2.2 * R.2.1)
    - P.2.1 * (Q.1 * R.2.2 - Q.2.2 * R.1)
    + P.2.2 * (Q.1 * R.2.1 - Q.2.1 * R.1)

/-- Two triangles `A B C`, `A' B' C'` in the projective plane, both non-degenerate
    (their vertices are not collinear). -/
structure DesarguesConfig where
  A : Vec
  B : Vec
  C : Vec
  A' : Vec
  B' : Vec
  C' : Vec
  hABC : det3 A B C ≠ 0
  hA'B'C' : det3 A' B' C' ≠ 0

namespace DesarguesConfig

variable (cfg : DesarguesConfig)

/-- Intersection of corresponding sides `BC` and `B'C'`. -/
def pointP : Vec := cross (cross cfg.B cfg.C) (cross cfg.B' cfg.C')

/-- Intersection of corresponding sides `CA` and `C'A'`. -/
def pointQ : Vec := cross (cross cfg.C cfg.A) (cross cfg.C' cfg.A')

/-- Intersection of corresponding sides `AB` and `A'B'`. -/
def pointR : Vec := cross (cross cfg.A cfg.B) (cross cfg.A' cfg.B')

/-- Concurrence determinant of the three connector lines `A A'`, `B B'`, `C C'`. -/
def concurDet : ℝ :=
  det3 (cross cfg.A cfg.A') (cross cfg.B cfg.B') (cross cfg.C cfg.C')

/-- Collinearity determinant of the three side-intersection points `P`, `Q`, `R`. -/
def collDet : ℝ := det3 cfg.pointP cfg.pointQ cfg.pointR

/-- The triangles are **perspective from a point**: the connectors `A A'`, `B B'`,
    `C C'` meet in a common point (their concurrence determinant vanishes). -/
def PerspectiveFromPoint : Prop := cfg.concurDet = 0

/-- The triangles are **perspective from a line**: the side-intersections `P`, `Q`, `R`
    are collinear (their determinant vanishes). -/
def PerspectiveFromLine : Prop := cfg.collDet = 0

end DesarguesConfig

open DesarguesConfig

/-- **The Desargues bracket identity** — the geometric content of the theorem.
    The collinearity determinant of the three side-intersection points factors as the
    product of the two triangle determinants and the concurrence determinant. A pure
    degree-`12` polynomial identity in the `18` coordinates, discharged by `ring`. -/
theorem desargues_bracket_identity (cfg : DesarguesConfig) :
    cfg.collDet = det3 cfg.A cfg.B cfg.C * det3 cfg.A' cfg.B' cfg.C' * cfg.concurDet := by
  simp only [DesarguesConfig.collDet, DesarguesConfig.concurDet, DesarguesConfig.pointP,
    DesarguesConfig.pointQ, DesarguesConfig.pointR, det3, cross]
  ring

/-- **Desargues's Theorem.** For two non-degenerate triangles, perspective from a point
    is equivalent to perspective from a line. The proof reads the equivalence directly
    off the bracket identity: dividing out the two nonzero triangle determinants, the
    collinearity determinant vanishes iff the concurrence determinant does. -/
theorem desargues (cfg : DesarguesConfig) :
    cfg.PerspectiveFromPoint ↔ cfg.PerspectiveFromLine := by
  have key := desargues_bracket_identity cfg
  unfold DesarguesConfig.PerspectiveFromPoint DesarguesConfig.PerspectiveFromLine
  constructor
  · intro h
    rw [key, h, mul_zero]
  · intro h
    rw [key] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with ha | hb
      · exact absurd ha cfg.hABC
      · exact absurd hb cfg.hA'B'C'
    · exact h2

/-- Perspective from a point implies perspective from a line. -/
theorem perspectiveFromLine_of_point (cfg : DesarguesConfig)
    (h : cfg.PerspectiveFromPoint) : cfg.PerspectiveFromLine :=
  (desargues cfg).mp h

/-- Perspective from a line implies perspective from a point. -/
theorem perspectiveFromPoint_of_line (cfg : DesarguesConfig)
    (h : cfg.PerspectiveFromLine) : cfg.PerspectiveFromPoint :=
  (desargues cfg).mpr h

/-- **Self-duality of Desargues.** Swapping points for lines (the two perspectivity
    conditions) leaves the theorem unchanged: each direction is the converse of the
    other. Stated here as the symmetric biconditional `point ↔ line`. -/
theorem desargues_self_dual (cfg : DesarguesConfig) :
    (cfg.PerspectiveFromPoint ↔ cfg.PerspectiveFromLine)
      ∧ (cfg.PerspectiveFromLine ↔ cfg.PerspectiveFromPoint) :=
  ⟨desargues cfg, (desargues cfg).symm⟩

/-- A concrete instance. With centre `(0,0,1)` and the three connectors taken along the
    `x`-axis, the `y`-axis, and the line `y = x`, the triangles
    `A=(1,0,1), B=(0,1,1), C=(1,1,1)` and `A'=(3,0,1), B'=(0,2,1), C'=(2,2,1)` are
    perspective from that point; Desargues then forces the three side-intersections to be
    collinear. -/
theorem desargues_example :
    ∃ cfg : DesarguesConfig, cfg.PerspectiveFromPoint ∧ cfg.PerspectiveFromLine := by
  refine ⟨{ A := (1, 0, 1), B := (0, 1, 1), C := (1, 1, 1),
            A' := (3, 0, 1), B' := (0, 2, 1), C' := (2, 2, 1),
            hABC := by norm_num [det3], hA'B'C' := by norm_num [det3] }, ?_, ?_⟩
  · show concurDet _ = 0
    norm_num [DesarguesConfig.concurDet, det3, cross]
  · apply perspectiveFromLine_of_point
    show concurDet _ = 0
    norm_num [DesarguesConfig.concurDet, det3, cross]

end MenelausTheoremOQ01OQ02
