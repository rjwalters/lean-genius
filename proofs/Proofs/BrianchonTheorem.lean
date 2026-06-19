import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-
# Brianchon's Theorem — proved as the projective dual of Pascal's theorem

## What This Proves

Brianchon's theorem: if a hexagon is *circumscribed* about a conic (each of its
six sides is tangent to the conic), then the three main diagonals joining
opposite vertices are concurrent.  This is the projective dual of Pascal's
hexagon theorem (`PascalsHexagon.lean`).

## The mathematical content

The deep geometric fact behind Pascal's theorem (six points on a conic ⟹ the
three intersections of opposite sides are collinear) is, as in the gallery's
`PascalsHexagon.lean`, taken as the single axiom `conic_implies_pascal`.

The new content here is the **pole–polar duality bridge**
`concurrent_brianchon_of_collinear_pascal`, which is proved with **no axioms and
no `sorry`**: it shows that, purely by linear algebra, Pascal's "three points
collinear" forces Brianchon's "three lines concurrent".  Brianchon's theorem
then follows by feeding Pascal's axiom into this bridge, introducing no new
assumption beyond the one Pascal already needs.

## The duality, in coordinates

Points and lines are nonzero vectors in `ℝ³`; the join of two points / meet of
two lines is the cross product; three points are collinear (resp. three lines
concurrent) iff the `3×3` determinant of their coordinate vectors vanishes.

For a symmetric conic `C` (a symmetric `3×3` matrix) the polarity `P ↦ C · P`
sends a point `P` on the conic to the tangent line of `C` at `P`.  A hexagon
circumscribed about `C` is therefore the dual of an inscribed hexagon whose
vertices `A, …, F` are the six contact points: its sides are the tangent lines
`C·A, …, C·F`, and its vertices are the meets of consecutive sides.

The bridge rests on two computational facts (proved below by `ring`):

* `crossProduct_mulMatrix` :
  `(M·u) × (M·v) = (adjugate M)ᵀ · (u × v)`              (the cofactor identity),
* `det_threeVectorMatrix_mulMatrix` :
  `det (M·u, M·v, M·w) = det M · det (u, v, w)`.

Applying the first twice (with `M = C`, then `M = adjugate C`) and using
`adjugate (adjugate C) = det C • C` (true for `3×3`), each Brianchon diagonal
equals `(det C • C)` applied to the corresponding Pascal point.  The second fact
then turns Pascal's vanishing determinant into Brianchon's.

## Status

`status: axiomatized` — the unconditional `brianchon_theorem` relies on exactly
one axiom, `conic_implies_pascal` (the *same* fact axiomatized by the Pascal
gallery entry), and on no others.  The duality bridge
`concurrent_brianchon_of_collinear_pascal` is axiom-free and `sorry`-free.
-/

set_option linter.unusedVariables false

open Matrix

namespace Brianchon

-- ============================================================
-- PART 1: Projective model (homogeneous coordinates in ℝ³)
-- ============================================================

/-- A projective point: a (nonzero) vector in `ℝ³`. -/
abbrev ProjPoint := Fin 3 → ℝ

/-- A projective line: a (nonzero) covector in `ℝ³`. -/
abbrev ProjLine := Fin 3 → ℝ

/-- The line through two points is their cross product. -/
noncomputable def lineThrough (p q : ProjPoint) : ProjLine := crossProduct p q

/-- The meet of two lines is their cross product. -/
noncomputable def lineIntersection (l m : ProjLine) : ProjPoint := crossProduct l m

/-- The `3×3` matrix whose rows are the three given vectors. -/
def threeVectorMatrix (u v w : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

/-- Three points are collinear iff their coordinate determinant vanishes. -/
def collinear (p q r : ProjPoint) : Prop := (threeVectorMatrix p q r).det = 0

/-- Three lines are concurrent iff their coefficient determinant vanishes. -/
def concurrent (l m n : ProjLine) : Prop := (threeVectorMatrix l m n).det = 0

/-- A conic is a symmetric `3×3` matrix `C`; a point `p` lies on it iff
`pᵀ C p = 0`. -/
abbrev Conic := Matrix (Fin 3) (Fin 3) ℝ

/-- The conic's quadratic form `pᵀ C p`. -/
noncomputable def conicQuadraticForm (C : Conic) (p : ProjPoint) : ℝ :=
  ∑ i, ∑ j, C i j * p i * p j

/-- A point lies on a conic iff its quadratic form vanishes. -/
def pointOnConic (p : ProjPoint) (C : Conic) : Prop := conicQuadraticForm C p = 0

/-- `C` is symmetric (`Cᵢⱼ = Cⱼᵢ`). -/
def Conic.symmetric (C : Conic) : Prop := ∀ i j, C i j = C j i

/-- Apply a matrix to a projective point (a projective transformation when the
matrix is invertible). -/
def mapPoint (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint := M *ᵥ p

-- ============================================================
-- PART 2: The two computational identities
-- ============================================================

set_option maxHeartbeats 2000000 in
/-- **Cofactor / Binet–Cauchy identity for the cross product.**
`(M·u) × (M·v) = (adjugate M)ᵀ · (u × v)`.  This is the algebraic heart of
pole–polar duality: the join/meet operation intertwines the point map `M` with
the line map `(adjugate M)ᵀ` (the cofactor matrix). -/
theorem crossProduct_mulMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (u v : Fin 3 → ℝ) :
    crossProduct (M *ᵥ u) (M *ᵥ v) = (M.adjugate)ᵀ *ᵥ (crossProduct u v) := by
  ext i
  fin_cases i <;>
    simp only [cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue,
      Matrix.adjugate_fin_three, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.reduceFinMk] <;>
    ring

/-- Applying a fixed matrix `M` to the three rows multiplies the
`threeVectorMatrix` determinant by `det M`.  Hence collinearity/concurrency is
governed by `det M`: in particular a vanishing source determinant forces a
vanishing target determinant. -/
theorem det_threeVectorMatrix_mulMatrix (M : Matrix (Fin 3) (Fin 3) ℝ) (u v w : Fin 3 → ℝ) :
    (threeVectorMatrix (M *ᵥ u) (M *ᵥ v) (M *ᵥ w)).det
      = M.det * (threeVectorMatrix u v w).det := by
  have h : threeVectorMatrix (M *ᵥ u) (M *ᵥ v) (M *ᵥ w) = threeVectorMatrix u v w * Mᵀ := by
    ext i j
    fin_cases i <;>
      simp only [threeVectorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.mulVec, dotProduct, Fin.sum_univ_three, Fin.isValue] <;>
      ring
  rw [h, Matrix.det_mul, Matrix.det_transpose]
  ring

-- ============================================================
-- PART 3: Symmetric-conic bookkeeping
-- ============================================================

/-- A symmetric matrix equals its own transpose. -/
theorem transpose_of_symmetric {C : Conic} (hC : C.symmetric) : Cᵀ = C := by
  ext i j
  exact hC j i

/-- The adjugate of a symmetric matrix is symmetric. -/
theorem adjugate_symmetric {C : Conic} (hC : C.symmetric) : (C.adjugate)ᵀ = C.adjugate := by
  rw [Matrix.adjugate_transpose, transpose_of_symmetric hC]

/-- For a symmetric `3×3` conic, the iterated cofactor matrix `((adj C)ᵀ adj)ᵀ`
collapses to the single linear map `det C • C`. -/
theorem dual_matrix_eq {C : Conic} (hC : C.symmetric) :
    ((C.adjugate)ᵀ.adjugate)ᵀ = C.det • C := by
  rw [adjugate_symmetric hC, Matrix.adjugate_adjugate _ (by decide : Fintype.card (Fin 3) ≠ 1),
    Matrix.transpose_smul, transpose_of_symmetric hC]
  simp [Fintype.card_fin]

-- ============================================================
-- PART 4: The circumscribed hexagon (dual configuration)
-- ============================================================

/-- The tangent line of the conic `C` at a contact point `P` lying on `C` is the
polar line `C ·ᵥ P`. -/
noncomputable def tangentLine (C : Conic) (P : ProjPoint) : ProjLine := mapPoint C P

/-- A vertex of the circumscribed hexagon: the meet of the tangent lines at two
contact points (the intersection of two adjacent sides). -/
noncomputable def circVertex (C : Conic) (P Q : ProjPoint) : ProjPoint :=
  lineIntersection (tangentLine C P) (tangentLine C Q)

-- ============================================================
-- PART 5: Each diagonal is the dual image of a Pascal point
-- ============================================================

/-- **Key reduction lemma.**  A circumscribed-hexagon diagonal
`lineThrough (circVertex C P Q) (circVertex C R S)` equals the fixed linear map
`det C • C` applied to the corresponding Pascal point
`lineIntersection (lineThrough P Q) (lineThrough R S)`. -/
theorem diag_eq {C : Conic} (hC : C.symmetric) (P Q R S : ProjPoint) :
    lineThrough (circVertex C P Q) (circVertex C R S)
      = (C.det • C) *ᵥ lineIntersection (lineThrough P Q) (lineThrough R S) := by
  unfold circVertex tangentLine mapPoint lineThrough lineIntersection
  -- Apply the cofactor identity bottom-up: inner meets first, then the outer join.
  simp only [crossProduct_mulMatrix]
  rw [dual_matrix_eq hC]

-- ============================================================
-- PART 6: The axiom-free duality bridge
-- ============================================================

/-- **Brianchon ⇐ Pascal (axiom-free duality bridge).**

For a symmetric conic `C` with six contact points `A, B, C', D, E, F`: if the
three Pascal points (intersections of opposite sides of the *inscribed* hexagon
of contact points) are collinear, then the three main diagonals of the
*circumscribed* hexagon are concurrent.

This is the projective duality between Pascal and Brianchon, made completely
explicit.  It is proved with **no axioms and no `sorry`** — it is pure linear
algebra: each diagonal is `(det C • C)` applied to a Pascal point, and applying
a fixed matrix scales the triple determinant by its own determinant. -/
theorem concurrent_brianchon_of_collinear_pascal {C : Conic} (hC : C.symmetric)
    (A B C' D E F : ProjPoint)
    (hPascal : collinear
      (lineIntersection (lineThrough A B) (lineThrough D E))
      (lineIntersection (lineThrough B C') (lineThrough E F))
      (lineIntersection (lineThrough C' D) (lineThrough F A))) :
    concurrent
      (lineThrough (circVertex C A B) (circVertex C D E))
      (lineThrough (circVertex C B C') (circVertex C E F))
      (lineThrough (circVertex C C' D) (circVertex C F A)) := by
  unfold concurrent
  rw [diag_eq hC, diag_eq hC, diag_eq hC, det_threeVectorMatrix_mulMatrix]
  unfold collinear at hPascal
  rw [hPascal, mul_zero]

-- ============================================================
-- PART 7: The circumscribed hexagon of contact points + Pascal's axiom
-- ============================================================

/-- Six contact points on a conic `C` (the points where the six sides of a
circumscribed hexagon touch `C`).  Equivalently, an inscribed hexagon whose
projective dual is the circumscribed hexagon of Brianchon's theorem. -/
structure ContactHexagon (C : Conic) where
  A : ProjPoint
  B : ProjPoint
  C' : ProjPoint
  D : ProjPoint
  E : ProjPoint
  F : ProjPoint
  hA : pointOnConic A C
  hB : pointOnConic B C
  hC : pointOnConic C' C
  hD : pointOnConic D C
  hE : pointOnConic E C
  hF : pointOnConic F C

/-- **Pascal's hexagon theorem (axiomatized).**  Six points on a conic make the
three intersections of opposite sides collinear.  This is exactly the deep fact
the gallery's `PascalsHexagon.lean` axiomatizes as `conic_implies_pascal_constraint`;
we restate it here in collinearity form and reuse it unchanged. -/
axiom conic_implies_pascal (C : Conic) (hex : ContactHexagon C) :
    collinear
      (lineIntersection (lineThrough hex.A hex.B) (lineThrough hex.D hex.E))
      (lineIntersection (lineThrough hex.B hex.C') (lineThrough hex.E hex.F))
      (lineIntersection (lineThrough hex.C' hex.D) (lineThrough hex.F hex.A))

-- ============================================================
-- PART 8: Brianchon's Theorem
-- ============================================================

/-- First main diagonal of the circumscribed hexagon. -/
noncomputable def brianchonDiag1 {C : Conic} (hex : ContactHexagon C) : ProjLine :=
  lineThrough (circVertex C hex.A hex.B) (circVertex C hex.D hex.E)

/-- Second main diagonal of the circumscribed hexagon. -/
noncomputable def brianchonDiag2 {C : Conic} (hex : ContactHexagon C) : ProjLine :=
  lineThrough (circVertex C hex.B hex.C') (circVertex C hex.E hex.F)

/-- Third main diagonal of the circumscribed hexagon. -/
noncomputable def brianchonDiag3 {C : Conic} (hex : ContactHexagon C) : ProjLine :=
  lineThrough (circVertex C hex.C' hex.D) (circVertex C hex.F hex.A)

/-- **Brianchon's Theorem** (projective dual of Pascal's hexagon theorem).

Let `C` be a symmetric conic and let a hexagon be circumscribed about `C`, its
six sides being the tangent lines of `C` at six contact points
`A, B, C', D, E, F` on `C`.  Then the three main diagonals of the circumscribed
hexagon are concurrent.

The proof combines Pascal's theorem (the shared axiom) with the axiom-free
duality bridge `concurrent_brianchon_of_collinear_pascal`.  It uses **no axiom
beyond** `conic_implies_pascal`, the same fact the Pascal gallery entry assumes. -/
theorem brianchon_theorem {C : Conic} (hC : C.symmetric) (hex : ContactHexagon C) :
    concurrent (brianchonDiag1 hex) (brianchonDiag2 hex) (brianchonDiag3 hex) :=
  concurrent_brianchon_of_collinear_pascal hC hex.A hex.B hex.C' hex.D hex.E hex.F
    (conic_implies_pascal C hex)

end Brianchon
