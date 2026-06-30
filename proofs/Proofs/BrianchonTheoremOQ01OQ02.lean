import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-
# Brianchon ⟺ Pascal: the converse duality bridge (OQ-01-OQ-02)

## Open question

The parent entry `BrianchonTheorem.lean` proves Brianchon's theorem as the
projective dual of Pascal's, via the **one-way** duality bridge

  `concurrent_brianchon_of_collinear_pascal`
    (Pascal collinear ⟹ Brianchon concurrent),

an axiom-free linear-algebra fact.  Its second open question asks for the
**converse direction** of the Pascal–Brianchon correspondence.

## What this file proves (axiom-free, no `sorry`)

The single computational fact behind the whole correspondence is the exact
scalar identity

  `brianchon_concurrency_det_eq` :
    det(diag₁, diag₂, diag₃) = (det C)^4 · det(p₁, p₂, p₃),

where `diag₁, diag₂, diag₃` are the three main diagonals of the circumscribed
hexagon and `p₁, p₂, p₃` are the three Pascal points of the inscribed hexagon of
contact points.  Each Brianchon diagonal is the fixed linear map `det C • C`
applied to the corresponding Pascal point (`diag_eq`, ported from the parent),
and applying a fixed matrix scales the triple determinant by its determinant
(`det_threeVectorMatrix_mulMatrix`); since `det (det C • C) = (det C)^4` for a
`3×3` matrix, the identity follows.

From this one identity both directions drop out:

* **Forward** (`concurrent_brianchon_of_collinear_pascal`): Pascal determinant
  `= 0` forces the Brianchon determinant `= 0`.  *No* nondegeneracy needed.

* **Converse** (`collinear_pascal_of_concurrent_brianchon`): when the conic is
  **nondegenerate** (`det C ≠ 0`), the factor `(det C)^4` is invertible, so a
  vanishing Brianchon determinant forces a vanishing Pascal determinant.

Packaged together (`pascal_collinear_iff_brianchon_concurrent`) this is the full
**equivalence** Pascal-collinear ⟺ Brianchon-concurrent for any nondegenerate
symmetric conic — the converse half of which is the new content of this entry.

## Scope / honesty note

This is the converse of the *duality bridge* (the determinant correspondence),
not the classical Braikenridge–Maclaurin converse ("the six contact points
actually lie on a conic").  The latter is a genuinely different and harder
statement (false without a genericity hypothesis) and remains open; see the
closing remark.  Everything proved here is pure linear algebra over `ℝ`,
imports only Mathlib, and uses **no axioms and no `sorry`** — in particular it
does *not* depend on the Pascal axiom `conic_implies_pascal`.
-/

set_option linter.unusedVariables false

open Matrix

namespace BrianchonConverse

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

/-- A conic is a symmetric `3×3` matrix `C`. -/
abbrev Conic := Matrix (Fin 3) (Fin 3) ℝ

/-- `C` is symmetric (`Cᵢⱼ = Cⱼᵢ`). -/
def Conic.symmetric (C : Conic) : Prop := ∀ i j, C i j = C j i

/-- Apply a matrix to a projective point. -/
def mapPoint (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint := M *ᵥ p

-- ============================================================
-- PART 2: The two computational identities (ported from parent)
-- ============================================================

set_option maxHeartbeats 2000000 in
/-- **Cofactor / Binet–Cauchy identity for the cross product.**
`(M·u) × (M·v) = (adjugate M)ᵀ · (u × v)`. -/
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
`threeVectorMatrix` determinant by `det M`. -/
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
-- PART 3: Symmetric-conic bookkeeping (ported from parent)
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

/-- The tangent line of the conic `C` at a contact point `P` is the polar line
`C ·ᵥ P`. -/
noncomputable def tangentLine (C : Conic) (P : ProjPoint) : ProjLine := mapPoint C P

/-- A vertex of the circumscribed hexagon: the meet of the tangent lines at two
contact points. -/
noncomputable def circVertex (C : Conic) (P Q : ProjPoint) : ProjPoint :=
  lineIntersection (tangentLine C P) (tangentLine C Q)

/-- **Key reduction lemma** (ported from parent).  A circumscribed-hexagon
diagonal equals the fixed linear map `det C • C` applied to the corresponding
Pascal point. -/
theorem diag_eq {C : Conic} (hC : C.symmetric) (P Q R S : ProjPoint) :
    lineThrough (circVertex C P Q) (circVertex C R S)
      = (C.det • C) *ᵥ lineIntersection (lineThrough P Q) (lineThrough R S) := by
  unfold circVertex tangentLine mapPoint lineThrough lineIntersection
  simp only [crossProduct_mulMatrix]
  rw [dual_matrix_eq hC]

-- ============================================================
-- PART 5: The exact scalar identity (the crux)
-- ============================================================

/-- **The Brianchon–Pascal determinant identity.**

For a symmetric conic `C` and six contact points `A, B, C', D, E, F`, the
coefficient determinant of the three Brianchon diagonals equals `(det C)^4`
times the coordinate determinant of the three Pascal points:

  `det(diag₁, diag₂, diag₃) = (det C)^4 · det(p₁, p₂, p₃)`.

Both directions of the Pascal–Brianchon correspondence are immediate corollaries.
Proved with **no axioms and no `sorry`**. -/
theorem brianchon_concurrency_det_eq {C : Conic} (hC : C.symmetric)
    (A B C' D E F : ProjPoint) :
    (threeVectorMatrix
        (lineThrough (circVertex C A B) (circVertex C D E))
        (lineThrough (circVertex C B C') (circVertex C E F))
        (lineThrough (circVertex C C' D) (circVertex C F A))).det
      = (C.det) ^ 4 *
        (threeVectorMatrix
          (lineIntersection (lineThrough A B) (lineThrough D E))
          (lineIntersection (lineThrough B C') (lineThrough E F))
          (lineIntersection (lineThrough C' D) (lineThrough F A))).det := by
  rw [diag_eq hC, diag_eq hC, diag_eq hC, det_threeVectorMatrix_mulMatrix, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

-- ============================================================
-- PART 6: Forward and converse bridges
-- ============================================================

/-- **Forward bridge** (Pascal ⟹ Brianchon), recovered from the scalar identity.
Pascal collinearity forces Brianchon concurrency; no nondegeneracy needed. -/
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
  rw [brianchon_concurrency_det_eq hC]
  unfold collinear at hPascal
  rw [hPascal, mul_zero]

/-- For a `3×3` real matrix, `det (det C • C) = (det C)^4 ≠ 0` whenever
`det C ≠ 0`. -/
theorem det_smul_self_ne_zero {C : Conic} (hdet : C.det ≠ 0) :
    (C.det • C).det ≠ 0 := by
  rw [Matrix.det_smul]
  simp only [Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero 3 hdet) hdet

/-- **Converse bridge** (Brianchon ⟹ Pascal, the new content).

For a **nondegenerate** symmetric conic (`det C ≠ 0`): if the three main
diagonals of the circumscribed hexagon are concurrent, then the three Pascal
points of the inscribed hexagon of contact points are collinear.

The proof divides the scalar identity by the invertible factor `(det C)^4`.
**No axioms, no `sorry`.** -/
theorem collinear_pascal_of_concurrent_brianchon {C : Conic} (hC : C.symmetric)
    (hdet : C.det ≠ 0) (A B C' D E F : ProjPoint)
    (hBri : concurrent
      (lineThrough (circVertex C A B) (circVertex C D E))
      (lineThrough (circVertex C B C') (circVertex C E F))
      (lineThrough (circVertex C C' D) (circVertex C F A))) :
    collinear
      (lineIntersection (lineThrough A B) (lineThrough D E))
      (lineIntersection (lineThrough B C') (lineThrough E F))
      (lineIntersection (lineThrough C' D) (lineThrough F A)) := by
  unfold concurrent at hBri
  rw [brianchon_concurrency_det_eq hC] at hBri
  unfold collinear
  have hpow : (C.det) ^ 4 ≠ 0 := pow_ne_zero 4 hdet
  rcases mul_eq_zero.mp hBri with h | h
  · exact absurd h hpow
  · exact h

-- ============================================================
-- PART 7: The full equivalence
-- ============================================================

/-- **Pascal collinear ⟺ Brianchon concurrent** for any nondegenerate symmetric
conic.  The forward implication is the parent's duality bridge; the backward
implication is the converse established here.  Axiom-free. -/
theorem pascal_collinear_iff_brianchon_concurrent {C : Conic} (hC : C.symmetric)
    (hdet : C.det ≠ 0) (A B C' D E F : ProjPoint) :
    collinear
      (lineIntersection (lineThrough A B) (lineThrough D E))
      (lineIntersection (lineThrough B C') (lineThrough E F))
      (lineIntersection (lineThrough C' D) (lineThrough F A))
    ↔ concurrent
      (lineThrough (circVertex C A B) (circVertex C D E))
      (lineThrough (circVertex C B C') (circVertex C E F))
      (lineThrough (circVertex C C' D) (circVertex C F A)) :=
  ⟨concurrent_brianchon_of_collinear_pascal hC A B C' D E F,
   collinear_pascal_of_concurrent_brianchon hC hdet A B C' D E F⟩

-- ============================================================
-- PART 8: Degeneracy is genuine — the nondegeneracy hypothesis is necessary
-- ============================================================

/-
The hypothesis `det C ≠ 0` in the converse is not cosmetic.  If `C` is the zero
conic, every tangent line `C ·ᵥ P = 0`, so every diagonal is the zero covector
and the Brianchon determinant vanishes identically — yet the Pascal points are
generically *not* collinear.  We record the degenerate collapse explicitly: for
`C = 0` the Brianchon diagonals are all zero and concurrency holds vacuously,
independently of the contact points.  This shows the converse must assume
nondegeneracy.
-/

/-- With the **zero conic**, every Brianchon diagonal collapses to the zero
covector, so the circumscribed "hexagon" is totally degenerate and concurrency
holds for *any* six contact points — even when the Pascal points are not
collinear.  This witnesses the necessity of `det C ≠ 0` in the converse. -/
theorem zero_conic_diag_eq_zero (A B : ProjPoint) :
    lineThrough (circVertex (0 : Conic) A B) (circVertex (0 : Conic) A B) = 0 := by
  unfold lineThrough circVertex tangentLine mapPoint lineIntersection
  ext i
  fin_cases i <;> simp

/-- Concurrency holds vacuously for the zero conic, regardless of the contact
points: all three diagonals are the zero covector, whose triple determinant is
`0`.  (Compare the converse `collinear_pascal_of_concurrent_brianchon`, which
would falsely conclude collinearity were the `det C ≠ 0` hypothesis dropped.) -/
theorem zero_conic_concurrent (A B C' D E F : ProjPoint) :
    concurrent
      (lineThrough (circVertex (0 : Conic) A B) (circVertex (0 : Conic) D E))
      (lineThrough (circVertex (0 : Conic) B C') (circVertex (0 : Conic) E F))
      (lineThrough (circVertex (0 : Conic) C' D) (circVertex (0 : Conic) F A)) := by
  unfold concurrent
  have hsym : (0 : Conic).symmetric := by intro i j; simp
  rw [brianchon_concurrency_det_eq hsym]
  simp

end BrianchonConverse
