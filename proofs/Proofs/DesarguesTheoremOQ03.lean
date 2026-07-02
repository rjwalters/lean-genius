import Mathlib

/-!
# Desargues's Theorem — OQ-03: Projective Invariance and the Fundamental Theorem

Parent: `Proofs/DesarguesTheorem.lean` (Desargues in homogeneous ℝ³ coordinates).

## Context

The parent entry formalizes Desargues's theorem in homogeneous coordinates: projective
points are nonzero vectors in ℝ³, three points are **collinear** iff the `3×3` matrix of
their coordinates is singular (`det = 0`), and three lines are **concurrent** iff their
coefficient vectors are singular (same `det = 0` condition).

The **Fundamental Theorem of Projective Geometry** says that the incidence-preserving
transformations of a projective space of dimension `≥ 2` are exactly the projective
(semilinear) maps. Its full statement is far beyond current Mathlib, but its concrete
algebraic engine — *invertible linear maps preserve the incidence relations* — is
elementary and is what this file supplies, axiom-free:

  `det [M·p, M·q, M·r] = det M · det [p, q, r]`,

so a linear map `M` preserves collinearity (and concurrence, the same determinant
condition), and when `M ∈ GL₃(ℝ)` (i.e. `det M ≠ 0`) it preserves *and reflects* them —
it is a genuine **collineation**. Consequently the entire Desargues configuration is
invariant under the projective linear group: this is why Desargues's theorem is a
statement of *projective* geometry, independent of any choice of coordinates.

## Results (axiom-free)

* `det_rowMatrix_mulVec` — `det [M·p, M·q, M·r] = det M · det [p, q, r]`.
* `Collinear` / `Concurrent` — the determinant incidence predicates.
* `collinear_map`, `concurrent_map` — any linear `M` preserves collinearity/concurrence.
* `collinear_map_iff`, `concurrent_map_iff` — an invertible `M` (`det M ≠ 0`) *reflects*
  them: it is a collineation.
* `collinear_self`, `collinear_comm` — basic incidence lemmas.
* `desargues_config_invariant` — the Desargues data (three concurrent joining lines and
  three collinear intersection points) transports along any invertible `M`.

## Status
Upper-level abstract FTPG (collineations ⇔ semilinear maps) needs projective-space
machinery Mathlib lacks and stays open; the linear-invariance core is fully proved here,
`0` axioms, `0` sorries.
-/

open Matrix

namespace DesarguesTheoremOQ03

/-- A projective point / line, as a homogeneous coordinate vector in `ℝ³`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `3×3` matrix whose rows are `p`, `q`, `r`. -/
def rowMatrix (p q r : Vec) : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![p, q, r]

/-- Three points are **collinear** iff their coordinate matrix is singular. -/
def Collinear (p q r : Vec) : Prop := (rowMatrix p q r).det = 0

/-- Three lines are **concurrent** iff their coefficient matrix is singular
    (the same determinant condition, by projective duality). -/
def Concurrent (l m n : Vec) : Prop := (rowMatrix l m n).det = 0

-- ============================================================================
-- The determinant transformation law (the algebraic core of FTPG)
-- ============================================================================

/-- **The determinant transformation law.** Applying a linear map `M` to each of the
three rows scales the determinant by `det M`:
`det [M·p, M·q, M·r] = det M · det [p, q, r]`.

Proof: the matrix with rows `M·p, M·q, M·r` is `(rowMatrix p q r) · Mᵀ`, and
`det (A · Mᵀ) = det A · det Mᵀ = det A · det M`. -/
theorem det_rowMatrix_mulVec (M : Matrix (Fin 3) (Fin 3) ℝ) (p q r : Vec) :
    (rowMatrix (M.mulVec p) (M.mulVec q) (M.mulVec r)).det = M.det * (rowMatrix p q r).det := by
  have hmat : rowMatrix (M.mulVec p) (M.mulVec q) (M.mulVec r) = rowMatrix p q r * Mᵀ := by
    ext i j
    fin_cases i <;>
      simp [rowMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        mul_comm]
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, mul_comm]

-- ============================================================================
-- Linear maps preserve incidence; invertible maps reflect it (collineations)
-- ============================================================================

/-- **Any linear map preserves collinearity.** -/
theorem collinear_map (M : Matrix (Fin 3) (Fin 3) ℝ) {p q r : Vec} (h : Collinear p q r) :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) := by
  unfold Collinear at *
  rw [det_rowMatrix_mulVec, h, mul_zero]

/-- **Any linear map preserves concurrence.** -/
theorem concurrent_map (M : Matrix (Fin 3) (Fin 3) ℝ) {l m n : Vec} (h : Concurrent l m n) :
    Concurrent (M.mulVec l) (M.mulVec m) (M.mulVec n) := by
  unfold Concurrent at *
  rw [det_rowMatrix_mulVec, h, mul_zero]

/-- **An invertible map reflects collinearity** (`det M ≠ 0`): the image is collinear iff
the source is. So `M` is a genuine collineation. -/
theorem collinear_map_iff {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det ≠ 0) (p q r : Vec) :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) ↔ Collinear p q r := by
  unfold Collinear
  rw [det_rowMatrix_mulVec]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hM
    · exact h'
  · intro h; rw [h, mul_zero]

/-- **An invertible map reflects concurrence** (`det M ≠ 0`). -/
theorem concurrent_map_iff {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det ≠ 0) (l m n : Vec) :
    Concurrent (M.mulVec l) (M.mulVec m) (M.mulVec n) ↔ Concurrent l m n :=
  collinear_map_iff hM l m n

-- ============================================================================
-- Basic incidence lemmas
-- ============================================================================

/-- A repeated point is always collinear with anything (a degenerate row). -/
theorem collinear_self (p q : Vec) : Collinear p p q := by
  simp only [Collinear, rowMatrix, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- Collinearity is symmetric in its first two arguments (swapping two rows negates the
determinant, and `0` is fixed). -/
theorem collinear_comm {p q r : Vec} (h : Collinear p q r) : Collinear q p r := by
  simp only [Collinear, rowMatrix, Matrix.det_fin_three, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at h ⊢
  linear_combination -h

-- ============================================================================
-- The Desargues configuration is projectively invariant
-- ============================================================================

/-- **Projective invariance of the Desargues configuration.** For an invertible `M`
(`det M ≠ 0`), the two incidence facts that make up Desargues's theorem — the three
joining lines being concurrent, and the three intersection points being collinear — both
transport along `M` in each direction. Hence Desargues's theorem, phrased in these
coordinates, is a coordinate-free statement invariant under the projective linear group. -/
theorem desargues_config_invariant {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.det ≠ 0)
    (lAA' lBB' lCC' P Q R : Vec) :
    (Concurrent (M.mulVec lAA') (M.mulVec lBB') (M.mulVec lCC') ↔ Concurrent lAA' lBB' lCC')
      ∧ (Collinear (M.mulVec P) (M.mulVec Q) (M.mulVec R) ↔ Collinear P Q R) :=
  ⟨concurrent_map_iff hM lAA' lBB' lCC', collinear_map_iff hM P Q R⟩

end DesarguesTheoremOQ03
