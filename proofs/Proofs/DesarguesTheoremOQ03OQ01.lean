import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-
# From PGL to PΓL: the semilinear group and frame rigidity (OQ-03-OQ-01)

Parent: `Proofs/DesarguesTheoremOQ03.lean` — *projective invariance of the Desargues
configuration under GL₃(ℝ)*.

## The follow-up question

The parent entry (OQ-03) proves the **linear** half of the algebraic engine behind the
Fundamental Theorem of Projective Geometry (FTPG): over `ℝ`, an invertible matrix `M`
acts on `PG(2, ℝ)` by a collineation, because
`det [M·p, M·q, M·r] = det M · det [p, q, r]`.
It explicitly leaves two things open:

1. the **semilinear** part — the FTPG identifies the *full* collineation group with
   `PΓL(3, K) = PGL(3, K) ⋊ Aut(K)`, not merely `PGL`; the field-automorphism twist is
   missing from OQ-03; and
2. the **rigidity** that gives the FTPG its force — a projective transformation is
   determined by its action on a projective *frame*.

This entry supplies both, and does so over an **arbitrary field `K`** (the coordinate
ring produced by Hilbert's coordinatization of any Desarguesian plane), tightening the
tie between Desargues and the FTPG.

## Why this is the right generalization

Desargues's theorem is exactly the synthetic hypothesis under which a projective plane
is coordinatizable as `PG(2, K)` for a division ring `K` (Hilbert). The FTPG then
describes the collineations of that coordinatized plane as `PΓL(3, K)`. Working over a
general field `K` (rather than only `ℝ`) is therefore not idle generality: it is the
natural home of the Desargues ⇒ coordinates ⇒ FTPG chain. Over `ℝ` the automorphism
group `Aut(ℝ)` is trivial, so the semilinear phenomenon is *invisible* — one must leave
`ℝ` to see the `Aut(K)` factor at all (e.g. `Aut(ℂ)` or `Aut(𝔽_{p^n})` are large).

## What is proved here (axiom-free, `0` sorries)

Points of `PG(2, K)` are nonzero vectors of `K³`; three of them are `Collinear` iff the
matrix with those rows is singular (`det = 0`) — the same incidence predicate as the
parent, now over `K`.

* **PGL(3, K) acts by collineations** (over any field):
  `rowMat_mulVec_det`, `collinear_mulVec`, `collinear_mulVec_iff`.
* **Aut(K) acts by collineations — the new semilinear part:**
  `collinear_semilinear` — a field endomorphism applied coordinatewise preserves
  collinearity.
* **PΓL(3, K) ⊆ Collineations — the constructive half of the FTPG:**
  `collinear_projSemilinear` — a linear map followed by a field automorphism (a
  projective *semilinear* map) preserves collinearity. This is the exact class of
  transformations the FTPG names.
* **Frame rigidity — the computational kernel of the FTPG:**
  `frame_general_position` — the standard frame `[1:0:0], [0:1:0], [0:0:1], [1:1:1]` is
  in general position (a genuine projective frame); and
  `frame_stabilizer_scalar` — a linear map fixing each frame point projectively is a
  *scalar* matrix. Equivalently the projective stabilizer of a frame in `PGL(3, K)` is
  trivial: **a projective transformation is uniquely determined by its action on a
  frame.**
* **Projective invariance of Desargues over `K`:**
  `desargues_relation_mulVec`, `desargues_relation_preserved` — the perspectivity
  relations (both `det = 0` conditions) transport along collineations, generalizing the
  parent's `ℝ`-only invariance to arbitrary fields.

## What stays open (the deep direction)

The hard converse `Collineations ⊆ PΓL(3, K)` — that *every* collineation is
semilinear — is the substantial content of the FTPG. It reconstructs the field
operations from incidence (again via Desargues) and is a large development; it is left
as the contextual open direction, not axiomatized. Everything below is fully proved.
-/

set_option linter.unusedVariables false

namespace DesarguesTheoremOQ03OQ01

open Matrix

variable {K : Type*} [Field K]

-- ============================================================
-- PART 1: The coordinatized plane PG(2,K)
-- ============================================================

/-- The 3×3 matrix formed by three vectors as its rows. -/
def rowMat (u v w : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j =>
    match i with
    | 0 => u j
    | 1 => v j
    | 2 => w j

/-- Explicit determinant of `rowMat`. -/
theorem rowMat_det (u v w : Fin 3 → K) :
    (rowMat u v w).det =
      u 0 * (v 1 * w 2 - v 2 * w 1) -
      u 1 * (v 0 * w 2 - v 2 * w 0) +
      u 2 * (v 0 * w 1 - v 1 * w 0) := by
  simp only [rowMat, Matrix.det_fin_three, Matrix.of_apply]
  ring

/-- Three projective points are **collinear** iff the determinant of the matrix with
those points as rows vanishes.  (Dually, three projective *lines* are **concurrent**
under the same predicate.) -/
def Collinear (p q r : Fin 3 → K) : Prop := (rowMat p q r).det = 0

-- ============================================================
-- PART 2: PGL(3,K) acts by collineations
-- ============================================================

/-- Stacking three `M`-transformed points as rows equals stacking the original points
and right-multiplying by `Mᵀ`. -/
theorem rowMat_mulVec (M : Matrix (Fin 3) (Fin 3) K) (p q r : Fin 3 → K) :
    rowMat (M.mulVec p) (M.mulVec q) (M.mulVec r) = rowMat p q r * Mᵀ := by
  ext i j
  fin_cases i <;>
    simp [rowMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, mul_comm]

/-- **Determinant multiplicativity of the linear action.**
The signed area (determinant) of three transformed points scales by `det M`. -/
theorem rowMat_mulVec_det (M : Matrix (Fin 3) (Fin 3) K) (p q r : Fin 3 → K) :
    (rowMat (M.mulVec p) (M.mulVec q) (M.mulVec r)).det
      = M.det * (rowMat p q r).det := by
  rw [rowMat_mulVec, Matrix.det_mul, Matrix.det_transpose, mul_comm]

/-- **PGL acts by collineations.** A linear map sends collinear points to collinear
points. -/
theorem collinear_mulVec (M : Matrix (Fin 3) (Fin 3) K) {p q r : Fin 3 → K}
    (h : Collinear p q r) :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) := by
  unfold Collinear at *
  rw [rowMat_mulVec_det, h, mul_zero]

/-- When `M` is invertible the linear action **reflects** collinearity as well:
`PGL(3, K)` acts on `PG(2, K)` by collineations. -/
theorem collinear_mulVec_iff (M : Matrix (Fin 3) (Fin 3) K) (hM : M.det ≠ 0)
    {p q r : Fin 3 → K} :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) ↔ Collinear p q r := by
  unfold Collinear
  rw [rowMat_mulVec_det]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hM
  · intro h; rw [h, mul_zero]

-- ============================================================
-- PART 3: Aut(K) acts by collineations — the semilinear part
-- ============================================================

/-- Applying a ring endomorphism `σ` coordinatewise to three points is the same as
mapping the stacked matrix through `σ`. -/
theorem rowMat_map (σ : K →+* K) (p q r : Fin 3 → K) :
    rowMat (fun i => σ (p i)) (fun i => σ (q i)) (fun i => σ (r i))
      = (rowMat p q r).map σ := by
  ext i j
  fin_cases i <;> simp [rowMat, Matrix.map_apply]

/-- **Aut(K) acts by collineations.** A field endomorphism applied coordinatewise — the
*semilinear* ingredient of `PΓL` that is invisible over `ℝ` — preserves collinearity. -/
theorem collinear_semilinear (σ : K →+* K) {p q r : Fin 3 → K}
    (h : Collinear p q r) :
    Collinear (fun i => σ (p i)) (fun i => σ (q i)) (fun i => σ (r i)) := by
  unfold Collinear at *
  rw [rowMat_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]

-- ============================================================
-- PART 4: PΓL(3,K) ⊆ Collineations  (the constructive half of the FTPG)
-- ============================================================

/-- **PΓL(3, K) acts by collineations.** A projective *semilinear* map — an invertible
linear map `M` followed by a field automorphism `σ` — preserves collinearity.

This is the inclusion `PΓL(3, K) ⊆ Aut(PG(2, K))`: every transformation named by the
Fundamental Theorem of Projective Geometry genuinely is a collineation. The FTPG's deep
content is the converse inclusion, which requires Desargues (coordinatization). -/
theorem collinear_projSemilinear (M : Matrix (Fin 3) (Fin 3) K) (σ : K →+* K)
    {p q r : Fin 3 → K} (h : Collinear p q r) :
    Collinear (fun i => σ ((M.mulVec p) i)) (fun i => σ ((M.mulVec q) i))
      (fun i => σ ((M.mulVec r) i)) :=
  collinear_semilinear σ (collinear_mulVec M h)

-- ============================================================
-- PART 5: The standard projective frame
-- ============================================================

/-- The standard frame of `PG(2, K)`: the three coordinate points and the unit point,
`e₀ = [1:0:0]`, `e₁ = [0:1:0]`, `e₂ = [0:0:1]`, `u = [1:1:1]`, are in **general
position** — every one of the four 3-point subsets has nonzero determinant, so no three
of them are collinear.  This makes them a genuine projective frame. -/
theorem frame_general_position :
    (rowMat (![1, 0, 0] : Fin 3 → K) ![0, 1, 0] ![0, 0, 1]).det = 1 ∧
    (rowMat (![1, 0, 0] : Fin 3 → K) ![0, 1, 0] ![1, 1, 1]).det = 1 ∧
    (rowMat (![1, 0, 0] : Fin 3 → K) ![0, 0, 1] ![1, 1, 1]).det = -1 ∧
    (rowMat (![0, 1, 0] : Fin 3 → K) ![0, 0, 1] ![1, 1, 1]).det = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · simp only [rowMat_det, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      ring

-- ============================================================
-- PART 6: Frame rigidity — the computational kernel of the FTPG
-- ============================================================

/-- **Frame rigidity / uniqueness up to scalar.**
If a linear map `M` fixes each of the four standard frame points *projectively* (sends
each to a scalar multiple of itself), then all four scalars coincide and `M` is that
common scalar times the identity.

Equivalently: the projective stabilizer of a frame inside `PGL(3, K)` is trivial, so a
projective transformation is **uniquely determined by its action on a frame**. This
rigidity is the exact computational statement underlying the Fundamental Theorem of
Projective Geometry (which upgrades "determined on a frame" to "semilinear"). -/
theorem frame_stabilizer_scalar (M : Matrix (Fin 3) (Fin 3) K) (a b c d : K)
    (ha : M.mulVec ![1, 0, 0] = a • (![1, 0, 0] : Fin 3 → K))
    (hb : M.mulVec ![0, 1, 0] = b • (![0, 1, 0] : Fin 3 → K))
    (hc : M.mulVec ![0, 0, 1] = c • (![0, 0, 1] : Fin 3 → K))
    (hd : M.mulVec ![1, 1, 1] = d • (![1, 1, 1] : Fin 3 → K)) :
    a = d ∧ b = d ∧ c = d ∧ M = d • (1 : Matrix (Fin 3) (Fin 3) K) := by
  -- Extract the columns of `M` from the three coordinate-point hypotheses.
  have e00 : M 0 0 = a := by
    have h := congrFun ha 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e10 : M 1 0 = 0 := by
    have h := congrFun ha 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e20 : M 2 0 = 0 := by
    have h := congrFun ha 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e01 : M 0 1 = 0 := by
    have h := congrFun hb 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e11 : M 1 1 = b := by
    have h := congrFun hb 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e21 : M 2 1 = 0 := by
    have h := congrFun hb 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e02 : M 0 2 = 0 := by
    have h := congrFun hc 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e12 : M 1 2 = 0 := by
    have h := congrFun hc 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  have e22 : M 2 2 = c := by
    have h := congrFun hc 2
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h
  -- The unit-point hypothesis forces the three diagonal scalars to agree with `d`.
  have hda : a = d := by
    have h := congrFun hd 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, mul_one] at h
    rw [e00, e01, e02] at h; linear_combination h
  have hdb : b = d := by
    have h := congrFun hd 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, mul_one] at h
    rw [e10, e11, e12] at h; linear_combination h
  have hdc : c = d := by
    have h := congrFun hd 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Pi.smul_apply, smul_eq_mul, mul_one] at h
    rw [e20, e21, e22] at h; linear_combination h
  refine ⟨hda, hdb, hdc, ?_⟩
  -- Assemble `M = d • 1` entrywise from the nine entry equations.  `fin_cases`
  -- introduces the indices in `Fin.mk` form, so we reduce the identity matrix with
  -- `simp only` and finish with `simp_all`, whose `Fin.isValue` normalization matches
  -- the `Fin.mk` indices against the entry hypotheses `e..` and the scalars `hda..hdc`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] <;>
    simp_all

-- ============================================================
-- PART 7: Projective invariance of the Desargues configuration over K
-- ============================================================

/-- **Projective invariance of Desargues over any field.**
The two relations appearing in Desargues's theorem — perspectivity from a point
(concurrency of the three joining lines) and perspectivity from a line (collinearity of
the three intersection points) — are both `det = 0` conditions on triples of homogeneous
vectors, hence preserved by the collineation group. This generalizes the parent OQ-03
invariance from `ℝ` to arbitrary `K`. -/
theorem desargues_relation_mulVec (M : Matrix (Fin 3) (Fin 3) K) {p q r : Fin 3 → K}
    (h : Collinear p q r) :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) :=
  collinear_mulVec M h

/-- A collineation preserves collinearity in **both directions** when invertible, so it
carries Desargues configurations to Desargues configurations bijectively — the precise
sense in which the Desarguesian property is intrinsic to `PG(2, K)`. -/
theorem desargues_relation_preserved (M : Matrix (Fin 3) (Fin 3) K) (hM : M.det ≠ 0)
    {p q r : Fin 3 → K} :
    Collinear (M.mulVec p) (M.mulVec q) (M.mulVec r) ↔ Collinear p q r :=
  collinear_mulVec_iff M hM

end DesarguesTheoremOQ03OQ01
