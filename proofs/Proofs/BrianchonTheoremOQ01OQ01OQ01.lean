import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-
# Pascal transfers to every linear image of the conic — projective covariance, axiom-free

## What This Proves

The parent `BrianchonTheoremOQ01OQ01.lean` proves Pascal's hexagon theorem for the
**rational-normal conic** `xz = y²` (parametrized `t ↦ (t², t, 1)`) axiom-free, in
the homogeneous `ℝ³` cross-product / determinant model.  Its docstring identifies
the **only** remaining ingredient separating that result from a full discharge of
the abstract `conic_implies_pascal` axiom:

> the projective-normalization / Sylvester transfer — that Pascal's conclusion is
> invariant under projective maps, so the parametrized case carries over to an
> arbitrary nondegenerate conic.

This file formalizes the **projective-covariance half** of that transfer, axiom-free.
We show Pascal's collinearity conclusion survives applying **any** linear map
`m : ℝ³ → ℝ³` to all six hexagon vertices — hence Pascal holds for every linear
image of the rational-normal conic.  Two classical identities of the `ℝ³` model do
all the work, each a single `ring` computation:

* **Cross-product covariance** (`cross_applyM`):
  `(m u) × (m v) = cof(m) · (u × v)`, where `cof(m)` is the cofactor matrix
  (`= adj(m)ᵀ`).  The join/meet of transformed points is the transformed join/meet.
* **Determinant covariance** (`det3_applyM`):
  `det₃(m u, m v, m w) = det(m) · det₃(u, v, w)`.  Collinearity (vanishing of `det₃`)
  is therefore a projective invariant.

Applying `cross_applyM` three times shows each transformed Pascal point is the SAME
matrix `cof(cof(m))` applied to the original Pascal point; `det3_applyM` then sends
the original (zero) collinearity determinant to zero.  No invertibility of `m` is
needed — the conclusion is a polynomial identity — so the result holds for every
linear map, and specializes to the genuine projective transfer when `det(m) ≠ 0`.

## Relation to the `conic_implies_pascal` axiom

Together with a Sylvester normalization (every nondegenerate symmetric `C` has an
invertible `M` carrying its zero locus `xᵀ C x = 0` onto `xz = y²`), this covariance
step would discharge `conic_implies_pascal` for nondegenerate conics: pull the six
points back along `M`, apply the parent's `pascal_parametrized`, and push forward by
`pascal_image` here.  The Sylvester normalization (the symmetric-matrix linear
algebra) is the remaining piece; the covariance is done here.

## Status
- [x] Cross-product and determinant covariance under a linear map — 0 sorries, 0 axioms
- [x] Pascal transfers to every linear image of the rational-normal conic
- [x] Same homogeneous `ℝ³` cross/det model as the parent; pure `ring` identities
- [x] No `sorry`, no `axiom`, no `native_decide`
-/

namespace BrianchonOQ01OQ01OQ01

/-! ## Homogeneous `ℝ³` model (cross product, determinant, collinearity)
Reproduced from the parent entry so this file is self-contained. -/

/-- The cross product of two vectors in `ℝ³` — the join of two projective points
and the meet of two projective lines. -/
noncomputable def cross (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The scalar triple product `u · (v × w)` = the `3×3` determinant with rows
`u, v, w`.  Three projective points are collinear iff this vanishes. -/
noncomputable def det3 (u v w : Fin 3 → ℝ) : ℝ :=
  u 0 * (v 1 * w 2 - v 2 * w 1)
    - u 1 * (v 0 * w 2 - v 2 * w 0)
    + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- Three projective points are collinear iff their determinant vanishes. -/
def Collinear (p q r : Fin 3 → ℝ) : Prop := det3 p q r = 0

/-- A point of the rational-normal conic `xz = y²`, parametrized by `t ↦ (t², t, 1)`. -/
noncomputable def conicPt (t : ℝ) : Fin 3 → ℝ := ![t ^ 2, t, 1]

/-! ## A linear map on `ℝ³` and its determinant / cofactor matrix
Given as explicit component formulas (matching the parent's style) so every
covariance identity reduces to a single `ring` call. -/

/-- Apply the `3×3` matrix `m` (rows `m 0, m 1, m 2`) to a vector `u`. -/
noncomputable def applyM (m : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![m 0 0 * u 0 + m 0 1 * u 1 + m 0 2 * u 2,
    m 1 0 * u 0 + m 1 1 * u 1 + m 1 2 * u 2,
    m 2 0 * u 0 + m 2 1 * u 1 + m 2 2 * u 2]

/-- The determinant of the `3×3` matrix `m` (cofactor expansion along row 0). -/
noncomputable def detM (m : Fin 3 → Fin 3 → ℝ) : ℝ :=
  m 0 0 * (m 1 1 * m 2 2 - m 1 2 * m 2 1)
    - m 0 1 * (m 1 0 * m 2 2 - m 1 2 * m 2 0)
    + m 0 2 * (m 1 0 * m 2 1 - m 1 1 * m 2 0)

/-- The **cofactor matrix** `cof(m)` (`= adj(m)ᵀ`): entry `(i, j)` is the signed
`(i, j)` cofactor of `m`.  It satisfies `(m u) × (m v) = cof(m) · (u × v)`. -/
noncomputable def cof (m : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![m 1 1 * m 2 2 - m 1 2 * m 2 1, m 1 2 * m 2 0 - m 1 0 * m 2 2,
      m 1 0 * m 2 1 - m 1 1 * m 2 0],
    ![m 0 2 * m 2 1 - m 0 1 * m 2 2, m 0 0 * m 2 2 - m 0 2 * m 2 0,
      m 0 1 * m 2 0 - m 0 0 * m 2 1],
    ![m 0 1 * m 1 2 - m 0 2 * m 1 1, m 0 2 * m 1 0 - m 0 0 * m 1 2,
      m 0 0 * m 1 1 - m 0 1 * m 1 0]]

/-! ## The two covariance identities -/

/-- **Cross-product covariance.** The join/meet of two transformed points is the
cofactor matrix applied to the join/meet: `(m u) × (m v) = cof(m) · (u × v)`. -/
theorem cross_applyM (m : Fin 3 → Fin 3 → ℝ) (u v : Fin 3 → ℝ) :
    cross (applyM m u) (applyM m v) = applyM (cof m) (cross u v) := by
  funext i
  fin_cases i <;>
    · simp only [cross, applyM, cof, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
      ring

/-- **Determinant covariance.** `det₃(m u, m v, m w) = det(m) · det₃(u, v, w)`, so
collinearity (the vanishing of `det₃`) is preserved by every linear map. -/
theorem det3_applyM (m : Fin 3 → Fin 3 → ℝ) (u v w : Fin 3 → ℝ) :
    det3 (applyM m u) (applyM m v) (applyM m w) = detM m * det3 u v w := by
  simp only [det3, applyM, detM, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Collinearity is a projective invariant** (for invertible `m`): if `det(m) ≠ 0`
then the images `m u, m v, m w` are collinear iff `u, v, w` are. -/
theorem collinear_applyM_iff {m : Fin 3 → Fin 3 → ℝ} (hm : detM m ≠ 0)
    (u v w : Fin 3 → ℝ) :
    Collinear (applyM m u) (applyM m v) (applyM m w) ↔ Collinear u v w := by
  unfold Collinear
  rw [det3_applyM, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hm
    · exact h
  · intro h; exact Or.inr h

/-! ## Pascal transfers to every linear image of the conic -/

/-- The three Pascal points of an inscribed hexagon `A B C D E F`
(`X = (AB) ∧ (DE)`, `Y = (BC) ∧ (EF)`, `Z = (CD) ∧ (FA)`). -/
noncomputable def pascalX (A B _C D E _F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross A B) (cross D E)
noncomputable def pascalY (_A B C _D E F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross B C) (cross E F)
noncomputable def pascalZ (A _B C D _E F : Fin 3 → ℝ) : Fin 3 → ℝ :=
  cross (cross C D) (cross F A)

/-- Each Pascal point of the transformed hexagon is the SAME matrix `cof(cof m)`
applied to the original Pascal point — apply `cross_applyM` three times. -/
theorem pascalX_applyM (m : Fin 3 → Fin 3 → ℝ) (A B C D E F : Fin 3 → ℝ) :
    pascalX (applyM m A) (applyM m B) (applyM m C) (applyM m D) (applyM m E) (applyM m F)
      = applyM (cof (cof m)) (pascalX A B C D E F) := by
  simp only [pascalX]
  rw [cross_applyM, cross_applyM, cross_applyM]

theorem pascalY_applyM (m : Fin 3 → Fin 3 → ℝ) (A B C D E F : Fin 3 → ℝ) :
    pascalY (applyM m A) (applyM m B) (applyM m C) (applyM m D) (applyM m E) (applyM m F)
      = applyM (cof (cof m)) (pascalY A B C D E F) := by
  simp only [pascalY]
  rw [cross_applyM, cross_applyM, cross_applyM]

theorem pascalZ_applyM (m : Fin 3 → Fin 3 → ℝ) (A B C D E F : Fin 3 → ℝ) :
    pascalZ (applyM m A) (applyM m B) (applyM m C) (applyM m D) (applyM m E) (applyM m F)
      = applyM (cof (cof m)) (pascalZ A B C D E F) := by
  simp only [pascalZ]
  rw [cross_applyM, cross_applyM, cross_applyM]

/-- **Pascal's theorem for the rational-normal conic (parametrized case).**
Re-proved here self-containedly: for any six parameters the Pascal points are
collinear. -/
theorem pascal_parametrized (a b c d e f : ℝ) :
    Collinear
      (pascalX (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalY (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f))
      (pascalZ (conicPt a) (conicPt b) (conicPt c) (conicPt d) (conicPt e) (conicPt f)) := by
  simp only [Collinear, det3, pascalX, pascalY, pascalZ, cross, conicPt,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **Main theorem — Pascal transfers to every linear image of the conic.**
For any linear map `m` and any six parameters, the six points
`m · conicPt a, …, m · conicPt f` (the image of the rational-normal conic under `m`)
have collinear Pascal points.  The transformed Pascal points are `cof(cof m)` applied
to the originals (`pascal{X,Y,Z}_applyM`), and `det3_applyM` carries the original
zero collinearity determinant to zero — no invertibility of `m` required.  For
invertible `m` (`det m ≠ 0`) this is the genuine projective transfer of Pascal's
theorem to the conic `m · (xz = y²)`. -/
theorem pascal_image (m : Fin 3 → Fin 3 → ℝ) (a b c d e f : ℝ) :
    Collinear
      (pascalX (applyM m (conicPt a)) (applyM m (conicPt b)) (applyM m (conicPt c))
        (applyM m (conicPt d)) (applyM m (conicPt e)) (applyM m (conicPt f)))
      (pascalY (applyM m (conicPt a)) (applyM m (conicPt b)) (applyM m (conicPt c))
        (applyM m (conicPt d)) (applyM m (conicPt e)) (applyM m (conicPt f)))
      (pascalZ (applyM m (conicPt a)) (applyM m (conicPt b)) (applyM m (conicPt c))
        (applyM m (conicPt d)) (applyM m (conicPt e)) (applyM m (conicPt f))) := by
  unfold Collinear
  rw [pascalX_applyM, pascalY_applyM, pascalZ_applyM, det3_applyM]
  have h := pascal_parametrized a b c d e f
  unfold Collinear at h
  rw [h, mul_zero]

end BrianchonOQ01OQ01OQ01
