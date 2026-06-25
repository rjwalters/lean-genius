import Mathlib

/-!
# Pascal's Hexagon (incomplete-01, OQ-03): positive-definite conics are never `stdConic`

## Context

The parent file `PascalsHexagonIncomplete01.lean` shows that the **real-point hypothesis** of
the Sylvester reduction `sylvester_stdConic_of_isotropic` is essential, using the *single*
positive-definite witness `diag(1,1,1) = (1 : Conic)`: that conic has only the trivial zero,
whereas `stdConic = diag(1,1,-1)` carries the real point `(1,0,1)`, so no invertible projective
transformation can identify them.

**OQ-03** asks for the general statement behind that one witness:

> Any **positive-definite** symmetric conic `C` fails to be projectively equivalent to `stdConic`
> over `ℝ`.

The mathematics is the classical fact that a positive-definite quadratic form vanishes at no
nonzero real point, while `stdConic` is isotropic (it carries the real point `(1,0,1) ≠ 0`).
A projective equivalence is a determinant-nonzero matrix `M` intertwining the two
"lies-on-the-conic" predicates; pulling the real point of `stdConic` back through `M⁻¹` would
produce a *nonzero* real zero of `C`, contradicting positive-definiteness.

This file proves that statement for an arbitrary `C` satisfying Mathlib's `Matrix.PosDef`
(Hermitian — i.e. symmetric over `ℝ` — with `xᵀ C x > 0` for all `x ≠ 0`), and recovers the
parent's identity-conic result as the special case `Matrix.posDef_one`.

The bridge to Mathlib is `conicQuadraticForm_eq_dotProduct`, identifying the file-local quadratic
form `∑ᵢⱼ Cᵢⱼ pᵢ pⱼ` with `p ⬝ᵥ (C *ᵥ p)`, the expression appearing in `Matrix.PosDef`.

The conic definitions below mirror `PascalsHexagonIncomplete01.lean` (reproduced locally because
`PascalsHexagon.lean` is currently bit-rotted).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PascalsHexagonIncomplete01OQ03

open Finset Matrix

/-- A projective point: a vector in `ℝ³`. -/
abbrev ProjPoint := Fin 3 → ℝ

/-- A conic: a `3×3` real matrix. -/
abbrev Conic := Matrix (Fin 3) (Fin 3) ℝ

/-- The quadratic form of a conic, `pᵀ C p = ∑ᵢⱼ Cᵢⱼ pᵢ pⱼ`. -/
noncomputable def conicQuadraticForm (C : Conic) (p : ProjPoint) : ℝ :=
  ∑ i, ∑ j, C i j * p i * p j

/-- A point lies on a conic iff its quadratic form vanishes. -/
def pointOnConic (p : ProjPoint) (C : Conic) : Prop := conicQuadraticForm C p = 0

/-- The standard conic `diag(1,1,-1)`: `x₀² + x₁² − x₂² = 0`. -/
def stdConic : Conic :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => -1
  | _, _ => 0

/-- A projective transformation acts by matrix-vector multiplication. -/
def projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint := M.mulVec p

/-- The point `(1, 0, 1)`. -/
def isotropicPoint : ProjPoint := ![1, 0, 1]

/-- `(1,0,1)` lies on `stdConic` (`1² + 0² − 1² = 0`). -/
theorem isotropicPoint_on_stdConic : pointOnConic isotropicPoint stdConic := by
  simp [pointOnConic, conicQuadraticForm, stdConic, isotropicPoint, Fin.sum_univ_three,
    Matrix.of_apply]

/-- `(1,0,1)` is nonzero. -/
theorem isotropicPoint_ne_zero : isotropicPoint ≠ 0 := by
  intro h
  have h0 := congr_fun h 0
  simp [isotropicPoint] at h0

/-- **Bridge to Mathlib.** The file-local quadratic form is exactly `p ⬝ᵥ (C *ᵥ p)`, the
    bilinear expression underlying `Matrix.PosDef`. -/
theorem conicQuadraticForm_eq_dotProduct (C : Conic) (p : ProjPoint) :
    conicQuadraticForm C p = p ⬝ᵥ (C *ᵥ p) := by
  simp only [conicQuadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **A positive-definite conic has only the trivial zero.** For `C` positive definite, a point
    lies on `C` iff it is the zero vector: the form vanishes at no nonzero real point. -/
theorem pointOnConic_posDef_iff {C : Conic} (hC : C.PosDef) (p : ProjPoint) :
    pointOnConic p C ↔ p = 0 := by
  rw [pointOnConic, conicQuadraticForm_eq_dotProduct]
  constructor
  · intro h
    by_contra hp
    have hpos : 0 < star p ⬝ᵥ (C *ᵥ p) := hC.dotProduct_mulVec_pos hp
    have hstar : star p = p := by funext i; simp
    rw [hstar] at hpos
    exact (lt_irrefl (0 : ℝ)) (h ▸ hpos)
  · intro h
    subst h
    simp

/-- **Positive-definite conics are never projectively equivalent to `stdConic`.**
    No determinant-nonzero matrix `M` intertwines "lies on `C`" with "lies on `stdConic`":
    `C` has only the trivial zero, whereas `stdConic` carries the nonzero point `(1,0,1)`, and the
    preimage of that point under an invertible `M` would be a nonzero real zero of `C`. -/
theorem posDef_not_projEquiv_stdConic {C : Conic} (hC : C.PosDef) :
    ¬ ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p : ProjPoint, pointOnConic p C ↔ pointOnConic (projTransform M p) stdConic := by
  rintro ⟨M, hdet, hiff⟩
  set q : ProjPoint := isotropicPoint with hq
  have hq0 : q ≠ 0 := isotropicPoint_ne_zero
  have hqc : pointOnConic q stdConic := isotropicPoint_on_stdConic
  -- the preimage `p = M⁻¹ q` transforms back to `q`
  set p : ProjPoint := M⁻¹.mulVec q with hp
  have hMp : projTransform M p = q := by
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
    simp only [projTransform, hp]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  -- so `p` lies on the positive-definite conic `C`, forcing `p = 0`
  have hpOn : pointOnConic p C := (hiff p).mpr (by rw [hMp]; exact hqc)
  have hp0 : p = 0 := (pointOnConic_posDef_iff hC p).mp hpOn
  -- but then `q = M·p = M·0 = 0`, contradicting `q ≠ 0`
  have hq00 : q = 0 := by
    rw [← hMp]; simp only [projTransform, hp0, Matrix.mulVec_zero]
  exact hq0 hq00

/-- **The parent's identity-conic result, recovered as a special case.** Since `(1 : Conic)` is
    positive definite (`Matrix.posDef_one`), it is not projectively equivalent to `stdConic`. -/
theorem one_not_projEquiv_stdConic :
    ¬ ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p : ProjPoint, pointOnConic p (1 : Conic) ↔ pointOnConic (projTransform M p) stdConic :=
  posDef_not_projEquiv_stdConic Matrix.PosDef.one

end PascalsHexagonIncomplete01OQ03

/-!
## Summary

Generalising the parent's single-witness necessity argument:

- `conicQuadraticForm_eq_dotProduct`: the file-local quadratic form `∑ᵢⱼ Cᵢⱼ pᵢ pⱼ` equals
  `p ⬝ᵥ (C *ᵥ p)`, bridging to Mathlib's `Matrix.PosDef`.
- `pointOnConic_posDef_iff`: a positive-definite conic vanishes only at the zero vector.
- `posDef_not_projEquiv_stdConic`: **no** positive-definite symmetric conic is projectively
  equivalent to `stdConic`, because `stdConic` is isotropic (carries `(1,0,1) ≠ 0`).
- `one_not_projEquiv_stdConic`: the parent's `diag(1,1,1)` statement, recovered via
  `Matrix.posDef_one`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
