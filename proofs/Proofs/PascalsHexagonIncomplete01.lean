import Mathlib

/-!
# Pascal's Hexagon (incomplete-01): the real-point hypothesis is essential

## Context

`PascalsHexagon.lean` reduces Pascal's theorem (for symmetric non-degenerate conics) to a single
remaining `sorry`, the Sylvester reduction `sylvester_stdConic_of_isotropic`: a non-degenerate
symmetric real conic carrying a **real point** `p₀` is projectively equivalent to
`stdConic = diag(1,1,-1)`. Its docstring asserts that the real-point hypothesis is

> "essential and not removable: a definite non-degenerate `C` (signature (3,0)/(0,3)) has only
> the trivial zero `p = 0`, while `stdConic` has a full cone of real zeros, so no such `M` can
> exist."

That claim is stated informally but never proved. This file proves it.

## What this file proves

Taking the positive-definite conic `diag(1,1,1) = (1 : Conic)` as the witness:

* `pointOnConic_one_iff`: a point lies on the identity conic iff it is the zero vector — the
  identity conic has only the trivial zero (`x₀² + x₁² + x₂² = 0 ⟺ x = 0` over ℝ);
* `real_point_hypothesis_essential`: there is **no** invertible `M` with
  `pointOnConic p (1 : Conic) ↔ pointOnConic (M·p) stdConic` for all `p`. Such an `M` would carry
  the single zero of the identity conic onto the nonzero `stdConic` point `(1,0,1)`, forcing a
  nonzero vector to be zero.

So the Sylvester reduction genuinely **requires** a real point on `C`; without it (the definite
case) the conclusion is false. This rigorously justifies the hypothesis `hp₀` in
`sylvester_stdConic_of_isotropic`.

**Honest scope.** This does *not* discharge the `sorry` (the hard, true Sylvester direction for
conics that *do* carry a real point). It proves the complementary necessity statement. The
conic definitions below mirror `PascalsHexagon.lean`'s, reproduced locally because that file is
currently bit-rotted under the 4.26.0 toolchain (parser/`ring`/`linarith` failures) and cannot
be imported.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PascalsHexagonIncomplete01

open Finset

/-- A projective point: a vector in `ℝ³` (mirrors `PascalsHexagon.ProjPoint`). -/
abbrev ProjPoint := Fin 3 → ℝ

/-- A conic: a `3×3` real matrix (mirrors `PascalsHexagon.Conic`). -/
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

/-- The quadratic form of the identity conic is the sum of squares `∑ᵢ pᵢ²`. -/
theorem conicQuadraticForm_one (p : ProjPoint) :
    conicQuadraticForm (1 : Conic) p = ∑ i, p i * p i := by
  unfold conicQuadraticForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i
    (fun j _ hj => by rw [Matrix.one_apply_ne' hj]; ring)
    (fun hi => absurd (Finset.mem_univ i) hi)]
  rw [Matrix.one_apply_eq]; ring

/-- **The identity conic has only the trivial zero.** A point lies on `(1 : Conic)` — the
    positive-definite conic `x₀² + x₁² + x₂² = 0` — iff it is the zero vector. -/
theorem pointOnConic_one_iff (p : ProjPoint) :
    pointOnConic p (1 : Conic) ↔ p = 0 := by
  rw [pointOnConic, conicQuadraticForm_one]
  constructor
  · intro h
    have hz : ∀ i ∈ Finset.univ, p i * p i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (p i)).mp h
    funext i
    exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))
  · intro h
    subst h
    simp

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

/-- **The real-point hypothesis of `sylvester_stdConic_of_isotropic` is essential.**
    No invertible projective transformation `M` makes the positive-definite identity conic
    equivalent to `stdConic`: the identity conic has only the zero point, whereas `stdConic`
    carries the nonzero point `(1,0,1)`, and an invertible `M` would have to send a zero vector
    onto it. -/
theorem real_point_hypothesis_essential :
    ¬ ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p : ProjPoint, pointOnConic p (1 : Conic) ↔ pointOnConic (projTransform M p) stdConic := by
  rintro ⟨M, hdet, hiff⟩
  set q : ProjPoint := isotropicPoint with hq
  have hq0 : q ≠ 0 := isotropicPoint_ne_zero
  have hqc : pointOnConic q stdConic := isotropicPoint_on_stdConic
  -- its preimage p = M⁻¹ q transforms back to q
  set p : ProjPoint := M⁻¹.mulVec q with hp
  have hMp : projTransform M p = q := by
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
    simp only [projTransform, hp]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu, Matrix.one_mulVec]
  -- so p lies on the identity conic, hence p = 0
  have hpOn : pointOnConic p (1 : Conic) := (hiff p).mpr (by rw [hMp]; exact hqc)
  have hp0 : p = 0 := (pointOnConic_one_iff p).mp hpOn
  -- but then q = M·p = M·0 = 0, contradicting q ≠ 0
  have hq00 : q = 0 := by
    rw [← hMp]; simp only [projTransform, hp0, Matrix.mulVec_zero]
  exact hq0 hq00

end PascalsHexagonIncomplete01

/-!
## Summary

Proving the informal "essential hypothesis" claim of `sylvester_stdConic_of_isotropic`:

- `pointOnConic_one_iff`: the identity conic `diag(1,1,1)` has only the trivial zero.
- `real_point_hypothesis_essential`: no invertible `M` makes the identity conic projectively
  equivalent to `stdConic`, so the Sylvester reduction genuinely needs a real point on `C`.

This complements (does not discharge) the remaining `sorry`, which handles conics that *do* carry
a real point. Conic definitions mirror `PascalsHexagon.lean`, reproduced locally because that file
is currently bit-rotted.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
