import Mathlib

/-!
# Pascal's Hexagon (incomplete-01, OQ-03, OQ-01): indefinite diagonal conics *are* `stdConic`

## Context

The necessity files in this chain show that a **definite** conic is never projectively equivalent
to `stdConic = diag(1,1,-1)`:

* `PascalsHexagonIncomplete01.lean` — the single witness `diag(1,1,1) = (1 : Conic)`;
* `PascalsHexagonIncomplete01OQ03.lean` — every `Matrix.PosDef` conic (`posDef_not_projEquiv_stdConic`).

Both proofs hinge on the same dichotomy: `stdConic` is **isotropic** (carries the real point
`(1,0,1) ≠ 0`), whereas a definite form vanishes only at the origin.

**OQ-01** asks for the *sufficiency* converse on the other side of the boundary:

> Is an **indefinite** diagonal conic `diag(a,b,c)` with `a,b > 0` and `c < 0` projectively
> equivalent to `stdConic`?

The answer is **yes, constructively**. This is the easy half of the Sylvester reduction
`sylvester_stdConic_of_isotropic` (the hard half — diagonalising an arbitrary symmetric conic — is
the still-open `sorry` in `PascalsHexagon.lean`): once a conic is *already diagonal* with the
signature `(2,1)` of `stdConic`, the equivalence is an explicit coordinate rescaling.

## What this file proves

Take the diagonal matrix `rescale a b c = diag(√a, √b, √(-c))`. Because `(√a)² = a`, `(√b)² = b`
and `(√(-c))² = -c`, the pullback of `stdConic`'s quadratic form along `rescale` is *exactly* the
form of `diag(a,b,c)`:

* `qform_stdConic_rescale` — `Q_stdConic(rescale·p) = Q_{diag(a,b,c)}(p)` as an identity of reals
  (for `0 ≤ a`, `0 ≤ b`, `c ≤ 0`);
* `det_rescale` / `det_rescale_ne_zero` — `rescale` is invertible when `a,b > 0`, `c < 0`;
* `diagConic_indefinite_projEquiv_stdConic` — hence `diag(a,b,c)` with `a,b > 0`, `c < 0` is
  projectively equivalent to `stdConic` (same notion of equivalence as the necessity files).

Combined with `posDef_not_projEquiv_stdConic`, this pins the boundary exactly at the **signature**:
among diagonal real conics, `diag(a,b,c)` is `stdConic`-equivalent precisely in the indefinite
`(2,1)` case, and never in the definite `(3,0)` case.

The conic definitions below mirror the sibling files (reproduced locally because
`PascalsHexagon.lean` is currently bit-rotted under the 4.26.0 toolchain).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PascalsHexagonIncomplete01OQ03OQ01

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

/-- The diagonal conic `diag(a,b,c)`: `a x₀² + b x₁² + c x₂² = 0`. -/
def diagConic (a b c : ℝ) : Conic :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => a
  | 1, 1 => b
  | 2, 2 => c
  | _, _ => 0

/-- A projective transformation acts by matrix-vector multiplication. -/
def projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint := M.mulVec p

/-- The diagonal rescaling matrix `diag(√a, √b, √(-c))` that carries `diag(a,b,c)` onto
    `stdConic` when `a,b ≥ 0` and `c ≤ 0`. -/
noncomputable def rescale (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => Real.sqrt a
  | 1, 1 => Real.sqrt b
  | 2, 2 => Real.sqrt (-c)
  | _, _ => 0

/-- The quadratic form of `stdConic` is `x₀² + x₁² − x₂²`. -/
theorem conicQuadraticForm_stdConic (q : ProjPoint) :
    conicQuadraticForm stdConic q = (q 0) ^ 2 + (q 1) ^ 2 - (q 2) ^ 2 := by
  simp only [conicQuadraticForm, stdConic, Fin.sum_univ_three, Matrix.of_apply]
  ring

/-- The quadratic form of `diag(a,b,c)` is `a x₀² + b x₁² + c x₂²`. -/
theorem conicQuadraticForm_diagConic (a b c : ℝ) (p : ProjPoint) :
    conicQuadraticForm (diagConic a b c) p = a * (p 0) ^ 2 + b * (p 1) ^ 2 + c * (p 2) ^ 2 := by
  simp only [conicQuadraticForm, diagConic, Fin.sum_univ_three, Matrix.of_apply]
  ring

/-- The coordinatewise action of `rescale a b c` on a point. -/
theorem rescale_mulVec (a b c : ℝ) (p : ProjPoint) :
    (rescale a b c).mulVec p 0 = Real.sqrt a * p 0 ∧
    (rescale a b c).mulVec p 1 = Real.sqrt b * p 1 ∧
    (rescale a b c).mulVec p 2 = Real.sqrt (-c) * p 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [rescale, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.of_apply]

/-- **The pullback identity.** Pulling `stdConic`'s quadratic form back along the rescaling
    `rescale a b c` reproduces exactly the quadratic form of `diag(a,b,c)` (for `0 ≤ a`, `0 ≤ b`,
    `c ≤ 0`), because `(√a)² = a`, `(√b)² = b`, `(√(-c))² = -c`. -/
theorem qform_stdConic_rescale (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ 0) (p : ProjPoint) :
    conicQuadraticForm stdConic (projTransform (rescale a b c) p)
      = conicQuadraticForm (diagConic a b c) p := by
  obtain ⟨e0, e1, e2⟩ := rescale_mulVec a b c p
  rw [conicQuadraticForm_stdConic, conicQuadraticForm_diagConic]
  simp only [projTransform, e0, e1, e2]
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb,
    Real.sq_sqrt (neg_nonneg.mpr hc)]
  ring

/-- The determinant of the rescaling matrix is `√a · √b · √(-c)`. -/
theorem det_rescale (a b c : ℝ) :
    (rescale a b c).det = Real.sqrt a * Real.sqrt b * Real.sqrt (-c) := by
  simp [Matrix.det_fin_three, rescale, Matrix.of_apply]

/-- For an indefinite signature (`a, b > 0`, `c < 0`) the rescaling matrix is invertible. -/
theorem det_rescale_ne_zero (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c < 0) :
    (rescale a b c).det ≠ 0 := by
  rw [det_rescale]
  have h1 : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h2 : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have h3 : 0 < Real.sqrt (-c) := Real.sqrt_pos.mpr (neg_pos.mpr hc)
  exact ne_of_gt (mul_pos (mul_pos h1 h2) h3)

/-- **Indefinite diagonal conics are projectively equivalent to `stdConic`.**
    For `a, b > 0` and `c < 0`, the determinant-nonzero rescaling `diag(√a, √b, √(-c))`
    intertwines "lies on `diag(a,b,c)`" with "lies on `stdConic`": this is the constructive,
    already-diagonal half of the Sylvester reduction. -/
theorem diagConic_indefinite_projEquiv_stdConic (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p : ProjPoint, pointOnConic p (diagConic a b c) ↔ pointOnConic (projTransform M p) stdConic := by
  refine ⟨rescale a b c, det_rescale_ne_zero a b c ha hb hc, fun p => ?_⟩
  unfold pointOnConic
  rw [qform_stdConic_rescale a b c ha.le hb.le hc.le p]

/-- **Sanity check / base case.** `stdConic` itself is `diag(1,1,-1)`, so it is projectively
    equivalent to `stdConic` via the identity rescaling `diag(1,1,1)`. -/
theorem stdConic_projEquiv_stdConic :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p : ProjPoint,
        pointOnConic p (diagConic 1 1 (-1)) ↔ pointOnConic (projTransform M p) stdConic :=
  diagConic_indefinite_projEquiv_stdConic 1 1 (-1) one_pos one_pos (by norm_num)

end PascalsHexagonIncomplete01OQ03OQ01

/-!
## Summary

Completing the diagonal half of the conic dichotomy begun by the necessity files:

- `qform_stdConic_rescale`: the rescaling `diag(√a,√b,√(-c))` pulls `stdConic`'s form back to the
  form of `diag(a,b,c)` exactly (signature `(2,1)`, i.e. `a,b ≥ 0`, `c ≤ 0`).
- `det_rescale_ne_zero`: that rescaling is invertible when `a,b > 0`, `c < 0`.
- `diagConic_indefinite_projEquiv_stdConic`: hence every indefinite diagonal conic `diag(a,b,c)`
  with `a,b > 0`, `c < 0` is projectively equivalent to `stdConic`.

Together with `posDef_not_projEquiv_stdConic` (definite ⟹ not equivalent), this locates the
boundary exactly at the **signature**: a diagonal real conic is `stdConic`-equivalent iff it is
indefinite of type `(2,1)`. This is the constructive, already-diagonal half of the open Sylvester
reduction `sylvester_stdConic_of_isotropic`; the remaining open part is the diagonalisation of an
arbitrary symmetric conic carrying a real point.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
