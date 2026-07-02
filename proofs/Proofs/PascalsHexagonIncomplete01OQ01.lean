import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Pascal's Hexagon (incomplete-01, OQ-01): removing the symmetry hypothesis

## Context

`PascalsHexagon.lean` reduces Pascal's theorem (for **symmetric** non-degenerate conics carrying a
real point) to the Sylvester reduction

> `sylvester_stdConic_of_isotropic (C : Conic) (hC_sym : C.symmetric) (hC_nd : C.nondegenerate)
>    (p₀ …) (hp₀ : pointOnConic p₀ C) : ∃ M, M.det ≠ 0 ∧ ∀ p, pointOnConic p C ↔
>    pointOnConic (projTransform M p) stdConic`.

Every route through that file carries the standing hypothesis `hC_sym : C.symmetric`, and the
residual `axiom conic_implies_pascal_constraint` is explicitly retained *only* for the
"asymmetric and degenerate cases". The parent's own proof sketch lists, as its first outstanding
step:

> "1. Handle asymmetric `C`: replace with symmetrized `(C + Cᵀ)/2` (same zero set)."

That reduction is stated informally but never proved. **This file proves it**, self-contained.

## What this file proves

For an arbitrary (possibly asymmetric) real conic `C`, let `symmetrize C = (C + Cᵀ)/2`. Then:

* `symmetrize_symmetric` : `symmetrize C` is symmetric;
* `conicQuadraticForm_symmetrize` : `C` and `symmetrize C` have the **same quadratic form**
  (`pᵀ C p = pᵀ (symmetrize C) p` for every `p`) — the quadratic form only sees the symmetric part;
* `pointOnConic_symmetrize` : consequently `C` and `symmetrize C` have the **same point set**;
* `sylvester_without_symmetry` : the Sylvester reduction's `C.symmetric` hypothesis is
  **removable** — given the symmetric case as a black box, every non-degenerate (in its symmetric
  part) conic carrying a real point is projectively equivalent to `stdConic`, symmetric or not.

This discharges the asymmetric half of the reduction: the residual axiom's asymmetric,
non-degenerate, isotropic case follows from the symmetric case with no new assumptions.

**Honest scope.** This does *not* discharge the hard Sylvester direction itself (the indefinite
**symmetric** case, `sylvester_stdConic_of_isotropic`); it removes the *symmetry* hypothesis from
that reduction, reducing the general non-degenerate case to the symmetric one. The conic
definitions below mirror `PascalsHexagon.lean`'s, reproduced locally because that file is currently
bit-rotted under the 4.26.0 toolchain and cannot be imported.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PascalsHexagonIncomplete01OQ01

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

/-- A conic is symmetric iff its matrix is. -/
def Conic.symmetric (C : Conic) : Prop := ∀ i j, C i j = C j i

/-- A conic is non-degenerate iff its determinant is nonzero. -/
def Conic.nondegenerate (C : Conic) : Prop := C.det ≠ 0

/-- A projective transformation acts by matrix-vector multiplication. -/
def projTransform (M : Matrix (Fin 3) (Fin 3) ℝ) (p : ProjPoint) : ProjPoint := M.mulVec p

/-- The standard conic `diag(1,1,-1)`: `x₀² + x₁² − x₂² = 0`. -/
def stdConic : Conic :=
  Matrix.of fun i j => match i, j with
  | 0, 0 => 1
  | 1, 1 => 1
  | 2, 2 => -1
  | _, _ => 0

/-- The **symmetrization** `(C + Cᵀ)/2` of a conic. -/
noncomputable def symmetrize (C : Conic) : Conic := fun i j => (C i j + C j i) / 2

/-- The symmetrization of any conic is symmetric. -/
theorem symmetrize_symmetric (C : Conic) : (symmetrize C).symmetric := by
  intro i j
  unfold symmetrize
  ring

/-- **The quadratic form only sees the symmetric part.**
`pᵀ C p = pᵀ (symmetrize C) p` for every point `p`: the antisymmetric part of `C`
contributes nothing to the quadratic form. -/
theorem conicQuadraticForm_symmetrize (C : Conic) (p : ProjPoint) :
    conicQuadraticForm (symmetrize C) p = conicQuadraticForm C p := by
  -- The transpose part is the same double sum with the summation order swapped.
  have hswap : ∑ i, ∑ j, C j i * p i * p j = ∑ i, ∑ j, C i j * p i * p j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  unfold conicQuadraticForm symmetrize
  -- Rewrite each summand `(Cᵢⱼ + Cⱼᵢ)/2 · pᵢpⱼ = (Cᵢⱼ pᵢpⱼ + Cⱼᵢ pᵢpⱼ)/2`, then split the sums.
  have step1 : ∀ i j : Fin 3,
      (C i j + C j i) / 2 * p i * p j = (C i j * p i * p j + C j i * p i * p j) / 2 :=
    fun i j => by ring
  simp_rw [step1, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hswap]
  ring

/-- **Same point set.** A point lies on `C` iff it lies on `symmetrize C`. This is the rigorous
"same zero set" claim that justifies the WLOG-symmetric step in the Sylvester reduction. -/
theorem pointOnConic_symmetrize (C : Conic) (p : ProjPoint) :
    pointOnConic p (symmetrize C) ↔ pointOnConic p C := by
  unfold pointOnConic
  rw [conicQuadraticForm_symmetrize]

/-- **The symmetry hypothesis of the Sylvester reduction is removable.**

Given the symmetric case of the Sylvester reduction as a hypothesis `sylvester_sym`, *every*
conic `C` whose symmetric part is non-degenerate and which carries a nonzero real point is
projectively equivalent to `stdConic` — with no symmetry assumption on `C` itself. The witnessing
matrix `M` is exactly the one produced for `symmetrize C`; it works for `C` because the two conics
have identical point sets (`pointOnConic_symmetrize`).

This reduces the asymmetric, non-degenerate, isotropic case of Pascal's
`conic_implies_pascal_constraint` to the symmetric case, introducing no new assumptions. -/
theorem sylvester_without_symmetry
    (sylvester_sym : ∀ C : Conic, C.symmetric → C.nondegenerate →
      (∃ p : ProjPoint, p ≠ 0 ∧ pointOnConic p C) →
      ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
        ∀ p, pointOnConic p C ↔ pointOnConic (projTransform M p) stdConic)
    (C : Conic) (hnd : (symmetrize C).nondegenerate)
    (hiso : ∃ p : ProjPoint, p ≠ 0 ∧ pointOnConic p C) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℝ, M.det ≠ 0 ∧
      ∀ p, pointOnConic p C ↔ pointOnConic (projTransform M p) stdConic := by
  -- Transport the isotropic witness onto `symmetrize C`.
  obtain ⟨p₀, hp₀ne, hp₀on⟩ := hiso
  have hp₀sym : pointOnConic p₀ (symmetrize C) := (pointOnConic_symmetrize C p₀).mpr hp₀on
  -- Apply the symmetric case to `symmetrize C`.
  obtain ⟨M, hMdet, hMiff⟩ :=
    sylvester_sym (symmetrize C) (symmetrize_symmetric C) hnd ⟨p₀, hp₀ne, hp₀sym⟩
  -- The same `M` works for `C`, since `C` and `symmetrize C` share their point set.
  refine ⟨M, hMdet, fun p => ?_⟩
  rw [← pointOnConic_symmetrize C p]
  exact hMiff p

/-- **Sanity check: the reduction is non-vacuous.** A concretely asymmetric conic and its
symmetrization define the same point set. Here `C = !![0,2,0; 0,0,0; 0,0,0]` is asymmetric
(`C 0 1 = 2 ≠ 0 = C 1 0`), yet shares every point with `symmetrize C`. -/
theorem symmetrize_nontrivial_example :
    ∃ C : Conic, ¬ C.symmetric ∧
      ∀ p : ProjPoint, pointOnConic p C ↔ pointOnConic p (symmetrize C) := by
  refine ⟨!![0, 2, 0; 0, 0, 0; 0, 0, 0], ?_, fun p => (pointOnConic_symmetrize _ p).symm⟩
  intro hsym
  have h := hsym 0 1
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h

end PascalsHexagonIncomplete01OQ01
