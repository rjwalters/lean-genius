/-
Similarity is K[X]-Module Isomorphism: the Structural Heart of Rational Canonical Form
(cayley-hamilton-minpoly-oq-02-oq-02-oq-01)

Open question from cayley-hamilton-minpoly-oq-02-oq-02:
"The minimal and characteristic polynomials do not determine the similarity
class; the complete invariant is the list of invariant factors (the rational
canonical form, RCF). Can the classification A ∼ B ⟺ RCF(A) = RCF(B) be
formalized?"

## What this file contributes

The sibling file `CayleyHamiltonMinpolyOQ02OQ02.lean` gave a concrete 4×4
counterexample showing minpoly + charpoly are *not* a complete invariant, and
`...OQ02OQ02OQ02.lean` built the single Jordan block `J_n(μ)` (one elementary
divisor `(X - μ)ⁿ`). The remaining gap is the *organizing principle* behind
RCF: why invariant factors are a **complete** invariant at all.

That principle is a reduction, not a computation:

    two operators are similar  ⟺  their associated K[X]-modules are isomorphic.

Recall the K[X]-module attached to an endomorphism `φ : M →ₗ[K] M`: it is `M`
itself, with the indeterminate `X` acting as `φ` (Mathlib's `Module.AEval' φ`,
where `X • m = φ m`). This file proves the bridge

  `conj_iff_nonempty_aeval_linearEquiv`:
      (∃ e : M ≃ₗ[K] M, e ∘ₗ φ = ψ ∘ₗ e)  ↔  Nonempty (AEval' φ ≃ₗ[K[X]] AEval' ψ)

i.e. `φ` and `ψ` are conjugate (similar) **iff** the K[X]-modules `AEval' φ`
and `AEval' ψ` are isomorphic. We also give the matrix-level corollary via
`Matrix.toLin'`.

## Why this is the right reduction

Combined with Mathlib's structure theorem for finitely generated modules over a
PID (`Module.equiv_directSum_of_isTorsion` in `Mathlib/Algebra/Module/PID.lean`),
which classifies a finitely generated torsion `K[X]`-module up to isomorphism by
its sequence of invariant factors, this bridge turns the geometric statement
"`A ∼ B ⟺ RCF(A) = RCF(B)`" into the algebraic statement "isomorphic modules
have the same invariant factors". One structural reduction replaces an
open-ended case analysis over canonical forms.

The forward direction repackages the construction Mathlib uses internally in
`LinearEquiv.isSemisimple_iff` (`Mathlib/LinearAlgebra/Semisimple.lean`) as a
standalone, reusable equivalence; the converse (module iso ⟹ conjugacy) does
not appear in Mathlib and is the new content here.

## What is proved (0 axioms, 0 sorries)

  * `aeval_linearEquiv_of_conj`     : intertwiner  ⟹  K[X]-module iso  (forward)
  * `conj_of_aeval_linearEquiv`     : K[X]-module iso  ⟹  intertwiner  (converse)
  * `conj_iff_nonempty_aeval_linearEquiv` : the full ⟺ at operator level
  * `aeval_isTorsion`               : for finite-dimensional `M`, `AEval' φ` is a
                                      torsion `K[X]`-module (the hypothesis of the
                                      PID structure theorem)
  * `matrix_conj_iff_nonempty_aeval_linearEquiv` : matrix-level ⟺ via `toLin'`

References:
- Hoffman & Kunze, "Linear Algebra" (1971), Chapter 7 (§7.1–7.3: the K[x]-module
  picture and the rational form).
- Dummit & Foote, "Abstract Algebra" (2004), §12.2 (rational canonical form as
  the invariant-factor decomposition of the F[x]-module).
- Mathlib: `Module.AEval'`, `LinearEquiv.ofAEval`, `Module.equiv_directSum_of_isTorsion`.
-/

import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open Polynomial Module Matrix

namespace RCFSimilarityBridge

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K M]

/-- **Forward direction.** An intertwiner `e ∘ φ = ψ ∘ e` (a `K`-linear
isomorphism conjugating `φ` to `ψ`) induces a `K[X]`-linear isomorphism of the
associated polynomial modules `AEval' φ ≃ₗ[K[X]] AEval' ψ`.

This is the construction Mathlib performs inside `LinearEquiv.isSemisimple_iff`,
extracted as a reusable equivalence. The underlying `K`-linear map is just `e`;
the point is that the intertwining hypothesis makes it commute with the
`X`-action (which is `φ` on the source and `ψ` on the target). -/
noncomputable def aeval_linearEquiv_of_conj
    (φ ψ : Module.End K M) (e : M ≃ₗ[K] M)
    (he : e.toLinearMap ∘ₗ φ = ψ ∘ₗ e.toLinearMap) :
    AEval' φ ≃ₗ[K[X]] AEval' ψ :=
  LinearEquiv.ofAEval _ (e.trans (AEval'.of ψ)) fun x ↦ by
    simpa [AEval'.X_smul_of] using LinearMap.congr_fun he x

/-- **Converse direction.** A `K[X]`-linear isomorphism `AEval' φ ≃ₗ[K[X]] AEval' ψ`
yields a `K`-linear isomorphism `e : M ≃ₗ[K] M` intertwining `φ` and `ψ`.

The map is `e = (of ψ)⁻¹ ∘ E ∘ (of φ)`, `K`-linear because `E` is in particular
`K`-linear. The intertwining identity is exactly the statement that `E` respects
the `X`-action: `X` acts as `φ` on the source and as `ψ` on the target. -/
theorem conj_of_aeval_linearEquiv
    (φ ψ : Module.End K M) (E : AEval' φ ≃ₗ[K[X]] AEval' ψ) :
    ∃ e : M ≃ₗ[K] M, e.toLinearMap ∘ₗ φ = ψ ∘ₗ e.toLinearMap := by
  -- `e` is `E` sandwiched between the canonical `K`-linear identifications `of`.
  refine ⟨((AEval'.of φ).trans (E.restrictScalars K)).trans (AEval'.of ψ).symm, ?_⟩
  ext m
  -- Unfold to a pointwise statement about `m : M`.
  show (AEval'.of ψ).symm (E (AEval'.of φ (φ m))) = ψ ((AEval'.of ψ).symm (E (AEval'.of φ m)))
  -- `of φ (φ m) = X • of φ m`, so we can pull `X` through the `K[X]`-linear `E`.
  have hX : AEval'.of φ (φ m) = (X : K[X]) • AEval'.of φ m := (AEval'.X_smul_of φ m).symm
  rw [hX, map_smul, AEval'.of_symm_X_smul]

/-- **The structural reduction.** Two endomorphisms `φ, ψ : M →ₗ[K] M` are
similar (conjugate by a `K`-linear automorphism) **iff** the `K[X]`-modules they
induce — `M` with `X` acting as `φ`, resp. as `ψ` — are isomorphic.

This is the algebraic heart of the rational canonical form: similarity *is*
isomorphism of `K[X]`-modules. Together with the PID structure theorem (which
classifies finitely generated torsion `K[X]`-modules by their invariant
factors), it explains why the invariant factors are a *complete* similarity
invariant, whereas the minimal polynomial alone (the largest invariant factor)
is not. -/
theorem conj_iff_nonempty_aeval_linearEquiv (φ ψ : Module.End K M) :
    (∃ e : M ≃ₗ[K] M, e.toLinearMap ∘ₗ φ = ψ ∘ₗ e.toLinearMap) ↔
      Nonempty (AEval' φ ≃ₗ[K[X]] AEval' ψ) :=
  ⟨fun ⟨e, he⟩ ↦ ⟨aeval_linearEquiv_of_conj φ ψ e he⟩,
   fun ⟨E⟩ ↦ conj_of_aeval_linearEquiv φ ψ E⟩

/-- For a finite-dimensional space `M`, the polynomial module `AEval' φ` is a
torsion `K[X]`-module: every element is killed by a nonzero polynomial, namely
the (monic, hence nonzero) characteristic polynomial of `φ`, which annihilates
the whole module by Cayley–Hamilton.

This is precisely the hypothesis `Module.IsTorsion` required by the PID
structure theorem `Module.equiv_directSum_of_isTorsion`, so it is the missing
link that lets one apply that classification to `AEval' φ`. -/
theorem aeval_isTorsion [FiniteDimensional K M] (φ : Module.End K M) :
    Module.IsTorsion K[X] (AEval' φ) := by
  intro x
  -- Transport `x` back to `M` along the canonical identification `of`.
  obtain ⟨m, rfl⟩ := (AEval'.of φ).surjective x
  -- The characteristic polynomial is monic, hence a nonzero divisor in `K[X]`.
  refine ⟨⟨φ.charpoly, mem_nonZeroDivisors_of_ne_zero φ.charpoly_monic.ne_zero⟩, ?_⟩
  -- `charpoly • x = aeval φ charpoly • x = 0` by Cayley–Hamilton.
  have hCH : (aeval φ) φ.charpoly = 0 := φ.aeval_self_charpoly
  show (φ.charpoly : K[X]) • (AEval'.of φ) m = 0
  rw [← AEval.of_aeval_smul, hCH]
  simp

/-- **Matrix-level corollary.** Two square matrices over `K` are similar — there
is an invertible `P` with `e = toLin' P` conjugating one to the other — iff the
`K[X]`-modules attached to the linear maps `Matrix.toLin' A` and `Matrix.toLin' B`
are isomorphic. This is the rational-canonical-form reduction in its classical
matrix phrasing. -/
theorem matrix_conj_iff_nonempty_aeval_linearEquiv
    {n : Type*} [Fintype n] [DecidableEq n] (A B : Matrix n n K) :
    (∃ e : (n → K) ≃ₗ[K] (n → K),
        e.toLinearMap ∘ₗ Matrix.toLin' A = (Matrix.toLin' B) ∘ₗ e.toLinearMap) ↔
      Nonempty (AEval' (Matrix.toLin' A) ≃ₗ[K[X]] AEval' (Matrix.toLin' B)) :=
  conj_iff_nonempty_aeval_linearEquiv (Matrix.toLin' A) (Matrix.toLin' B)

end RCFSimilarityBridge
