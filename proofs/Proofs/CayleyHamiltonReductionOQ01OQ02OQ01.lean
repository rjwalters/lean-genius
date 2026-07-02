/-
  Cayley–Hamilton via Nilpotency Reduction
  (cayley-hamilton-reduction-oq-01-oq-02-oq-01)

  Question: Can the general Cayley–Hamilton theorem (charpoly(M)(M) = 0) be
  proved by *reducing to the nilpotent case*, rather than appealing to the
  abstract algebraic proof (`aeval_self_charpoly`)?  Concretely: on each
  generalized eigenspace `Gλ = ker (M - λ)^n` the operator `M - λ` is
  nilpotent, so Cayley–Hamilton for `M` should follow from Cayley–Hamilton for
  nilpotent operators together with the generalized-eigenspace decomposition.

  This file proves the **base cases** of that reduction, all *independently of*
  `aeval_self_charpoly`:

  1. **Nilpotent index bound** (`nilpotent_pow_finrank_eq_zero`):
     a nilpotent endomorphism of an `n`-dimensional space satisfies `φ^n = 0`.
     Proof: the kernel chain `ker φ ⊆ ker φ² ⊆ ...` stabilises by dimension
     `n` (`Module.End.ker_pow_le_ker_pow_finrank`); this is CH-free.

  2. **Cayley–Hamilton for nilpotent operators** (`nilpotent_aeval_charpoly`,
     `matrix_nilpotent_aeval_charpoly`): combine `φ^n = 0` with the fact that a
     nilpotent operator has `charpoly = X^n`.  The latter comes from
     `IsNilpotent.charpoly_eq_X_pow_finrank` / the reverse-polynomial argument
     `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`, neither of which uses
     `aeval_self_charpoly`.  So this is a genuinely independent proof of
     Cayley–Hamilton on the nilpotent case.

  3. **Single-eigenvalue reduction** (`matrix_single_eigenvalue_charpoly`,
     `matrix_single_eigenvalue_aeval_charpoly`): if `M - λ·I` is nilpotent
     (i.e. `M` has a single eigenvalue `λ`), then `charpoly(M) = (X - λ)^n` and
     `charpoly(M)(M) = 0`.  This is the first genuinely non-nilpotent case, and
     it is obtained from the nilpotent case purely by the affine translation
     `charpoly(M - λ)(X) = charpoly(M)(X + λ)` (`Matrix.charpoly_sub_scalar`).
     It demonstrates that the "reduce to nilpotent" strategy really does reduce
     a nontrivial case.

  What remains (documented, not proved here): the *multi*-eigenvalue reduction
  over an algebraically closed field, which requires assembling the generalized
  eigenspace decomposition `⨆ μ, genEigenspace M μ = ⊤`
  (`Module.End.iSup_genEigenspace_eq_top`) with the single-eigenvalue result on
  each summand.  That is the remaining content of the full reduction.

  References:
  - CayleyHamiltonReductionOQ01OQ02.lean: efficient minpoly reduction (parent)
  - Mathlib.LinearAlgebra.Eigenspace.Zero: `IsNilpotent.charpoly_eq_X_pow_finrank`
  - Axler, "Linear Algebra Done Right" §8 (generalized eigenspaces, Lemma 8.11)
-/
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

namespace CayleyHamiltonNilpotentReduction

open Module Polynomial Matrix

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {n : Type*} [Fintype n] [DecidableEq n]

-- ============================================================
-- PART I: Nilpotency index bound (CH-free)
-- ============================================================

/-- A nilpotent endomorphism of a finite-dimensional space is killed by its
    dimensionth power: `φ^(finrank K V) = 0`.

    This is the quantitative form of "the nilpotency index is at most the
    dimension".  It is proved from the stabilisation of the kernel chain
    `ker φ ⊆ ker φ² ⊆ ...` (`Module.End.ker_pow_le_ker_pow_finrank`) and makes
    **no** appeal to the Cayley–Hamilton theorem. -/
theorem nilpotent_pow_finrank_eq_zero {φ : Module.End K V} (h : IsNilpotent φ) :
    φ ^ (finrank K V) = 0 := by
  obtain ⟨k, hk⟩ := h
  have hker : LinearMap.ker (φ ^ k) = ⊤ := by rw [hk, LinearMap.ker_zero]
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← hker]
  exact Module.End.ker_pow_le_ker_pow_finrank φ k

-- ============================================================
-- PART II: Cayley–Hamilton for nilpotent operators (CH-free)
-- ============================================================

/-- **Cayley–Hamilton for nilpotent endomorphisms**, proved independently of
    `aeval_self_charpoly`.

    Ingredients: `IsNilpotent.charpoly_eq_X_pow_finrank` (charpoly `= X^n`, via
    the reverse-polynomial / nilpotent-coefficient argument) and
    `nilpotent_pow_finrank_eq_zero` (`φ^n = 0`, via the kernel chain). -/
theorem nilpotent_aeval_charpoly {φ : Module.End K V} (h : IsNilpotent φ) :
    aeval φ φ.charpoly = 0 := by
  rw [IsNilpotent.charpoly_eq_X_pow_finrank h, map_pow, aeval_X]
  exact nilpotent_pow_finrank_eq_zero h

/-- Matrix form of the nilpotency index bound: for a nilpotent `n × n` matrix,
    `M^(card n) = 0`.  Transported from `nilpotent_pow_finrank_eq_zero` along the
    algebra equivalence `Matrix.toLinAlgEquiv'`. -/
theorem matrix_isNilpotent_pow_card_eq_zero {M : Matrix n n K} (h : IsNilpotent M) :
    M ^ (Fintype.card n) = 0 := by
  have hφ : IsNilpotent (Matrix.toLinAlgEquiv' M) := h.map Matrix.toLinAlgEquiv'
  have key : (Matrix.toLinAlgEquiv' M) ^ (Fintype.card n) = 0 := by
    have hpow := nilpotent_pow_finrank_eq_zero hφ
    rwa [Module.finrank_fintype_fun_eq_card] at hpow
  have hmap : Matrix.toLinAlgEquiv' (M ^ Fintype.card n) = Matrix.toLinAlgEquiv' 0 := by
    rw [map_pow, map_zero]; exact key
  exact Matrix.toLinAlgEquiv'.injective hmap

/-- For a nilpotent matrix, `charpoly(M) = X^(card n)`.  This uses only the
    reverse-polynomial argument `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent`
    (a nilpotent polynomial over a reduced ring is zero), not Cayley–Hamilton. -/
theorem matrix_nilpotent_charpoly {M : Matrix n n K} (h : IsNilpotent M) :
    M.charpoly = X ^ (Fintype.card n) := by
  rw [← sub_eq_zero]
  exact (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero

/-- **Cayley–Hamilton for nilpotent matrices**, independent of
    `aeval_self_charpoly`: `charpoly(M)(M) = 0`. -/
theorem matrix_nilpotent_aeval_charpoly {M : Matrix n n K} (h : IsNilpotent M) :
    aeval M M.charpoly = 0 := by
  rw [matrix_nilpotent_charpoly h, map_pow, aeval_X]
  exact matrix_isNilpotent_pow_card_eq_zero h

-- ============================================================
-- PART III: Single-eigenvalue reduction (M - λ·I nilpotent)
-- ============================================================

/-- If `M - λ·I` is nilpotent (equivalently, `M` has a single eigenvalue `λ`),
    then `charpoly(M) = (X - λ)^(card n)`.

    This is the affine-translation step of the nilpotency reduction: the
    nilpotent case gives `charpoly(M - λ·I) = X^n`, and
    `Matrix.charpoly_sub_scalar` says `charpoly(M - λ·I)(X) = charpoly(M)(X + λ)`;
    substituting `X ↦ X - λ` recovers `charpoly(M) = (X - λ)^n`. -/
theorem matrix_single_eigenvalue_charpoly {M : Matrix n n K} {μ : K}
    (h : IsNilpotent (M - Matrix.scalar n μ)) :
    M.charpoly = (X - C μ) ^ (Fintype.card n) := by
  have hN : (M - Matrix.scalar n μ).charpoly = X ^ (Fintype.card n) :=
    matrix_nilpotent_charpoly h
  rw [Matrix.charpoly_sub_scalar] at hN
  -- hN : M.charpoly.comp (X + C μ) = X ^ card
  have key := congrArg (fun p : K[X] => p.comp (X - C μ)) hN
  simpa only [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.one_comp,
    sub_add_cancel, Polynomial.comp_X] using key

/-- **Cayley–Hamilton for single-eigenvalue matrices**, independent of
    `aeval_self_charpoly`: if `M - λ·I` is nilpotent then `charpoly(M)(M) = 0`.

    This is the first genuinely non-nilpotent case handled by the reduction:
    `charpoly(M)(M) = (M - λ·I)^(card n) = 0` since `M - λ·I` is nilpotent. -/
theorem matrix_single_eigenvalue_aeval_charpoly {M : Matrix n n K} {μ : K}
    (h : IsNilpotent (M - Matrix.scalar n μ)) :
    aeval M M.charpoly = 0 := by
  rw [matrix_single_eigenvalue_charpoly h, map_pow, map_sub, aeval_X, aeval_C]
  have hs : algebraMap K (Matrix n n K) μ = Matrix.scalar n μ := rfl
  rw [hs]
  exact matrix_isNilpotent_pow_card_eq_zero h

end CayleyHamiltonNilpotentReduction

/-
  ## Summary

  **Problem**: prove Cayley–Hamilton by reducing to the nilpotent case rather
  than using the abstract algebraic proof `aeval_self_charpoly`.

  **Status**: base cases fully proved (0 sorries, 0 axioms), all CH-free.

  **Proved (7 theorems)**:
  - `nilpotent_pow_finrank_eq_zero`  — nilpotent `φ ⟹ φ^(finrank) = 0` (kernel chain)
  - `nilpotent_aeval_charpoly`       — CH for nilpotent endomorphisms
  - `matrix_isNilpotent_pow_card_eq_zero` — nilpotent `M ⟹ M^(card) = 0`
  - `matrix_nilpotent_charpoly`      — nilpotent `M ⟹ charpoly = X^(card)`
  - `matrix_nilpotent_aeval_charpoly`— CH for nilpotent matrices
  - `matrix_single_eigenvalue_charpoly`      — single eigenvalue `⟹ charpoly = (X-λ)^(card)`
  - `matrix_single_eigenvalue_aeval_charpoly`— CH for single-eigenvalue matrices

  **Independence note**: none of the seven theorems invoke `aeval_self_charpoly`
  (Mathlib's abstract Cayley–Hamilton).  The two facts used —
  `IsNilpotent.charpoly_eq_X_pow_finrank` and
  `Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent` — are both proved in
  Mathlib via the reverse polynomial `charpolyRev` and the observation that a
  nilpotent polynomial over a reduced ring vanishes, *not* via Cayley–Hamilton.

  **Remaining for the full reduction**: assemble the single-eigenvalue result on
  each generalized eigenspace using `Module.End.iSup_genEigenspace_eq_top` (valid
  over an algebraically closed field).  That step — turning the local nilpotent
  bound into the global `charpoly(M)(M) = 0` for arbitrary `M` — is the content
  of the multi-eigenvalue reduction and is left as future work.
-/
