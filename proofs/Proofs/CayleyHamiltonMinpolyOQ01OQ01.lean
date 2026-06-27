/-
  The minimal polynomial divides the generalized-eigenspace product
  Open Question (cayley-hamilton-minpoly-oq-01-oq-01)

  Parent: cayley-hamilton-minpoly-oq-01 (Jordan Canonical Form and the Minimal Polynomial)

  The parent file axiomatizes the full JCF–minpoly product formula

      minpoly K f = ∏_{μ} (X - μ)^{e_μ},   e_μ = maxGenEigenspaceIndex f μ

  as `minpoly_product_formula`, noting that Mathlib 4.26.0 does not yet provide
  the explicit Jordan block matrix decomposition.

  This file proves the FORWARD divisibility direction of that formula WITHOUT any
  Jordan block infrastructure — purely from Mathlib's generalized-eigenspace
  theory (`iSup_maxGenEigenspace_eq_top`):

      minpoly K f  ∣  ∏_{μ eigenvalue} (X - μ)^{e_μ}.

  The key idea: over an algebraically closed field the maximal generalized
  eigenspaces span V (Axler 8.21 = `iSup_maxGenEigenspace_eq_top`). On the
  μ-summand the factor `(X - μ)^{e_μ}` already annihilates, and since the factors
  commute (the product lives in the commutative ring K[X]) the whole product
  annihilates f. Hence the product is a multiple of the minimal polynomial.

  This converts the parent's `minpoly_product_formula` axiom into a one-sided
  gap: only the reverse divisibility (`∏ ∣ minpoly`, equivalently the exactness
  `maxGenEigenspaceIndex_exact`) still requires the largest-Jordan-block witness.

  Status: 0 sorries, 0 axioms. Fully verified against Mathlib 4.26.0.

  References:
  - Axler, "Linear Algebra Done Right", Lemma 8.21 (generalized eigenspaces span)
  - Mathlib: LinearAlgebra.Eigenspace.{Basic, Triangularizable}
-/

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace JordanMinpolyOQ01OQ01

/-- If `ν` is not an eigenvalue of `f`, its maximal generalized eigenspace is trivial.
    (Contrapositive: a nonzero generalized eigenvector forces an eigenvalue.) -/
theorem maxGenEigenspace_eq_bot_of_not_hasEigenvalue [FiniteDimensional K V]
    {f : Module.End K V} {ν : K} (h : ¬ f.HasEigenvalue ν) :
    f.maxGenEigenspace ν = ⊥ := by
  by_contra hbot
  rw [maxGenEigenspace_eq] at hbot
  exact h (hasEigenvalue_of_hasGenEigenvalue (hasGenEigenvalue_iff.mpr hbot))

/-- `aeval f` of the factor `(X - C ν)^k` is the endomorphism `(f - ν • 1)^k`,
    matching the form used by `genEigenspace_nat`. -/
theorem aeval_linear_factor_pow (f : Module.End K V) (ν : K) (k : ℕ) :
    aeval f ((X - C ν) ^ k) = (f - ν • 1) ^ k := by
  rw [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- **Forward divisibility of the JCF product formula.**

    Over an algebraically closed field, the minimal polynomial of `f` divides the
    product over the eigenvalues of `(X - μ)^{maxGenEigenspaceIndex f μ}`.

    Proof: the product polynomial annihilates `f`. The maximal generalized
    eigenspaces span `V`; on the `ν`-eigenspace the factor `(X - ν)^{e_ν}`
    already kills every vector, and the remaining (commuting) factors then map `0`
    to `0`. So the product evaluates to `0` on a spanning family, hence is `0`, and
    `minpoly.dvd` finishes. No Jordan block matrices required. -/
theorem minpoly_dvd_maxGenEigenspace_product [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    minpoly K f ∣
      ∏ μ ∈ (finite_hasEigenvalue f).toFinset, (X - C μ) ^ f.maxGenEigenspaceIndex μ := by
  classical
  set s := (finite_hasEigenvalue f).toFinset with hs
  -- It suffices that the product annihilates f.
  refine minpoly.dvd K f ?_
  -- Show the endomorphism aeval f (∏ ...) is zero by checking its kernel is ⊤.
  rw [← LinearMap.ker_eq_top, eq_top_iff, ← iSup_maxGenEigenspace_eq_top f]
  refine iSup_le fun ν => ?_
  intro v hv
  rw [LinearMap.mem_ker]
  by_cases hν : ν ∈ s
  · -- ν is an eigenvalue: pull out its factor, which annihilates v.
    have efac : ((f - ν • 1) ^ f.maxGenEigenspaceIndex ν) v = 0 := by
      have hv' : v ∈ f.genEigenspace ν (f.maxGenEigenspaceIndex ν) := by
        rw [← maxGenEigenspace_eq]; exact hv
      rwa [genEigenspace_nat, LinearMap.mem_ker] at hv'
    rw [show (∏ μ ∈ s, (X - C μ) ^ f.maxGenEigenspaceIndex μ)
          = (∏ μ ∈ s.erase ν, (X - C μ) ^ f.maxGenEigenspaceIndex μ)
            * (X - C ν) ^ f.maxGenEigenspaceIndex ν
        from (Finset.prod_erase_mul s _ hν).symm,
       map_mul, Module.End.mul_apply, aeval_linear_factor_pow, efac, map_zero]
  · -- ν is not an eigenvalue: its eigenspace is trivial, so v = 0.
    have hnev : ¬ f.HasEigenvalue ν := fun hev =>
      hν ((Set.Finite.mem_toFinset _).mpr hev)
    have hv0 : v = 0 := by
      have : v ∈ (⊥ : Submodule K V) := by
        rw [← maxGenEigenspace_eq_bot_of_not_hasEigenvalue hnev]; exact hv
      simpa using this
    rw [hv0, map_zero]

end JordanMinpolyOQ01OQ01
