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
  gap: only the reverse divisibility (`∏ ∣ minpoly`) still requires assembling the
  primary decomposition.

  This file additionally supplies the **exactness** ingredient that reverse
  divisibility needs (previously the documented blocker `maxGenEigenspaceIndex_exact`):

    * `genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex` — below the limit index the
      generalized-eigenspace chain strictly increases, so `maxGenEigenspaceIndex` is
      the *exact* nilpotency index of `f - μ`, not just an upper bound.  Proved from
      Mathlib's `Module.End.ker_pow_constant` plus the least-index characterization
      of `maxGenEigenspaceIndex` (= `monotonicSequenceLimitIndex`).
    * `exists_mem_maxGenEigenspace_pow_pred_ne_zero` — the concrete witness: a vector
      in the maximal generalized eigenspace not killed by `(f - μ)^{e-1}`.

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

/-- **Exactness of the generalized-eigenspace index.**

    Below `maxGenEigenspaceIndex` the generalized-eigenspace chain is *strictly*
    increasing: for every `k < f.maxGenEigenspaceIndex μ`,

        `f.genEigenspace μ k < f.genEigenspace μ (k + 1)`.

    Equivalently `maxGenEigenspaceIndex f μ` is the *exact* nilpotency index of
    `f - μ` on the maximal generalized eigenspace, not merely an upper bound: the
    chain cannot already be constant strictly below its limit index.

    This is the missing ingredient (`maxGenEigenspaceIndex_exact`) that the reverse
    divisibility `∏ (X - μ)^{e_μ} ∣ minpoly K f` requires.  It follows from
    Mathlib's one-step kernel-stabilization lemma `Module.End.ker_pow_constant`
    (equality of two consecutive kernels of a power forces the chain constant
    afterwards) together with the fact that `maxGenEigenspaceIndex` is, by
    definition, the *least* index at which the chain stabilizes. -/
theorem genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) {k : ℕ} (hk : k < f.maxGenEigenspaceIndex μ) :
    f.genEigenspace μ (k : ℕ∞) < f.genEigenspace μ ((k : ℕ∞) + 1) := by
  -- The chain is monotone, so it suffices to rule out equality at this step.
  refine lt_of_le_of_ne ((f.genEigenspace μ).monotone (by exact_mod_cast Nat.le_succ k)) ?_
  intro heq
  -- Equality of two consecutive generalized eigenspaces = equality of two
  -- consecutive kernels of powers of `f - μ`.
  have hker : LinearMap.ker ((f - μ • 1) ^ k)
      = LinearMap.ker ((f - μ • 1) ^ k.succ) := by
    have h1 : f.genEigenspace μ (k : ℕ∞) = LinearMap.ker ((f - μ • 1) ^ k) :=
      genEigenspace_nat
    have h2 : f.genEigenspace μ ((k + 1 : ℕ) : ℕ∞)
        = LinearMap.ker ((f - μ • 1) ^ (k + 1)) := genEigenspace_nat
    have hcast : ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; ring
    rw [Nat.succ_eq_add_one, ← h1, ← h2, hcast]
    exact heq
  -- `ker_pow_constant` then makes the kernel chain constant from `k` onwards, so
  -- the generalized-eigenspace chain is constant from `k` onwards too.
  have hstab : ∀ d : ℕ,
      f.genEigenspace μ (k : ℕ∞) = f.genEigenspace μ ((k + d : ℕ) : ℕ∞) := by
    intro d
    have hk' := Module.End.ker_pow_constant (f := f - μ • 1) (k := k) hker d
    rw [(genEigenspace_nat : f.genEigenspace μ (k : ℕ∞) = _),
        (genEigenspace_nat : f.genEigenspace μ ((k + d : ℕ) : ℕ∞) = _)]
    exact hk'
  -- Hence `k` is a stabilization index of the defining monotone sequence.
  have hmem : ∀ m : ℕ, k ≤ m →
      ((f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom) k
        = ((f.genEigenspace μ).comp WithTop.coeOrderHom.toOrderHom) m := by
    intro m hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    simpa using hstab d
  -- But `maxGenEigenspaceIndex` is the *least* such index, contradicting `k < it`.
  have hle : f.maxGenEigenspaceIndex μ ≤ k := Nat.sInf_le hmem
  exact absurd hk (not_lt.mpr hle)

/-- **The index is the exact nilpotency degree.**  When `maxGenEigenspaceIndex f μ`
    is positive there is a vector `v` in the maximal generalized eigenspace with
    `(f - μ)^{e-1} v ≠ 0` (while `(f - μ)^e v = 0`).  This is the concrete witness
    that distinguishes the *exact* product formula from the forward divisibility:
    no smaller exponent than `e_μ = maxGenEigenspaceIndex f μ` annihilates the
    whole `μ`-summand. -/
theorem exists_mem_maxGenEigenspace_pow_pred_ne_zero [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) (hpos : 0 < f.maxGenEigenspaceIndex μ) :
    ∃ v ∈ f.maxGenEigenspace μ,
      ((f - μ • 1) ^ (f.maxGenEigenspaceIndex μ - 1)) v ≠ 0 := by
  set e := f.maxGenEigenspaceIndex μ with he
  have hlt := genEigenspace_lt_succ_of_lt_maxGenEigenspaceIndex f μ (k := e - 1) (by omega)
  have hcast : ((e - 1 : ℕ) : ℕ∞) + 1 = ((e : ℕ) : ℕ∞) := by
    have hsub : e - 1 + 1 = e := by omega
    calc ((e - 1 : ℕ) : ℕ∞) + 1 = (((e - 1) + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ = ((e : ℕ) : ℕ∞) := by rw [hsub]
  rw [hcast] at hlt
  obtain ⟨v, hv_mem, hv_not⟩ := SetLike.exists_of_lt hlt
  refine ⟨v, ?_, ?_⟩
  · rw [maxGenEigenspace_eq]; exact hv_mem
  · rw [genEigenspace_nat, LinearMap.mem_ker] at hv_not
    exact hv_not

end JordanMinpolyOQ01OQ01
