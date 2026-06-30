import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import Proofs.SchursLemma

/-!
# Schur's Lemma OQ-02 — the endomorphism algebra is *exactly* the scalars

## What This Proves

The parent file (`SchursLemma.lean`) proves the **scalar form** of Schur's Lemma:
over an algebraically closed field `k`, every `A`-linear endomorphism of a
finite-dimensional simple `A`-module `M` is multiplication by *some* scalar
`c : k` (`schur_endomorphism_scalar`).  Existence of `c` is the part used to *find*
a scalar; this file supplies the complementary half — **uniqueness** — and packages
the two into the structural statement that the endomorphism algebra collapses
completely onto `k`.

Concretely:

* `schur_scalar_unique` — the scalar is **unique**: `∃! c, ∀ m, f m = c • m`.
* `schur_scalar_bijective` — the scalar map `c ↦ c • id : k → End_A(M)` is a
  **bijection**.  (Injective by uniqueness; surjective by the parent's scalar form.)
* `scalarEquiv` — hence a `k`-linear equivalence `k ≃ₗ[k] End_A(M)`.
* `finrank_end_eq_one` — therefore `dim_k End_A(M) = 1`: the endomorphism algebra
  of an absolutely simple module is one-dimensional, i.e. *exactly* the scalars.

This is the precise sense in which a finite-dimensional simple module over an
algebraically closed field is **absolutely simple**: its commutant is just `k`.
It is the structural upgrade of the parent's existence statement and the engine
behind the dimension counts of character theory.

## Approach

Uniqueness is the one new analytic ingredient.  If `c • v = c' • v` for a nonzero
vector `v` (which exists since a simple module is nontrivial), then `(c - c') • v = 0`;
because `M` is a vector space over the field `k`, scaling by the inverse of a nonzero
`c - c'` would force `v = 0`, a contradiction.  Everything else is bookkeeping on top
of the parent results.

## References
* Serre, *Linear Representations of Finite Groups*, §2.2 (Schur's lemma and its
  corollary that the commutant of an irreducible is the scalars).
* Curtis–Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §27 (absolutely simple modules).
-/

open Module

namespace SchursLemmaOQ02

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [IsSimpleModule A M] [FiniteDimensional k M]

/-- Cancellation for the `k`-action on a nonzero vector of a vector space: if two
scalars agree after scaling a single nonzero vector, they are equal. -/
private theorem smul_right_cancel₀ {c c' : k} {v : M} (hv : v ≠ 0)
    (h : c • v = c' • v) : c = c' := by
  by_contra hcc
  have hkey : (c - c') • v = 0 := by rw [sub_smul, h, sub_self]
  have hne : c - c' ≠ 0 := sub_ne_zero.mpr hcc
  apply hv
  have hcong := congrArg (fun x => (c - c')⁻¹ • x) hkey
  simpa [smul_smul, inv_mul_cancel₀ hne] using hcong

/-- **Uniqueness of the Schur scalar.** Over an algebraically closed field, the
scalar `c` with `f = c • id` (whose existence is `schur_endomorphism_scalar`) is
unique. -/
theorem schur_scalar_unique (f : M →ₗ[A] M) : ∃! c : k, ∀ m, f m = c • m := by
  obtain ⟨c, hc⟩ := SchursLemma.schur_endomorphism_scalar (k := k) f
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have h1 : c' • v = c • v := (hc' v).symm.trans (hc v)
  exact smul_right_cancel₀ hv h1

/-- The scalar map `c ↦ c • id : k → End_A(M)` is **injective** (Schur uniqueness). -/
theorem schur_scalar_injective :
    Function.Injective (fun c : k => (c • LinearMap.id : Module.End A M)) := by
  intro c c' h
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have hv2 : c • v = c' • v := by
    have := LinearMap.congr_fun h v
    simpa using this
  exact smul_right_cancel₀ hv hv2

/-- The scalar map `c ↦ c • id : k → End_A(M)` is **surjective** (Schur scalar form). -/
theorem schur_scalar_surjective :
    Function.Surjective (fun c : k => (c • LinearMap.id : Module.End A M)) := by
  intro f
  obtain ⟨c, hc⟩ := SchursLemma.schur_endomorphism_eq_smul_id (k := k) f
  exact ⟨c, hc.symm⟩

/-- **The endomorphism algebra is exactly the scalars.** The map `c ↦ c • id` is a
bijection `k → End_A(M)`. -/
theorem schur_scalar_bijective :
    Function.Bijective (fun c : k => (c • LinearMap.id : Module.End A M)) :=
  ⟨schur_scalar_injective, schur_scalar_surjective⟩

/-- The scalar map packaged as a `k`-linear map `k →ₗ[k] End_A(M)`. -/
noncomputable def scalarLinearMap : k →ₗ[k] Module.End A M where
  toFun c := c • LinearMap.id
  map_add' a b := by rw [add_smul]
  map_smul' a b := by
    simp only [RingHom.id_apply, smul_eq_mul, mul_smul]

/-- The `k`-linear equivalence `k ≃ₗ[k] End_A(M)` realizing the commutant as the
scalars. -/
noncomputable def scalarEquiv : k ≃ₗ[k] Module.End A M :=
  LinearEquiv.ofBijective scalarLinearMap schur_scalar_bijective

/-- **The commutant is one-dimensional.** The endomorphism algebra of a
finite-dimensional simple `A`-module over an algebraically closed field is
one-dimensional over `k` — the precise statement that the module is *absolutely
simple*. -/
theorem finrank_end_eq_one : Module.finrank k (Module.End A M) = 1 := by
  rw [← LinearEquiv.finrank_eq scalarEquiv]
  exact finrank_self k

#check @schur_scalar_unique
#check @schur_scalar_bijective
#check @finrank_end_eq_one

end SchursLemmaOQ02
