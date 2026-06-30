import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-
# Primary Decomposition from the Minimal Polynomial

## What This Proves
This file answers the open question raised in `CayleyHamiltonOQ01` (Minimal
Polynomial Reduction and Annihilator Theory):

> Extend to primary decomposition: μ_T = ∏ pᵢ^{eᵢ} (distinct irreducibles) and
> the corresponding V = ⊕ ker(pᵢ^{eᵢ}(T)).

Given an endomorphism `T : V →ₗ[K] V` of a vector space over a field `K`, and a
factorisation of the minimal polynomial into **pairwise coprime** factors
`μ_T = ∏ᵢ qᵢ^{eᵢ}` (the distinct-irreducible-prime-power form), the space splits
as an internal direct sum of the `T`-invariant generalized eigenspaces
`Wᵢ = ker(qᵢ^{eᵢ}(T))`:

    V = ⨁ᵢ ker( (qᵢ^{eᵢ})(T) ).

This is the classical **Primary Decomposition Theorem**, the engine behind the
rational canonical form and (over an algebraically closed field) the Jordan form.

## Main results
* `iSup_ker_aeval_eq_ker_aeval_prod` — for a finite family of pairwise coprime
  polynomials, the supremum of the kernels of `qᵢ(T)` equals the kernel of the
  product `(∏ qᵢ)(T)`. (Iterated CRT for the action of `K[X]` on `V`.)
* `ker_aeval_mapsTo` — each kernel `ker(p(T))` is a `T`-invariant subspace.
* `iSupIndep_ker_aeval` — the kernels of a pairwise coprime family are
  independent (the sum is direct).
* `iSup_ker_aeval_eq_top` — if the product annihilates `T`, the kernels span `V`.
* `isInternal_ker_aeval` — the kernels form an internal direct sum decomposition
  of `V` (general coprime form).
* `isInternal_primaryDecomposition_of_minpoly` — the headline: specialising to a
  pairwise-coprime prime-power factorisation of the minimal polynomial gives the
  primary decomposition `V = ⨁ᵢ ker(qᵢ^{eᵢ}(T))`.

## Method
The whole argument is built from Mathlib's binary kernel lemmas
(`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime` and
`Polynomial.disjoint_ker_aeval_of_isCoprime`) lifted to an arbitrary finite
family by `Finset` induction and the `IsCoprime.prod_right` coprimality combinator.
No finiteness or algebraic-closure hypotheses on `V` are needed for the general
statement; the minimal-polynomial corollary only uses `minpoly.aeval`.

## Extends
- `CayleyHamiltonOQ01.lean` (minimal polynomial reduction & annihilator theory)

## Status
0 sorries, 0 axioms. Fully machine-verified.
-/

open Polynomial Submodule LinearMap Finset

namespace CayleyHamiltonOQ01OQ04

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (T : V →ₗ[K] V)

/-- Each "primary" subspace `ker (p(T))` is invariant under `T`, because every
polynomial in `T` commutes with `T`. -/
theorem ker_aeval_mapsTo (p : K[X]) :
    ∀ x ∈ LinearMap.ker (aeval T p), T x ∈ LinearMap.ker (aeval T p) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have hcomm : (aeval T p) * T = T * (aeval T p) := by
    have e1 : (aeval T p) * T = aeval T (p * X) := by rw [map_mul, aeval_X]
    have e2 : T * (aeval T p) = aeval T (X * p) := by rw [map_mul, aeval_X]
    rw [e1, e2, mul_comm]
  calc aeval T p (T x) = ((aeval T p) * T) x := by rw [Module.End.mul_apply]
    _ = (T * (aeval T p)) x := by rw [hcomm]
    _ = T (aeval T p x) := by rw [Module.End.mul_apply]
    _ = T 0 := by rw [hx]
    _ = 0 := by rw [map_zero]

/-- **Iterated Chinese Remainder Theorem for `K[X]` acting on `V`.**
For a finite family of pairwise coprime polynomials, the supremum of the kernels
`ker(qᵢ(T))` equals the kernel of the product `(∏ qᵢ)(T)`. -/
theorem iSup_ker_aeval_eq_ker_aeval_prod {ι : Type*} (p : ι → K[X]) {s : Finset ι}
    (h : (s : Set ι).Pairwise (fun i j => IsCoprime (p i) (p j))) :
    (⨆ i ∈ s, LinearMap.ker (aeval T (p i))) =
      LinearMap.ker (aeval T (∏ i ∈ s, p i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Module.End.one_eq_id, LinearMap.ker_id]
  | @insert a s ha ih =>
      have hsub : (s : Set ι) ⊆ (insert a s : Finset ι) :=
        Finset.coe_subset.mpr (Finset.subset_insert a s)
      have hps : (s : Set ι).Pairwise (fun i j => IsCoprime (p i) (p j)) := h.mono hsub
      have hcop : IsCoprime (p a) (∏ i ∈ s, p i) := by
        refine IsCoprime.prod_right (fun i hi => ?_)
        have hai : a ≠ i := fun he => ha (he ▸ hi)
        exact h (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi) hai
      rw [Finset.iSup_insert, ih hps, Finset.prod_insert ha,
        sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop]

variable {ι : Type*} [Fintype ι] (p : ι → K[X])

/-- The kernels of a pairwise coprime family are **independent**: their sum is
direct.  Each `ker(pᵢ(T))` is disjoint from the supremum of the others, since
`pᵢ` is coprime to the product of the remaining factors. -/
theorem iSupIndep_ker_aeval (hpw : Pairwise (fun i j => IsCoprime (p i) (p j))) :
    iSupIndep (fun i => LinearMap.ker (aeval T (p i))) := by
  classical
  have huniv : (Set.univ : Set ι).Pairwise (fun i j => IsCoprime (p i) (p j)) :=
    Set.pairwise_univ.mpr hpw
  rw [iSupIndep_def]
  intro i
  -- Rewrite the supremum over `j ≠ i` as a kernel of a product over `univ.erase i`.
  have herase : (Finset.univ.erase i : Set ι).Pairwise (fun i j => IsCoprime (p i) (p j)) :=
    huniv.mono (by simp)
  have hsup :
      (⨆ (j) (_ : j ≠ i), LinearMap.ker (aeval T (p j))) =
        LinearMap.ker (aeval T (∏ j ∈ Finset.univ.erase i, p j)) := by
    rw [← iSup_ker_aeval_eq_ker_aeval_prod T p herase]
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  rw [hsup]
  -- `pᵢ` is coprime to the product of the remaining factors.
  have hcop : IsCoprime (p i) (∏ j ∈ Finset.univ.erase i, p j) := by
    refine IsCoprime.prod_right (fun j hj => ?_)
    exact hpw (Finset.ne_of_mem_erase hj).symm
  exact disjoint_ker_aeval_of_isCoprime T hcop

/-- If the product of a pairwise coprime family annihilates `T`, the kernels
span the whole space. -/
theorem iSup_ker_aeval_eq_top (hpw : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hprod : aeval T (∏ i, p i) = 0) :
    (⨆ i, LinearMap.ker (aeval T (p i))) = ⊤ := by
  classical
  have huniv : ((Finset.univ : Finset ι) : Set ι).Pairwise (fun i j => IsCoprime (p i) (p j)) := by
    rw [Finset.coe_univ]; exact Set.pairwise_univ.mpr hpw
  have key : (⨆ i, LinearMap.ker (aeval T (p i))) =
      LinearMap.ker (aeval T (∏ i, p i)) := by
    rw [← iSup_ker_aeval_eq_ker_aeval_prod T p huniv]
    simp only [Finset.mem_univ, iSup_true]
  rw [key, hprod, LinearMap.ker_zero]

/-- **Primary decomposition (general coprime form).**
If `T : V →ₗ[K] V` is annihilated by the product of a finite family of pairwise
coprime polynomials, then `V` is the internal direct sum of the kernels
`ker(pᵢ(T))`. -/
theorem isInternal_ker_aeval [DecidableEq ι] (hpw : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hprod : aeval T (∏ i, p i) = 0) :
    DirectSum.IsInternal (fun i => LinearMap.ker (aeval T (p i))) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨iSupIndep_ker_aeval T p hpw, iSup_ker_aeval_eq_top T p hpw hprod⟩

/-- **Primary Decomposition Theorem.**
Let `μ_T = ∏ᵢ qᵢ^{eᵢ}` be a factorisation of the minimal polynomial of `T` into
pairwise coprime prime powers (the distinct-irreducibles form).  Then `V`
decomposes as the internal direct sum of the primary components
`Wᵢ = ker(qᵢ^{eᵢ}(T))`:

    V = ⨁ᵢ ker( (qᵢ^{eᵢ})(T) ).

Each component `Wᵢ` is `T`-invariant (`ker_aeval_mapsTo`). -/
theorem isInternal_primaryDecomposition_of_minpoly [DecidableEq ι] (q : ι → K[X]) (e : ι → ℕ)
    (hq : Pairwise (fun i j => IsCoprime (q i) (q j)))
    (hmin : minpoly K T = ∏ i, (q i) ^ (e i)) :
    DirectSum.IsInternal (fun i => LinearMap.ker (aeval T ((q i) ^ (e i)))) := by
  refine isInternal_ker_aeval T (fun i => (q i) ^ (e i)) (fun i j hij => ?_) ?_
  · exact (hq hij).pow
  · rw [← hmin]; exact minpoly.aeval K T

end CayleyHamiltonOQ01OQ04
