import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.FDRep
import Mathlib.Tactic

/-!
# Schur's Lemma (Representation Theory)

## What This Proves

**Schur's Lemma** is the cornerstone of representation theory. Its module-theoretic
content has three classical layers, all formalized here:

1. **Dichotomy.** Any module homomorphism between two simple modules is either an
   isomorphism or the zero map (`LinearMap.bijective_or_eq_zero`).
2. **Division ring.** Consequently the endomorphism ring of a simple module is a
   division ring (`Module.End.instDivisionRing`).
3. **Scalar form (algebraically closed case).** If the field `k` is algebraically
   closed and the simple module `M` is finite-dimensional over `k`, then *every*
   endomorphism of `M` is multiplication by a scalar `c ∈ k`.

The first two layers are restatements of existing Mathlib results. The third —
the famous "endomorphisms of an irreducible representation are scalars" — is, in
Mathlib, available only in the abstract `𝕜`-linear *category* setting
(`CategoryTheory.endomorphism_simple_eq_smul_id`) and for `FDRep`. The concrete
**module-language scalar form** proved here (`schur_endomorphism_scalar`) is the
form actually used in character theory and is assembled from Mathlib's eigenvalue
theory plus the dichotomy above.

## Mathematical Statement

Let `A` be a `k`-algebra and `M` a simple `A`-module that is finite-dimensional
over an algebraically closed field `k`. Then for every `A`-linear endomorphism
`f : M →ₗ[A] M` there is a scalar `c : k` with `f m = c • m` for all `m`.

## Approach (the eigenvalue argument)

* View `f` as a `k`-linear endomorphism `g := f.restrictScalars k`.
* Since `k` is algebraically closed and `M` is finite-dimensional and nonzero,
  `g` has an eigenvalue `c` with eigenvector `v ≠ 0` (`Module.End.exists_eigenvalue`).
* The map `h := f - c • id` is `A`-linear and kills `v`, so it is **not** injective.
* By Schur's dichotomy a non-injective endomorphism of a simple module is `0`,
  hence `f = c • id`, i.e. `f m = c • m` for all `m`. ∎

## References
* Schur, "Neue Begründung der Theorie der Gruppencharaktere" (1905)
* Serre, *Linear Representations of Finite Groups*, §2.2
-/

open Module

namespace SchursLemma

/-! ## Layer 1 & 2: the dichotomy and the division ring (over any ring)

These re-export Mathlib's general module-theoretic Schur lemma so the full
statement is visible in one place. -/

section General

variable {R M N : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Schur's Lemma (dichotomy).** A homomorphism between two simple modules is
either bijective or zero. -/
theorem hom_bijective_or_zero [IsSimpleModule R M] [IsSimpleModule R N]
    (f : M →ₗ[R] N) : Function.Bijective f ∨ f = 0 :=
  f.bijective_or_eq_zero

/-- A nonzero homomorphism between simple modules is a linear isomorphism. -/
noncomputable def homEquivOfNeZero [IsSimpleModule R M] [IsSimpleModule R N]
    {f : M →ₗ[R] N} (hf : f ≠ 0) : M ≃ₗ[R] N :=
  LinearEquiv.ofBijective f (f.bijective_of_ne_zero hf)

/-- **Schur's Lemma (orthogonality).** If two simple modules are *not* isomorphic,
then the only homomorphism between them is the zero map. -/
theorem hom_eq_zero_of_not_linearEquiv [IsSimpleModule R M] [IsSimpleModule R N]
    (h : IsEmpty (M ≃ₗ[R] N)) (f : M →ₗ[R] N) : f = 0 := by
  by_contra hf
  exact h.false (homEquivOfNeZero hf)

/-- **Schur's Lemma (division ring).** The endomorphism ring of a simple module is
a division ring: every nonzero endomorphism is invertible. -/
noncomputable def endDivisionRing [DecidableEq (Module.End R M)] [IsSimpleModule R M] :
    DivisionRing (Module.End R M) :=
  inferInstance

end General

/-! ## Layer 3: the scalar form over an algebraically closed field

This is the genuinely new content of this file: the concrete module statement
that endomorphisms of a finite-dimensional irreducible representation over an
algebraically closed field are scalars. -/

section Scalar

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {A : Type*} [Ring A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [IsSimpleModule A M] [FiniteDimensional k M]

/-- **Schur's Lemma (scalar form).** Over an algebraically closed field `k`, every
`A`-linear endomorphism of a finite-dimensional simple `A`-module `M` is
multiplication by a scalar: there is some `c : k` with `f m = c • m` for all `m`. -/
theorem schur_endomorphism_scalar (f : M →ₗ[A] M) : ∃ c : k, ∀ m, f m = c • m := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  -- View `f` as a `k`-linear endomorphism and extract an eigenvalue.
  set g : Module.End k M := f.restrictScalars k with hg
  obtain ⟨c, hc⟩ := g.exists_eigenvalue
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hgv : g v = c • v := hv.apply_eq_smul
  have hvne : v ≠ 0 := hv.2
  refine ⟨c, ?_⟩
  -- The `A`-linear map `h := f - c • id` annihilates the eigenvector `v`.
  set h : M →ₗ[A] M := f - c • LinearMap.id with hh
  have hhv : h v = 0 := by
    have : f v = c • v := hgv
    simp only [hh, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, this, sub_self]
  -- A non-injective endomorphism of a simple module must be zero (Schur).
  have hnotinj : ¬ Function.Injective h := by
    intro hinj
    exact hvne (hinj (by rw [hhv, map_zero]))
  have hzero : h = 0 := (h.bijective_or_eq_zero).resolve_left fun hb => hnotinj hb.injective
  -- Unwind `h = 0` pointwise to `f m = c • m`.
  intro m
  have := LinearMap.congr_fun hzero m
  simpa [hh, sub_eq_zero] using this

/-- A simple `A`-module over an algebraically closed field is **absolutely simple**:
the only endomorphisms commuting with the action are the scalars, so the
endomorphism algebra is exactly `k`. Concretely, every endomorphism agrees with
`c • id` for a unique `c`. -/
theorem schur_endomorphism_eq_smul_id (f : M →ₗ[A] M) :
    ∃ c : k, f = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := schur_endomorphism_scalar (k := k) f
  exact ⟨c, by ext m; simpa using hc m⟩

end Scalar

/-! ## Categorical / `FDRep` form

For completeness we re-export the abstract categorical Schur lemma and its
`FDRep` (finite-dimensional representation) specialization, which is how Mathlib
packages the dimension count of hom-spaces between irreducibles. -/

section Categorical

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Linear 𝕜 C] [HasKernels C]

/-- **Schur's Lemma (categorical, scalar form).** In a `𝕜`-linear category with
finite-dimensional hom-spaces over an algebraically closed field, every
endomorphism of a simple object is a scalar multiple of the identity. -/
theorem categorical_endomorphism_scalar
    {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] (f : X ⟶ X) :
    ∃ c : 𝕜, c • 𝟙 X = f :=
  endomorphism_simple_eq_smul_id 𝕜 f

end Categorical

section FDRepSchur

open CategoryTheory

universe u

variable {k G : Type u} [Field k] [Monoid G] [IsAlgClosed k]

open scoped Classical in
/-- **Schur's Lemma for `FDRep`.** Over an algebraically closed field, the
hom-space between two irreducible finite-dimensional representations is
`1`-dimensional when they are isomorphic and `0`-dimensional otherwise. -/
theorem fdRep_finrank_hom_simple_simple
    (V W : FDRep k G) [Simple V] [Simple W] :
    Module.finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  FDRep.finrank_hom_simple_simple V W

end FDRepSchur

end SchursLemma
