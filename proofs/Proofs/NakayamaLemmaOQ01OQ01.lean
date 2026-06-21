import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic
import Proofs.NakayamaLemmaOQ01

/-
# Minimal number of generators equals `dim` of the residue space `M / 𝔪M`

## What This Proves

Over a local ring `(R, 𝔪)` with residue field `k = R / 𝔪`, a finitely generated
module `M` has a *minimal* number of generators, and that number is computed by a
single linear-algebra invariant: the `k`-dimension of the residue vector space
`M / 𝔪M`.

* **Residue space as a `k`-vector space.** `ResidueModule R M := M ⧸ 𝔪 • ⊤` is an
  `R`-module annihilated by `𝔪`, hence a module over `k = R / 𝔪 = ResidueField R`.
  Mathlib already supplies the `Module (R ⧸ I) (M ⧸ I • ⊤)` instance
  (`Module.instModuleQuotientIdealSMulTop`) and `M / 𝔪M` is a finite-dimensional
  `k`-vector space when `M` is `R`-finite.

* **The bridge lemma** (`span_residueModule_eq_top_iff`). A set `t ⊆ M` has its
  image spanning `M / 𝔪M` over `k` iff `span R t ⊔ 𝔪 • ⊤ = ⊤`, i.e. iff `t`
  generates `M` *modulo* `𝔪M`. This is the precise translation between the
  `k`-vector-space picture and the `R`-module picture, proved by combining
  `Submodule.map_mkQ_eq_top` (surjective quotient maps) with
  `Submodule.restrictScalars_span` (spans over `R` and over the residue field `k`
  coincide, since `R → k` is surjective).

* **Lower bound** (`finrank_le_card_of_span_eq_top`). *Every* generating set of `M`
  has at least `dim_k (M/𝔪M)` elements. Its image spans the residue space, and a
  spanning set of a finite-dimensional vector space has at least `dim`-many
  elements (`finrank_le_of_span_eq_top`).

* **Existence / upper bound** (`exists_spanning_finset_card_eq_finrank`). There is a
  generating set of `M` of size *exactly* `dim_k (M/𝔪M)`: lift a `k`-basis of
  `M/𝔪M` to `M`, and the parent file's `nakayama_span_of_span_quotient` promotes
  "spans mod `𝔪M`" to "spans `M`". The lift has at most `dim`-many elements, and
  the lower bound forces equality.

* **The headline** (`numGenerators_eq_finrank`). Packaging the minimal generator
  count as `numGenerators R M := sInf { n | ∃ s : Finset M, s.card = n ∧ span R s = ⊤ }`,
  the two bounds give
  `numGenerators R M = finrank (ResidueField R) (M ⧸ 𝔪M)`.

## Relation to Mathlib and the parent

Mathlib has Nakayama, the residue field, the `k`-vector-space structure on
`M / 𝔪M`, and the cotangent-space specialisation `𝔪/𝔪²` (`Ideal.Cotangent`), but
states the minimal-generator-count equation `μ(M) = dim_k M/𝔪M` for *no* module —
only the principal-ideal corollary `finrank … ≤ 1 ↔ IsPrincipal` for the cotangent
space. The parent file `NakayamaLemmaOQ01` contributes
`nakayama_span_of_span_quotient` (lifting a residue-space spanning set to a
generating set); this file builds the two-sided count on top of it.

This file is `0`-axiom (only `propext` / `Classical.choice` / `Quot.sound`; no
`native_decide`, no `axiom`, no `sorry`).
-/

namespace NakayamaGenerators

open Submodule IsLocalRing Module

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The residue vector space `M / 𝔪M`. As `M / 𝔪M` is annihilated by `𝔪`, it is a
module over the residue field `k = R / 𝔪`. -/
abbrev ResidueModule (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] : Type _ :=
  M ⧸ (maximalIdeal R • (⊤ : Submodule R M))

/-- The residue space `M / 𝔪M` is a vector space over the residue field. -/
instance : Module (ResidueField R) (ResidueModule R M) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) _

instance : IsScalarTower R (ResidueField R) (ResidueModule R M) :=
  inferInstanceAs <| IsScalarTower R (R ⧸ maximalIdeal R) _

instance [Module.Finite R M] : FiniteDimensional (ResidueField R) (ResidueModule R M) :=
  Module.Finite.of_restrictScalars_finite R _ _

/-- The quotient map `M → M / 𝔪M`. -/
abbrev residueMap (R M : Type*) [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] : M →ₗ[R] ResidueModule R M :=
  (maximalIdeal R • (⊤ : Submodule R M)).mkQ

/-- **Bridge lemma.** A family `t ⊆ M` has its image spanning the residue space
`M / 𝔪M` over the residue field iff `t` generates `M` modulo `𝔪M`, i.e.
`span R t ⊔ 𝔪 • ⊤ = ⊤`. Spans over `R` and over `k = R/𝔪` coincide because
`R → k` is surjective. -/
theorem span_residueModule_eq_top_iff {t : Set M} :
    Submodule.span (ResidueField R) (residueMap R M '' t) = ⊤ ↔
      Submodule.span R t ⊔ maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
  rw [← (Submodule.restrictScalars_injective R ..).eq_iff,
    Submodule.restrictScalars_span, Submodule.restrictScalars_top,
    ← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]
  exact Ideal.Quotient.mk_surjective

/-- **Lower bound, family form.** Any finite spanning family of `M` has at least
`dim_k (M / 𝔪M)` elements. -/
theorem finrank_le_of_span_eq_top' {ι : Type*} [Fintype ι] {g : ι → M}
    (hg : Submodule.span R (Set.range g) = ⊤) :
    finrank (ResidueField R) (ResidueModule R M) ≤ Fintype.card ι := by
  refine _root_.finrank_le_of_span_eq_top (v := fun i => residueMap R M (g i)) ?_
  have hcomp : (fun i => residueMap R M (g i)) = residueMap R M ∘ g := rfl
  rw [hcomp, Set.range_comp, span_residueModule_eq_top_iff, hg, top_sup_eq]

/-- **Lower bound.** Every generating finset of `M` has at least `dim_k (M / 𝔪M)`
elements. -/
theorem finrank_le_card_of_span_eq_top {s : Finset M}
    (hs : Submodule.span R (s : Set M) = ⊤) :
    finrank (ResidueField R) (ResidueModule R M) ≤ s.card := by
  have hrange : Set.range (Subtype.val : ↥s → M) = (s : Set M) := by
    ext x; simp
  have hspan : Submodule.span R (Set.range (Subtype.val : ↥s → M)) = ⊤ := by
    rw [hrange]; exact hs
  have h := finrank_le_of_span_eq_top' hspan
  simpa [Fintype.card_coe] using h

/-- **Existence / upper bound.** There is a generating set of `M` of size exactly
`dim_k (M / 𝔪M)`: lift a `k`-basis of `M / 𝔪M` and apply Nakayama. -/
theorem exists_spanning_finset_card_eq_finrank [Module.Finite R M] :
    ∃ t : Finset M, Submodule.span R (t : Set M) = ⊤ ∧
      t.card = finrank (ResidueField R) (ResidueModule R M) := by
  classical
  set d := finrank (ResidueField R) (ResidueModule R M) with hd
  -- a `k`-basis of the residue space, indexed by `Fin d`
  let b := Module.finBasis (ResidueField R) (ResidueModule R M)
  -- lift each basis vector to `M`
  choose g hg using fun i =>
    (Submodule.mkQ_surjective (maximalIdeal R • (⊤ : Submodule R M))) (b i)
  -- the lifts span the residue space over `k` (they map onto the basis)
  have hkspan : Submodule.span (ResidueField R) (residueMap R M '' Set.range g) = ⊤ := by
    have hb : residueMap R M '' Set.range g = Set.range ⇑b := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext hg)
    rw [hb]; exact b.span_eq
  -- hence they span `M` modulo `𝔪M`, and Nakayama lifts this to spanning `M`
  have hsup : Submodule.span R (Set.range g) ⊔ maximalIdeal R • (⊤ : Submodule R M) = ⊤ :=
    span_residueModule_eq_top_iff.mp hkspan
  have hrange : Submodule.span R (Set.range g) = ⊤ :=
    NakayamaLemma.nakayama_span_of_span_quotient hsup.ge
  -- package the lifts as a finset
  refine ⟨Finset.image g Finset.univ, ?_, ?_⟩
  · rwa [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  · have hts : ((Finset.image g Finset.univ : Finset M) : Set M) = Set.range g := by
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hle : (Finset.image g Finset.univ).card ≤ d := by
      calc (Finset.image g Finset.univ).card
          ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_image_le
        _ = d := by simp
    have hge : d ≤ (Finset.image g Finset.univ).card :=
      finrank_le_card_of_span_eq_top (s := Finset.image g Finset.univ) (by rw [hts]; exact hrange)
    omega

/-- The minimal number of generators of an `R`-module `M`: the least size of a
finite generating set. -/
noncomputable def numGenerators (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : ℕ :=
  sInf { n | ∃ s : Finset M, s.card = n ∧ Submodule.span R (s : Set M) = ⊤ }

/-- **Minimal number of generators = `dim` of the residue space.** Over a local
ring `(R, 𝔪)` with residue field `k`, a finitely generated module `M` satisfies
`μ(M) = dim_k (M / 𝔪M)`. -/
theorem numGenerators_eq_finrank [Module.Finite R M] :
    numGenerators R M = finrank (ResidueField R) (ResidueModule R M) := by
  obtain ⟨t, htspan, htcard⟩ := exists_spanning_finset_card_eq_finrank (R := R) (M := M)
  have hne : { n | ∃ s : Finset M, s.card = n ∧ Submodule.span R (s : Set M) = ⊤ }.Nonempty :=
    ⟨t.card, t, rfl, htspan⟩
  refine le_antisymm ?_ ?_
  · -- `d` is attained, so `μ ≤ d`
    rw [← htcard]
    exact Nat.sInf_le ⟨t, rfl, htspan⟩
  · -- the minimiser is a generating set, so it has `≥ d` elements
    obtain ⟨s, hscard, hsspan⟩ := Nat.sInf_mem hne
    have := finrank_le_card_of_span_eq_top hsspan
    rw [numGenerators, ← hscard]
    exact this

end NakayamaGenerators
