import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-
# Categorical Schroeder-Bernstein Property (OQ-01)

## Open Question
"Can the Schroeder-Bernstein property be characterized categorically?
Banaschewski and Brummer (1986) showed it holds in categories with a
'retraction condition', but a complete characterization remains open."

## S2/S3 deliverables

1. Define `HasSBP (C : Type*) [Category C]` as the statement that mutual
   monomorphisms imply isomorphism.
2. Prove `hasSBP_Type : HasSBP (Type u)` by bridging through
   `CategoryTheory.mono_iff_injective` and `Function.Embedding.antisymm`.
3. Prove `hasSBP_Discrete : HasSBP (Discrete α)` (S4 ACT) using
   the Mathlib instance that every morphism in a `Discrete` category
   is an iso — `asIso` of the supplied mono witnesses the required iso
   without consuming the mono hypothesis.

## S5 ACT (this PR)

4. Prove `not_hasSBP_TopCat : ¬ HasSBP TopCat.{0}` via the classical
   `[0, 1]` vs `(0, 1)` counterexample: mutual continuous injections
   exist (compression `[0, 1] → [1/4, 1/2] ⊂ (0, 1)` via `(x + 1) / 4`;
   inclusion `(0, 1) ↪ [0, 1]`) but `[0, 1]` is compact while `(0, 1)`
   is not, blocking any homeomorphism via `Homeomorph.compactSpace` and
   the `isCompact_Ioo_iff` non-compactness witness.

No sorries, no axioms.

## Future phases (not in this file)

- Banaschewski-Brummer (S6+): state and prove a sufficient categorical
  condition implying `HasSBP C` (the 1986 retraction-condition theorem).
- S7+ classification: survey strict generalizations (Trnková 1975,
  Pradic-Brown 2019 — SBP in IZF + Infinity equivalent to LEM).
- Counter-examples in `Grp` (Bumby 1965) and `Ban` (Gowers 1996) remain
  at the literature-citation level; Lean-formal failure witnesses beyond
  `TopCat` are out of scope for OQ-01 S5.
-/

namespace SchroederBernsteinOQ01

open CategoryTheory

universe u

/-- A category `C` has the **Schroeder-Bernstein property** iff for every
pair of objects with mutual monomorphisms there is an isomorphism between
them. -/
def HasSBP (C : Type*) [Category C] : Prop :=
  ∀ X Y : C, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)

/-- `Type u` has the Schroeder-Bernstein property: any two types with
mutual monomorphisms (i.e. mutual injections) are categorically isomorphic
(i.e. bijective). Bridges the classical Schroeder-Bernstein theorem
(`Function.Embedding.antisymm`) to the categorical statement. -/
theorem hasSBP_Type : HasSBP (Type u) := by
  intro X Y ⟨m, hm⟩ ⟨n, hn⟩
  -- In `Type u`, monomorphisms are exactly the injections.
  have hmi : Function.Injective m := (mono_iff_injective m).mp hm
  have hni : Function.Injective n := (mono_iff_injective n).mp hn
  -- Apply the classical Schroeder-Bernstein theorem on embeddings.
  obtain ⟨e⟩ := Function.Embedding.antisymm ⟨m, hmi⟩ ⟨n, hni⟩
  -- Lift the equivalence to a categorical isomorphism.
  exact ⟨e.toIso⟩

/-- `Discrete α` has the Schroeder-Bernstein property vacuously: every
morphism in a discrete category is an isomorphism
(`Mathlib/CategoryTheory/Discrete/Basic.lean` instance
`{f : i ⟶ j} : IsIso f`), so the first supplied mono is itself an iso
witness; the second mono hypothesis is not consumed.

This is a second concrete `HasSBP` instance alongside `hasSBP_Type`, and
demonstrates that the predicate is satisfied by categories where the
property is vacuous (every Hom-set has at most one element, and every
non-empty Hom-set is an iso). -/
theorem hasSBP_Discrete {α : Type u} : HasSBP (Discrete α) := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩

/-! ## S5 ACT — `¬ HasSBP TopCat` via the `[0,1]` vs `(0,1)` counterexample

The classical Banach-space failure of SBP has a topological analogue: the
closed interval `[0,1]` and the open interval `(0,1)` admit mutual
continuous injections (`f : [0,1] → (0,1)` by `x ↦ (x+1)/4`; `g : (0,1) → [0,1]`
by inclusion), yet they are not homeomorphic — `[0,1]` is compact while
`(0,1)` is not. This refutes `HasSBP TopCat`.

The compression `f` is well-defined: for `x ∈ [0,1]`, we have
`(x+1)/4 ∈ [1/4, 1/2] ⊂ (0,1)`. -/

private noncomputable def fHom :
    (TopCat.of ↥(Set.Icc (0 : ℝ) 1)) ⟶ (TopCat.of ↥(Set.Ioo (0 : ℝ) 1)) :=
  TopCat.ofHom
    { toFun := fun ⟨x, hx⟩ => ⟨(x + 1) / 4, by
        rcases hx with ⟨h0, h1⟩
        refine ⟨?_, ?_⟩
        · linarith
        · linarith⟩,
      continuous_toFun := by fun_prop }

private noncomputable def gHom :
    (TopCat.of ↥(Set.Ioo (0 : ℝ) 1)) ⟶ (TopCat.of ↥(Set.Icc (0 : ℝ) 1)) :=
  TopCat.ofHom
    { toFun := fun ⟨y, hy⟩ => ⟨y, Set.Ioo_subset_Icc_self hy⟩,
      continuous_toFun := by fun_prop }

private theorem fHom_injective :
    Function.Injective (TopCat.Hom.hom fHom) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  simp [fHom] at hab
  linarith

private theorem gHom_injective :
    Function.Injective (TopCat.Hom.hom gHom) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  simp [gHom] at hab
  exact hab

/-- **`TopCat` does not have the Schroeder-Bernstein property.**

The closed interval `[0,1]` and the open interval `(0,1)`, viewed as
objects of `TopCat.{0}`, admit mutual monomorphisms (`fHom` and `gHom`
above are continuous injections) but are not homeomorphic: `[0,1]` is
compact (Heine-Borel, `CompactIccSpace`), so any homeomorphism would
transfer compactness to `(0,1)` via `Homeomorph.compactSpace`, and then
`isCompact_Ioo_iff` would force `1 ≤ 0`. -/
theorem not_hasSBP_TopCat : ¬ HasSBP TopCat.{0} := by
  intro h
  have hf_mono : Mono fHom := (TopCat.mono_iff_injective fHom).mpr fHom_injective
  have hg_mono : Mono gHom := (TopCat.mono_iff_injective gHom).mpr gHom_injective
  obtain ⟨iso⟩ :=
    h (TopCat.of ↥(Set.Icc (0 : ℝ) 1)) (TopCat.of ↥(Set.Ioo (0 : ℝ) 1))
      ⟨fHom, hf_mono⟩ ⟨gHom, hg_mono⟩
  -- `[0,1]` is compact via the `CompactIccSpace` typeclass on ℝ; transport
  -- through the `TopCat.coe_of := rfl` reduction.
  haveI : CompactSpace ↥(Set.Icc (0 : ℝ) 1) := inferInstance
  -- Homeomorphisms transfer compactness; the codomain `(0,1)` inherits it.
  have hY_compact : CompactSpace ↥(Set.Ioo (0 : ℝ) 1) :=
    (TopCat.homeoOfIso iso).compactSpace
  -- Push down to a `Set ℝ` statement.
  have hIoo_compact : IsCompact (Set.Ioo (0 : ℝ) 1) :=
    isCompact_iff_isCompact_univ.mpr hY_compact.isCompact_univ
  -- `isCompact_Ioo_iff` forces `1 ≤ 0`; contradiction.
  rw [isCompact_Ioo_iff] at hIoo_compact
  linarith

end SchroederBernsteinOQ01
