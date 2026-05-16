import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Groupoid
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

## S6 ACT (this PR)

5. Prove `hasSBP_of_isDiscrete : [IsDiscrete C] → HasSBP C` — the
   vacuous sufficient condition. In any `[IsDiscrete C]` category (at
   most one morphism between objects, with morphisms forcing object
   equality), every morphism is iso (`isIso_of_isDiscrete`), so the
   first mono of a mutual-monomorphism pair is itself an iso witness.
   This abstracts the proof pattern of `hasSBP_Discrete` to all
   `IsDiscrete` categories; `Discrete α` is one such instance.

## S11 ACT (this PR)

6. Prove `hasSBP_of_isGroupoid : [IsGroupoid C] → HasSBP C` — a
   second vacuous sufficient condition broadening the `IsDiscrete`
   regime to all groupoids. Mathlib's `IsGroupoid.all_isIso`
   (`Mathlib.CategoryTheory.Groupoid` line 119, registered as an
   instance at line 121) makes every morphism iso, so the first mono
   of a mutual-monomorphism pair is itself an iso witness — the
   second mono is again unused. The hypothesis broadens
   `hasSBP_of_isDiscrete`'s instance space from at-most-one-Hom-per-pair
   to all groupoids (fundamental groupoids of spaces, Brandt
   groupoids, `EssGroupoid`, etc.) while preserving the
   `not_hasSBP_TopCat` sanity check (`TopCat` is not a groupoid:
   inclusion `(0,1) ↪ [0,1]` lacks a continuous inverse).

## Future phases (not in this file)

- Banaschewski-Brummer S11+ (non-vacuous): identify a sufficient
  hypothesis that does NOT force `Mono = Iso`. Candidates:
  regular-mono variants (RegularMono / StrongMono), the fully-faithful
  concrete path D.i per S10 PREP §3.2, retraction-conditions per
  Banaschewski-Brummer 1986. The S5 TopCat counterexample is a
  useful sanity check: any chosen hypothesis `P` must exclude
  `TopCat` (since `P TopCat -> HasSBP TopCat` would contradict
  `not_hasSBP_TopCat`).
- S8+ classification: survey strict generalizations (Trnková 1975,
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

/-! ## S6 ACT — `[IsDiscrete C] → HasSBP C` (vacuous sufficient condition)

The vacuous half of the Banaschewski-Brümmer style sufficient condition
for the categorical Schroeder-Bernstein property: any `[IsDiscrete C]`
category satisfies SBP because every morphism in such a category is
already an isomorphism (Mathlib's `isIso_of_isDiscrete`), so the first
mono of a mutual-monomorphism pair witnesses the required iso without
the second mono being consumed.

`IsDiscrete C` is the Mathlib typeclass (`Mathlib.CategoryTheory.Discrete.Basic`)
asserting that `C` has at most one morphism between any two objects AND
that any morphism `f : X ⟶ Y` forces `X = Y`. `Discrete α` is the
canonical instance (`Discrete.isDiscrete`); the existing `hasSBP_Discrete`
above is the specialization at `C = Discrete α`.

This abstracts `hasSBP_Discrete`'s proof pattern: the substantive work
happens in Mathlib's `isIso_of_isDiscrete` instance, and the categorical
SBP statement reduces to `asIso m` once `IsIso m` is in scope.

The hypothesis `IsDiscrete C` is restrictive (it forces `Mono = Iso`),
so this is the **vacuous case** of the Banaschewski-Brümmer sufficient
condition. A non-vacuous hypothesis (regular-mono variants, retraction
conditions) is deferred to S7+.
-/

/-- **S6 ACT — vacuous sufficient condition for SBP**: any `[IsDiscrete C]`
category has the Schroeder-Bernstein property. Generalizes `hasSBP_Discrete`
beyond `C = Discrete α`. -/
theorem hasSBP_of_isDiscrete (C : Type*) [Category C] [IsDiscrete C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩

/-! ## S11 ACT — `[IsGroupoid C] → HasSBP C` (vacuous-but-broadening)

The second vacuous sufficient condition for the categorical
Schroeder-Bernstein property: any `[IsGroupoid C]` category satisfies
SBP because Mathlib's `IsGroupoid.all_isIso` instance (`Mathlib.
CategoryTheory.Groupoid` line 119, registered as a global instance at
line 121) makes every morphism an isomorphism. The first supplied mono
therefore witnesses the required iso directly; the second mono is again
unused.

This broadens the `[IsDiscrete C] → HasSBP C` regime (S6 ACT) from
"at most one morphism per object pair" to all groupoids — i.e. all
categories where every morphism is invertible. Concrete additional
instance space: fundamental groupoids of topological spaces, Brandt
groupoids, the `EssGroupoid` of any category, action groupoids.

The proof is one line (`asIso m`), structurally identical to
`hasSBP_Discrete` / `hasSBP_of_isDiscrete`. What differs is the route
to `IsIso m`: in S4 / S6 it comes from `isIso_of_isDiscrete`; here it
comes from `IsGroupoid.all_isIso`.

**Sanity vs S5**: `TopCat` is not a groupoid — the continuous inclusion
`(0,1) ↪ [0,1]` has no continuous inverse — so this hypothesis does not
contradict `not_hasSBP_TopCat`.

**Vacuousness**: This is the **vacuous-but-broadening** half of the
Banaschewski-Brümmer sufficient-condition map (forces `Mono = Iso`
again). The first genuinely non-vacuous sufficient condition (path D.i
fully-faithful concrete, per S10 PREP §3.2) is deferred to S12+.
-/

/-- **S11 ACT — vacuous-but-broadening sufficient condition for SBP**:
any `[IsGroupoid C]` category has the Schroeder-Bernstein property.
Broadens `hasSBP_of_isDiscrete` from at-most-one-Hom categories to all
groupoids (every morphism iso). -/
theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩

end SchroederBernsteinOQ01
