import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-
# Categorical Schroeder-Bernstein Property (OQ-01)

## Open Question
"Can the Schroeder-Bernstein property be characterized categorically?
Banaschewski and Brummer (1986) showed it holds in categories with a
'retraction condition', but a complete characterization remains open."

## S2/S3 deliverables (this file)

1. Define `HasSBP (C : Type*) [Category C]` as the statement that mutual
   monomorphisms imply isomorphism.
2. Prove `hasSBP_Type : HasSBP (Type u)` by bridging through
   `CategoryTheory.mono_iff_injective` and `Function.Embedding.antisymm`.
3. Prove `hasSBP_Discrete : HasSBP (Discrete α)` (S4 ACT, this PR) using
   the Mathlib instance that every morphism in a `Discrete` category
   is an iso — `asIso` of the supplied mono witnesses the required iso
   without consuming the mono hypothesis.

No sorries, no axioms.

## Future phases (not in this file)

- S4 Banaschewski-Brummer: state and prove a sufficient categorical
  condition implying `HasSBP C` (the 1986 retraction-condition theorem).
- S5+ classification: survey strict generalizations (Trnková 1975,
  Pradic-Brown 2019 — SBP in IZF + Infinity equivalent to LEM).
- Counter-examples in `Grp` (Bumby 1965) and `Ban` (Gowers 1996) remain
  at the literature-citation level; Lean-formal failure witnesses are
  out of scope for OQ-01 S2/S3.
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

end SchroederBernsteinOQ01
