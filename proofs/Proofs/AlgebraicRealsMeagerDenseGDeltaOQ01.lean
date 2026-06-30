import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Proofs.AlgebraicRealsMeagerDenseGDelta

/-!
# The Algebraic Reals are an Explicit Fσ — completing the Gδ/Fσ dichotomy

## Open Question (algebraic-reals-meager-dense-gdelta-oq-01)

The parent entry `algebraic-reals-meager-dense-gdelta` exhibits the **transcendental** reals as
a concrete dense `Gδ` and shows that the **algebraic** reals are *not* a `Gδ`. Its first open
question asks to

> "Dualize to the algebraic reals as an explicit Fσ (countable union of closed singletons) and
>  record the full Gδ/Fσ classification of the dichotomy."

Mathlib has the predicate `IsGδ` (a countable intersection of open sets) but **no** `Fσ`
counterpart, so we first introduce one, dual in the exact sense of De Morgan:

    IsFσ s  :↔  s is a countable union of closed sets
            ↔  sᶜ is a Gδ          (`isFσ_iff_isGδ_compl`).

With this in hand the dichotomy becomes a clean, complete classification of the two halves of
the real line:

| set                         | `Fσ` | `Gδ` | category   |
|-----------------------------|------|------|------------|
| algebraic reals             | ✓    | ✗    | meagre     |
| transcendental reals        | ✗    | ✓    | comeagre   |

The algebraic reals are the **explicit** countable union of closed singletons
`⋃_{a algebraic} {a}` — each `{a}` closed because `ℝ` is `T1`, the index set countable
(`AlgebraicNumbersCountable.algebraic_reals_countable`). Being meagre and dense they are not a
`Gδ` (parent); dually, the transcendentals are a `Gδ` but, since their complement (the algebraic
reals) is not a `Gδ`, they are *not* an `Fσ`. This is the mirror image of the parent and the
classical companion to "`ℚ` is `Fσ` but not `Gδ`".

## Main results

* `IsFσ` : a set is `Fσ` if it is a countable union of closed sets (dual to `IsGδ`).
* `isFσ_iff_isGδ_compl` : `s` is `Fσ` iff `sᶜ` is `Gδ` — the De Morgan duality.
* `isFσ_of_countable` : in a `T1` space, every countable set is `Fσ` (dual to the parent's
  `isGδ_compl_of_countable`).
* `algebraicReals_eq_iUnion_singletons` : the algebraic reals *are* the union of their singletons.
* `algebraicReals_isFσ` : **the headline** — the algebraic reals are an explicit `Fσ`.
* `transcendentalReals_not_isFσ` : the transcendentals are *not* an `Fσ`.
* `algebraic_gδ_fσ_dichotomy` : the packaged four-way classification of the dichotomy.
-/

open Set Topology

namespace AlgebraicRealsMeagerDenseGDeltaOQ01

/-! ### The `Fσ` predicate and its duality with `Gδ` -/

/-- **A set is `Fσ` if it is a countable union of closed sets.**

This is the exact dual of Mathlib's `IsGδ` (a countable intersection of open sets); the two are
interchanged by complementation, recorded in `isFσ_iff_isGδ_compl`. -/
def IsFσ {X : Type*} [TopologicalSpace X] (s : Set X) : Prop :=
  ∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T

/-- **`Fσ ⇒ Gδ` of the complement.** Complementing a countable union of closed sets gives a
countable intersection of open sets (`Set.compl_sUnion`). -/
theorem IsFσ.isGδ_compl {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsFσ s) :
    IsGδ sᶜ := by
  obtain ⟨T, hTc, hTcount, rfl⟩ := hs
  refine ⟨compl '' T, ?_, hTcount.image _, ?_⟩
  · rintro t ⟨u, hu, rfl⟩
    exact isOpen_compl_iff.mpr (hTc u hu)
  · rw [Set.compl_sUnion]

/-- **`Gδ` of the complement ⇒ `Fσ`.** The reverse De Morgan passage: complementing a countable
intersection of open sets gives a countable union of closed sets (`Set.compl_sInter`). -/
theorem isFσ_of_isGδ_compl {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsGδ sᶜ) :
    IsFσ s := by
  obtain ⟨T, hTo, hTcount, hT⟩ := hs
  refine ⟨compl '' T, ?_, hTcount.image _, ?_⟩
  · rintro t ⟨u, hu, rfl⟩
    exact (hTo u hu).isClosed_compl
  · rw [← compl_compl s, hT, Set.compl_sInter]

/-- **`Fσ`/`Gδ` duality.** `s` is `Fσ` exactly when `sᶜ` is `Gδ`. -/
theorem isFσ_iff_isGδ_compl {X : Type*} [TopologicalSpace X] {s : Set X} :
    IsFσ s ↔ IsGδ sᶜ :=
  ⟨IsFσ.isGδ_compl, isFσ_of_isGδ_compl⟩

/-- **In a `T1` space every countable set is `Fσ`** — explicitly, the union of its singletons.

This is the dual of the parent's `isGδ_compl_of_countable`: there a countable set has `Gδ`
*complement*; here the countable set is *itself* the countable union of the closed singletons
`{a}` (closed because the space is `T1`). -/
theorem isFσ_of_countable {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Countable) : IsFσ s := by
  refine ⟨(fun a => {a}) '' s, ?_, hs.image _, ?_⟩
  · rintro t ⟨a, _, rfl⟩
    exact isClosed_singleton
  · rw [Set.sUnion_image, Set.biUnion_of_singleton]

/-! ### The algebraic reals as a concrete `Fσ` -/

/-- **The algebraic reals are the union of their singletons.** The explicit `Fσ` decomposition
requested by the open question, displayed before packaging it into `IsFσ`. -/
theorem algebraicReals_eq_iUnion_singletons :
    {x : ℝ | IsAlgebraic ℚ x} = ⋃ a ∈ {x : ℝ | IsAlgebraic ℚ x}, {a} :=
  (Set.biUnion_of_singleton _).symm

/-- **The algebraic reals are an explicit `Fσ` in `ℝ`.**

They are countable (`AlgebraicNumbersCountable.algebraic_reals_countable`), so by
`isFσ_of_countable` they are the countable union of the closed singletons `{a}`, `a` algebraic —
the dual structural statement to the parent's dense-`Gδ` transcendentals. -/
theorem algebraicReals_isFσ : IsFσ {x : ℝ | IsAlgebraic ℚ x} :=
  isFσ_of_countable AlgebraicNumbersCountable.algebraic_reals_countable

/-- **The transcendental reals are *not* an `Fσ`.**

If they were `Fσ`, their complement — the algebraic reals — would be a `Gδ`
(`IsFσ.isGδ_compl`), contradicting the parent's `algebraicReals_not_isGδ`. So the transcendentals
sit on the `Gδ`-only side of the dichotomy, exactly opposite the algebraic reals. -/
theorem transcendentalReals_not_isFσ : ¬ IsFσ {x : ℝ | ¬ IsAlgebraic ℚ x} := by
  intro h
  apply AlgebraicRealsMeagerDenseGDelta.algebraicReals_not_isGδ
  have hc : {x : ℝ | ¬ IsAlgebraic ℚ x}ᶜ = {x : ℝ | IsAlgebraic ℚ x} := by
    ext x; simp only [mem_compl_iff, mem_setOf_eq, not_not]
  rw [← hc]
  exact h.isGδ_compl

/-! ### The full Gδ/Fσ classification -/

/-- **The complete dichotomy.** Packaging the four facts that classify each half of the line:

* the **algebraic** reals are an `Fσ` but not a `Gδ`;
* the **transcendental** reals are a `Gδ` but not an `Fσ`.

The two sets are perfect complements in every sense — Baire category (meagre vs. comeagre,
parent) and Borel complexity (`Fσ`-but-not-`Gδ` vs. `Gδ`-but-not-`Fσ`, here). -/
theorem algebraic_gδ_fσ_dichotomy :
    (IsFσ {x : ℝ | IsAlgebraic ℚ x} ∧ ¬ IsGδ {x : ℝ | IsAlgebraic ℚ x}) ∧
      (IsGδ {x : ℝ | ¬ IsAlgebraic ℚ x} ∧ ¬ IsFσ {x : ℝ | ¬ IsAlgebraic ℚ x}) :=
  ⟨⟨algebraicReals_isFσ, AlgebraicRealsMeagerDenseGDelta.algebraicReals_not_isGδ⟩,
    ⟨AlgebraicRealsMeagerDenseGDelta.transcendentalReals_isGδ, transcendentalReals_not_isFσ⟩⟩

end AlgebraicRealsMeagerDenseGDeltaOQ01

#print axioms AlgebraicRealsMeagerDenseGDeltaOQ01.isFσ_iff_isGδ_compl
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ01.isFσ_of_countable
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ01.algebraicReals_isFσ
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ01.transcendentalReals_not_isFσ
#print axioms AlgebraicRealsMeagerDenseGDeltaOQ01.algebraic_gδ_fσ_dichotomy
