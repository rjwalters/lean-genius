/-
  Club, Stationary, Diagonal Intersection — Basic API
  (`Proofs/Club/Basic.lean`, lifted from `Proofs/FodorPressingDown.lean`
  per `fodor-pressing-down-oq-01` S1 OBSERVE migration plan, PR #18280)

  This file lifts the local infrastructure for club / stationary / diagonal-
  intersection sets out of the single-purpose `FodorPressingDown.lean` and
  into a standalone module under `Ordinal` namespace, so it can be reused by
  sibling slugs (`fodor-pressing-down-oq-04` Solovay splitting, etc.).

  ## Naming and design lock (per S1 OBSERVE PR #18280, locked decisions)

  - **Namespace:** `Ordinal` (matches `Ordinal.IsAcc` already in Mathlib).
  - **Structure vs Prop:** `IsClubBelow` is a `structure` with three fields
    (subset_Iio, closed, unbounded); the others are `def`-bindings returning
    `Prop` or `Set Ordinal`.
  - **Universe polymorphism:** definitions stay polymorphic over the implicit
    `Ordinal` universe; combinatorial lemmas (`diagInter_isClubBelow`,
    `fodor`) remain in the parent file (where they are pinned at
    `Cardinal.{0}`) until a downstream request appears.
  - **File path:** `proofs/Proofs/Club/Basic.lean` (new directory
    `proofs/Proofs/Club/` introduced for future siblings
    `DiagonalIntersection.lean`, `Galvin.lean`).

  ## Status

  - 0 sorries, 0 axioms.
  - The parent `Proofs/FodorPressingDown.lean` still contains DUPLICATE
    definitions in `namespace FodorPressingDown`. S3 (move
    `diagInter_isClosedBelow`) and S4 (cut parent's duplicates) follow.
  - Strictly additive: this PR introduces the new module without touching
    the parent. Other consumers can `import Proofs.Club.Basic` immediately.
-/

import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Tactic

namespace Ordinal

open Set Order

/-- A set `S` is unbounded below ordinal `o`: above every `α < o` there is
some `β ∈ S` with `α < β < o`. -/
def IsUnboundedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ α < o, ∃ β ∈ S, α < β ∧ β < o

/-- A club (closed unbounded) set below ordinal `o`. We require `S ⊆ Iio o`
so that club members are definitionally below `o`. -/
structure IsClubBelow (S : Set Ordinal) (o : Ordinal) : Prop where
  subset_Iio : S ⊆ Iio o
  closed     : IsClosedBelow S o
  unbounded  : IsUnboundedBelow S o

/-- A set `S` is stationary below `o` if it meets every club below `o`. -/
def IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty

/-- Diagonal intersection of an ordinal-indexed family of sets, restricted to
ordinals below `o`: `Δ_{β<o}(f β) = {γ < o | ∀ β < γ, γ ∈ f β}`. -/
def diagInter (f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {γ | γ < o ∧ ∀ β, β < γ → γ ∈ f β}

/-- `f` is regressive on `S` if `f α < α` for every nonzero `α ∈ S`. -/
def IsRegressive (f : Ordinal → Ordinal) (S : Set Ordinal) : Prop :=
  ∀ ⦃α⦄, α ∈ S → α ≠ 0 → f α < α

/-- Every element of a club below `o` is itself below `o`. -/
theorem IsClubBelow.mem_lt {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α ∈ S) : α < o :=
  hS.subset_Iio hα

/-- A club below `o` contains every accumulation point below `o`. -/
theorem IsClubBelow.mem_of_isAcc {S : Set Ordinal} {o : Ordinal}
    (hS : IsClubBelow S o) {α : Ordinal} (hα : α < o) (hAcc : α.IsAcc S) :
    α ∈ S :=
  hS.closed.forall_lt α hα hAcc

@[simp]
theorem mem_diagInter {f : Ordinal → Set Ordinal} {o γ : Ordinal} :
    γ ∈ diagInter f o ↔ γ < o ∧ ∀ β < γ, γ ∈ f β := Iff.rfl

theorem diagInter_subset_Iio (f : Ordinal → Set Ordinal) (o : Ordinal) :
    diagInter f o ⊆ Iio o :=
  fun _ h => h.1

/-- `Iio o` is a club below `o` when `o` is a successor-limit ordinal. -/
theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
    IsClubBelow (Iio o) o where
  subset_Iio := fun _ h => h
  closed := by
    rw [isClosedBelow_iff]
    intro p pltq _hacc
    exact pltq
  unbounded := fun α hα => by
    have h1 : α + 1 < o := ho.succ_lt hα
    exact ⟨α + 1, h1, lt_add_one α, h1⟩

end Ordinal
