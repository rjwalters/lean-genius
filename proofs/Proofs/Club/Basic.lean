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

/-- **Diagonal Intersection is Closed** (0 sorries).

    Proof: Given γ < o an acc point of Δ(f β),
    for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
    Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
    Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
    (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
  rw [isClosedBelow_iff]
  intro γ γlto γAcc
  simp only [mem_diagInter]
  refine ⟨γlto, fun β βltγ => ?_⟩
  apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
  rw [isAcc_iff]
  refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
  obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
  simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
  obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
  have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
  exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩

/-! ### IsRegressive companion lemmas

Library-style helpers for `IsRegressive` that the Fodor pressing-down proof
(currently in `Proofs/FodorPressingDown.lean`) uses inline. Lifting these to
the library prepares the post-S4-ACT re-statement of `fodor` in terms of
`Ordinal.IsRegressive` (sister-slug `fodor-pressing-down-oq-04` will consume
them directly once it imports `Proofs.Club.Basic`). -/

/-- Every function is vacuously regressive on the empty set. -/
theorem IsRegressive.empty {f : Ordinal → Ordinal} :
    IsRegressive f (∅ : Set Ordinal) :=
  fun _ h _ => absurd h (Set.notMem_empty _)

/-- Regressivity is anti-monotone under set inclusion: if `f` is regressive
on `T` and `S ⊆ T`, then `f` is regressive on `S`. -/
theorem IsRegressive.mono {f : Ordinal → Ordinal} {S T : Set Ordinal}
    (hST : S ⊆ T) (hT : IsRegressive f T) : IsRegressive f S :=
  fun _ hα hα0 => hT (hST hα) hα0

/-- Restricting to a preimage fiber preserves regressivity. Used in Fodor's
contradiction step: if `f` is regressive on `S`, it is regressive on every
constancy class `S ∩ f ⁻¹' {c}`. -/
theorem IsRegressive.inter_preimage {f : Ordinal → Ordinal} {S : Set Ordinal}
    {c : Ordinal} (hS : IsRegressive f S) :
    IsRegressive f (S ∩ f ⁻¹' {c}) :=
  hS.mono Set.inter_subset_left

/-- Bridge to the bare `∀ α ∈ S, f α < α` hypothesis form used by the
existing Fodor statement: under the standing assumption that `S` contains
no zero, `IsRegressive f S` is equivalent to `∀ α ∈ S, f α < α`. -/
theorem IsRegressive.iff_forall_lt {f : Ordinal → Ordinal} {S : Set Ordinal}
    (hS_pos : ∀ α ∈ S, 0 < α) :
    IsRegressive f S ↔ ∀ α ∈ S, f α < α :=
  ⟨fun h α hα => h hα (hS_pos α hα).ne', fun h _ hα _ => h _ hα⟩

end Ordinal
