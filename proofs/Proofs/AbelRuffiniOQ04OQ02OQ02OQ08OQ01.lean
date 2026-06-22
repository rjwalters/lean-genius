/-
# Solvability of Sₐ and Aₐ is intrinsic to `Fintype.card α`
  (Abel–Ruffini OQ-04-OQ-02-OQ-02-OQ-08-OQ-01)

The parent bridge `AbelRuffiniOQ04OQ02OQ02OQ08` proved, for an arbitrary finite
type `α`, that `IsSolvable (alternatingGroup α) ↔ IsSolvable (Perm α)`, and
specialised the classical thresholds to `Fin n`.  Its first listed future
direction asks to transport solvability *invariance under cardinality*:

> `IsSolvable (alternatingGroup α) ↔ IsSolvable (alternatingGroup β)` whenever
> `Fintype.card α = Fintype.card β`, via a permutation `MulEquiv`.

This file delivers exactly that, and upgrades both classical classifications
from `Fin n` to an *arbitrary* finite type:

* `perm_solvable_iff_card`        : `IsSolvable (Perm α) ↔ Fintype.card α ≤ 4`
* `alternating_solvable_iff_card` : `IsSolvable (alternatingGroup α) ↔ Fintype.card α ≤ 4`

The engine is the conjugation isomorphism `Equiv.permCongrHom e : Perm α ≃* Perm β`
induced by any bijection `e : α ≃ β`.  Because `Equiv.Perm.sign` is invariant
under `permCongr` (`sign_permCongr`), this isomorphism carries `alternatingGroup α`
*onto* `alternatingGroup β` (`map_permCongrHom_alternating`), giving a canonical
`MulEquiv` of the two alternating groups (`alternatingCongr`).  Solvability is a
`MulEquiv` invariant (`isSolvable_congr`), so it depends on `α` only through
`Fintype.card α` — the answer to the parent's question.

Choosing `β = Fin (Fintype.card α)` and composing with the parent's `Fin n`
classifications turns "Sₙ / Aₙ solvable ⇔ n ≤ 4" into a statement about any
finite type whatsoever; equinumerous types have isomorphic alternating groups
and identical solvability.

167-line companion; no `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01

open AbelRuffiniOQ04OQ02OQ02 AbelRuffiniOQ04OQ02OQ02OQ08

/-! ## §1  Solvability is a `MulEquiv` invariant

`solvable_of_surjective` transports solvability along a surjective group
homomorphism.  A `MulEquiv` is surjective both ways, so it gives an `↔`. -/

section MulEquivTransport

variable {G G' : Type*} [Group G] [Group G']

/-- A group isomorphic to a solvable group is solvable. -/
theorem isSolvable_of_mulEquiv (e : G ≃* G') [IsSolvable G] : IsSolvable G' :=
  solvable_of_surjective (f := (e : G →* G')) (EquivLike.surjective e)

/-- Solvability is invariant under group isomorphism. -/
theorem isSolvable_congr (e : G ≃* G') : IsSolvable G ↔ IsSolvable G' :=
  ⟨fun h => by haveI := h; exact isSolvable_of_mulEquiv e,
   fun h => by haveI := h; exact isSolvable_of_mulEquiv e.symm⟩

end MulEquivTransport

/-! ## §2  Transport across a bijection of the underlying type

A bijection `e : α ≃ β` conjugates permutations, `Equiv.permCongrHom e`, and
this is a `MulEquiv Perm α ≃* Perm β`.  Solvability of the full symmetric group
therefore depends on `α` only through its cardinality. -/

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

/-- The symmetric groups of two equipotent types are equisolvable. -/
theorem perm_solvable_congr (e : α ≃ β) :
    IsSolvable (Perm α) ↔ IsSolvable (Perm β) :=
  isSolvable_congr e.permCongrHom

/-! ## §3  The conjugation isomorphism preserves the alternating subgroup

`Equiv.Perm.sign_permCongr` says `permCongr` preserves the sign, and the
alternating group is exactly the sign-kernel (`mem_alternatingGroup`).  Hence
`permCongrHom e` maps `alternatingGroup α` bijectively onto `alternatingGroup β`. -/

/-- `permCongrHom e` carries the alternating group onto the alternating group. -/
theorem map_permCongrHom_alternating (e : α ≃ β) :
    (alternatingGroup α).map (e.permCongrHom : Perm α →* Perm β) = alternatingGroup β := by
  ext g
  simp only [Subgroup.mem_map, Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨p, hp, rfl⟩
    show Perm.sign (e.permCongr p) = 1
    rw [Equiv.Perm.sign_permCongr]
    exact hp
  · intro hg
    refine ⟨e.symm.permCongr g, ?_, ?_⟩
    · rw [Equiv.Perm.sign_permCongr]; exact hg
    · show e.permCongr (e.symm.permCongr g) = g
      rw [← Equiv.permCongr_symm]
      exact e.permCongr.apply_symm_apply g

/-- The canonical isomorphism `alternatingGroup α ≃* alternatingGroup β` induced
by a bijection `e : α ≃ β`. -/
noncomputable def alternatingCongr (e : α ≃ β) :
    alternatingGroup α ≃* alternatingGroup β :=
  (MulEquiv.subgroupMap e.permCongrHom (alternatingGroup α)).trans
    (MulEquiv.subgroupCongr (map_permCongrHom_alternating e))

/-- The alternating groups of two equipotent types are equisolvable. -/
theorem alternating_solvable_congr (e : α ≃ β) :
    IsSolvable (alternatingGroup α) ↔ IsSolvable (alternatingGroup β) :=
  isSolvable_congr (alternatingCongr e)

/-! ## §4  The classical classifications for an arbitrary finite type

Specialising the transport to `β = Fin (Fintype.card α)` and composing with the
parent's `Fin n` classifications removes the `Fin n` hypothesis entirely. -/

/-- **Sₐ classification, intrinsic form.** For *any* finite type `α`, the
symmetric group `Perm α` is solvable iff `Fintype.card α ≤ 4`. -/
theorem perm_solvable_iff_card (α : Type*) [DecidableEq α] [Fintype α] :
    IsSolvable (Perm α) ↔ Fintype.card α ≤ 4 := by
  rw [perm_solvable_congr (Fintype.equivFin α), sym_solvable_iff]

/-- **Aₐ classification, intrinsic form.** For *any* finite type `α`, the
alternating group `alternatingGroup α` is solvable iff `Fintype.card α ≤ 4`. -/
theorem alternating_solvable_iff_card (α : Type*) [DecidableEq α] [Fintype α] :
    IsSolvable (alternatingGroup α) ↔ Fintype.card α ≤ 4 := by
  rw [alternating_solvable_congr (Fintype.equivFin α), alternating_solvable_iff]

/-! ## §5  Cardinality is the only invariant that matters -/

/-- Solvability of the alternating group depends on the type only through its
cardinality — the parent's first future direction. -/
theorem alternating_solvable_iff_of_card_eq (h : Fintype.card α = Fintype.card β) :
    IsSolvable (alternatingGroup α) ↔ IsSolvable (alternatingGroup β) := by
  rw [alternating_solvable_iff_card, alternating_solvable_iff_card, h]

/-- Likewise for the symmetric group. -/
theorem perm_solvable_iff_of_card_eq (h : Fintype.card α = Fintype.card β) :
    IsSolvable (Perm α) ↔ IsSolvable (Perm β) := by
  rw [perm_solvable_iff_card, perm_solvable_iff_card, h]

/-- Equinumerous finite types have isomorphic alternating groups (the explicit
witness is `alternatingCongr`). -/
theorem nonempty_alternatingCongr_of_card_eq (h : Fintype.card α = Fintype.card β) :
    Nonempty (alternatingGroup α ≃* alternatingGroup β) :=
  ⟨alternatingCongr (Fintype.equivOfCardEq h)⟩

/-! ## §6  The threshold agreement, for an arbitrary finite type

Combining §4 with the parent bridge: for any finite `α`, `Perm α` and
`alternatingGroup α` are solvable *together*, and the common boundary sits at
cardinality `5`.  None of this requires `α = Fin n`. -/

/-- For any finite type, the symmetric and alternating groups are simultaneously
solvable, and the threshold is `Fintype.card α ≤ 4` for both. -/
theorem sym_alternating_solvable_iff_card (α : Type*) [DecidableEq α] [Fintype α] :
    (IsSolvable (Perm α) ↔ IsSolvable (alternatingGroup α)) ∧
      (IsSolvable (Perm α) ↔ Fintype.card α ≤ 4) := by
  refine ⟨(alternating_solvable_iff_sym_solvable α).symm, perm_solvable_iff_card α⟩

/-- **Sharp threshold, arbitrary type.** Any 4-element type has solvable
alternating group; any 5-element type does not — the jump is forced for every
finite type of that size, not just `Fin n`. -/
theorem sharp_threshold_card
    {α₄ : Type*} [DecidableEq α₄] [Fintype α₄] (h₄ : Fintype.card α₄ = 4)
    {α₅ : Type*} [DecidableEq α₅] [Fintype α₅] (h₅ : Fintype.card α₅ = 5) :
    IsSolvable (alternatingGroup α₄) ∧ ¬IsSolvable (alternatingGroup α₅) := by
  refine ⟨(alternating_solvable_iff_card α₄).mpr (by omega),
    fun hsolv => ?_⟩
  have := (alternating_solvable_iff_card α₅).mp hsolv
  omega

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01
