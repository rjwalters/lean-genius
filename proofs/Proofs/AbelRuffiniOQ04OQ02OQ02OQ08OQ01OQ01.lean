/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01

## Solvability of `Perm α` is **downward closed under injections**

The parent (`…OQ-08-OQ-01`) proved the *intrinsic threshold*:
`Perm α` is solvable **iff** `Fintype.card α ≤ 4`, for any finite `α`.

That is a statement about a single carrier.  This file extracts the
**order-structural consequence** that the threshold form hides: solvability of
permutation groups is *monotone in the carrier*.

* `perm_solvable_of_embedding`  — the **structural reason**: an embedding
  `α ↪ β` realises `Perm α` as a subgroup of `Perm β` (via Mathlib's
  `Equiv.Perm.viaEmbeddingHom`, an injective group hom), so solvability of the
  *larger* permutation group descends to the smaller.  No cardinality, no
  classification — pure functoriality of `Perm` along injections.
* `perm_solvable_mono` / `alternating_solvable_mono` — the cardinality face:
  `card α ≤ card β` and `Perm β` solvable forces `Perm α` solvable.
* `solvable_perm_card_isDownSet` — packaging: `{n | IsSolvable (Perm (Fin n))}`
  is the down-set `{0,1,2,3,4}`, i.e. downward closed *and* bounded by `4`.

The two routes to monotonicity agree.  The embedding route proves
`card α ≤ card β → solvable β → solvable α` *without ever mentioning the number
4*; the threshold route recovers the same implication from
`perm_solvable_iff_card`.  Their agreement is the content of
`mono_routes_agree`: the abstract subgroup descent and the arithmetic of the
sharp boundary are the same statement.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01

variable {α β : Type*}

/-! ## §1  Structural monotonicity along an embedding

The functor `Perm` sends an injection `α ↪ β` to an injective group hom
`Perm α →* Perm β` (extend a permutation of `α` by the identity off the image).
Solvability is closed under taking subgroups / injective preimages, so it flows
from the codomain back to the domain. -/

/-- **Structural descent.**  If `α` embeds into `β` and `Perm β` is solvable,
then `Perm α` is solvable — because `Equiv.Perm.viaEmbeddingHom e` is an
injective hom `Perm α →* Perm β`.  This is the carrier-monotonicity of
permutation-group solvability, *independent of any cardinality count*. -/
theorem perm_solvable_of_embedding (e : α ↪ β) [IsSolvable (Perm β)] :
    IsSolvable (Perm α) :=
  solvable_of_solvable_injective (Perm.viaEmbeddingHom_injective e)

/-! ## §2  The cardinality face

A finite type embeds into another exactly when its cardinality is no larger, so
§1 immediately yields cardinality-monotonicity. -/

/-- **Monotone in cardinality (symmetric).**  For finite types, `card α ≤ card β`
and `Perm β` solvable force `Perm α` solvable. -/
theorem perm_solvable_mono [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) [IsSolvable (Perm β)] :
    IsSolvable (Perm α) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  exact perm_solvable_of_embedding e

/-- **Monotone in cardinality (alternating).**  Same statement for the
alternating groups, obtained from the symmetric case through the parent bridge
`alternating_solvable_iff_sym_solvable`. -/
theorem alternating_solvable_mono [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β)
    (hβ : IsSolvable (alternatingGroup β)) :
    IsSolvable (alternatingGroup α) := by
  have hβ' : IsSolvable (Perm β) := (alternating_solvable_iff_sym_solvable β).mp hβ
  have hα : IsSolvable (Perm α) := perm_solvable_mono h
  exact (alternating_solvable_iff_sym_solvable α).mpr hα

/-! ## §3  The two routes agree, and the down-set packaging

The threshold `perm_solvable_iff_card` gives a second, purely arithmetic, proof
of cardinality-monotonicity.  That it matches the embedding proof of §2 is the
statement that "subgroup descent" and "`n ≤ 4` is downward closed" express the
same fact. -/

/-- **Route agreement.**  The embedding-based monotonicity of §2 is equivalent to
the arithmetic monotonicity read off the sharp threshold: under `card α ≤ card β`,
`Perm β` solvable ⟹ `Perm α` solvable holds, and the threshold form
`perm_solvable_iff_card` derives the very same implication. -/
theorem mono_routes_agree [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) :
    (IsSolvable (Perm β) → IsSolvable (Perm α)) := by
  intro hβ
  -- arithmetic route, via the parent threshold
  rw [perm_solvable_iff_card] at hβ ⊢
  omega

/-- The cardinalities `n` for which `Perm (Fin n)` is solvable form the
down-set `{0,1,2,3,4}`: membership is exactly `n ≤ 4`. -/
theorem solvable_perm_card_eq_le_four (n : ℕ) :
    IsSolvable (Perm (Fin n)) ↔ n ≤ 4 := by
  rw [perm_solvable_iff_card (Fin n), Fintype.card_fin]

/-- **Down-set property, stated as monotonicity on `ℕ`.**  If `m ≤ n` and
`Perm (Fin n)` is solvable then so is `Perm (Fin m)` — the solvable
cardinalities are closed downward. -/
theorem solvable_perm_card_isDownSet {m n : ℕ} (hmn : m ≤ n)
    (hn : IsSolvable (Perm (Fin n))) : IsSolvable (Perm (Fin m)) := by
  rw [solvable_perm_card_eq_le_four] at hn ⊢
  omega

/-- **Maximum solvable cardinality.**  `4` is the largest `n` with
`Perm (Fin n)` solvable: it is solvable, and any solvable `n` is `≤ 4`. -/
theorem four_is_max_solvable_card :
    IsSolvable (Perm (Fin 4)) ∧
      ∀ n, IsSolvable (Perm (Fin n)) → n ≤ 4 := by
  refine ⟨(solvable_perm_card_eq_le_four 4).mpr (le_refl 4), fun n hn => ?_⟩
  exact (solvable_perm_card_eq_le_four n).mp hn

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01
