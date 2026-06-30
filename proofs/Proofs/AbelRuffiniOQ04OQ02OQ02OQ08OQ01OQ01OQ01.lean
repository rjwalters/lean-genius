/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01

## Non-solvability of `Perm α` is **upward closed under injections**

The parent (`…OQ-01-OQ-01`) proved that solvability of permutation groups is
*downward closed in the carrier*: `{n | IsSolvable (Perm (Fin n))}` is the
down-set `{0,1,2,3,4}`.  This file proves the **order-theoretic dual**, the other
half of the dichotomy:

* `perm_not_solvable_of_embedding` — the **structural reason**: it is the exact
  contrapositive of the parent's `perm_solvable_of_embedding`.  If `α ↪ β` and
  `Perm α` is *not* solvable, then `Perm β` is *not* solvable either — the
  pathology of the *smaller* permutation group infects the *larger* one (an
  unsolvable `Perm α` sits inside `Perm β` as a subgroup, so `Perm β` cannot be
  solvable).
* `perm_not_solvable_mono` / `alternating_not_solvable_mono` — the cardinality
  face: `card α ≤ card β` and `Perm α` unsolvable forces `Perm β` unsolvable.
* `not_solvable_perm_card_isUpSet` — packaging:
  `{n | ¬ IsSolvable (Perm (Fin n))}` is the up-set `{n | 5 ≤ n}`, upward closed.

Together with the parent these say: the solvable and unsolvable cardinalities
**partition `ℕ`** as an order-complementary down-set / up-set pair, meeting at the
Abel–Ruffini boundary, where the least unsolvable cardinality `5` is the
successor of the greatest solvable one `4` (`five_is_min_unsolvable_card`,
`solvable_unsolvable_partition`, `boundary_is_successor`).

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01

variable {α β : Type*}

/-! ## §1  Structural co-monotonicity along an embedding

The parent's `perm_solvable_of_embedding` lets solvability flow *down* an
injection `α ↪ β` (from the codomain back to the domain).  Reading that
contrapositively, *non*-solvability flows *up*: an unsolvable `Perm α` realised
as a subgroup of `Perm β` obstructs solvability of the whole `Perm β`. -/

/-- **Structural ascent (contrapositive of `perm_solvable_of_embedding`).**
If `α` embeds into `β` and `Perm α` is *not* solvable, then `Perm β` is *not*
solvable — an unsolvable permutation group cannot embed into a solvable one. -/
theorem perm_not_solvable_of_embedding (e : α ↪ β)
    (hα : ¬ IsSolvable (Perm α)) : ¬ IsSolvable (Perm β) := by
  intro hβ
  haveI := hβ
  exact hα (perm_solvable_of_embedding e)

/-! ## §2  The cardinality face

A finite type embeds into another exactly when its cardinality is no larger, so
§1 immediately yields cardinality co-monotonicity of non-solvability. -/

/-- **Co-monotone in cardinality (symmetric).**  For finite types,
`card α ≤ card β` and `Perm α` unsolvable force `Perm β` unsolvable. -/
theorem perm_not_solvable_mono [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β)
    (hα : ¬ IsSolvable (Perm α)) : ¬ IsSolvable (Perm β) := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le h
  exact perm_not_solvable_of_embedding e hα

/-- **Co-monotone in cardinality (alternating).**  Same statement for the
alternating groups, transported through the grandparent bridge
`sym_not_solvable_iff_alternating_not_solvable`. -/
theorem alternating_not_solvable_mono [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β)
    (hα : ¬ IsSolvable (alternatingGroup α)) :
    ¬ IsSolvable (alternatingGroup β) := by
  have hpα : ¬ IsSolvable (Perm α) :=
    (sym_not_solvable_iff_alternating_not_solvable α).mpr hα
  have hpβ : ¬ IsSolvable (Perm β) := perm_not_solvable_mono h hpα
  exact (sym_not_solvable_iff_alternating_not_solvable β).mp hpβ

/-! ## §3  The up-set packaging and the dichotomy

The threshold `perm_solvable_iff_card` turns non-solvability into the arithmetic
predicate `5 ≤ n`, exhibiting the unsolvable cardinalities as the up-set
order-complementary to the parent's down-set `{≤4}`. -/

/-- The cardinalities `n` for which `Perm (Fin n)` is **not** solvable form the
up-set `{n | 5 ≤ n}`: non-solvability is exactly `5 ≤ n`. -/
theorem not_solvable_perm_card_eq_ge_five (n : ℕ) :
    ¬ IsSolvable (Perm (Fin n)) ↔ 5 ≤ n := by
  rw [perm_solvable_iff_card (Fin n), Fintype.card_fin]
  omega

/-- **Up-set property, stated as co-monotonicity on `ℕ`.**  If `m ≤ n` and
`Perm (Fin m)` is unsolvable then so is `Perm (Fin n)` — the unsolvable
cardinalities are closed upward. -/
theorem not_solvable_perm_card_isUpSet {m n : ℕ} (hmn : m ≤ n)
    (hm : ¬ IsSolvable (Perm (Fin m))) : ¬ IsSolvable (Perm (Fin n)) := by
  rw [not_solvable_perm_card_eq_ge_five] at hm ⊢
  omega

/-- **Minimum unsolvable cardinality.**  `5` is the least `n` with
`Perm (Fin n)` unsolvable: it is unsolvable, and any unsolvable `n` is `≥ 5`.
This is the order-dual of the parent's `four_is_max_solvable_card`. -/
theorem five_is_min_unsolvable_card :
    ¬ IsSolvable (Perm (Fin 5)) ∧
      ∀ n, ¬ IsSolvable (Perm (Fin n)) → 5 ≤ n := by
  refine ⟨(not_solvable_perm_card_eq_ge_five 5).mpr (le_refl 5), fun n hn => ?_⟩
  exact (not_solvable_perm_card_eq_ge_five n).mp hn

/-- **Order-complementarity.**  Non-solvability of `Perm (Fin n)` is precisely
the negation of the parent's solvability predicate `n ≤ 4`: the up-set and the
down-set are set-theoretic complements in `ℕ`. -/
theorem not_solvable_iff_not_le_four (n : ℕ) :
    ¬ IsSolvable (Perm (Fin n)) ↔ ¬ (n ≤ 4) := by
  rw [solvable_perm_card_eq_le_four]

/-- **The partition.**  The solvable cardinalities (down-set `{≤4}`) and the
unsolvable cardinalities (up-set `{≥5}`) partition `ℕ`: every `n` lies in exactly
one of the two faces. -/
theorem solvable_unsolvable_partition (n : ℕ) :
    (IsSolvable (Perm (Fin n)) ∧ ¬ (5 ≤ n)) ∨
      (¬ IsSolvable (Perm (Fin n)) ∧ 5 ≤ n) := by
  rcases le_or_gt 5 n with h | h
  · exact Or.inr ⟨(not_solvable_perm_card_eq_ge_five n).mpr h, h⟩
  · exact Or.inl ⟨(solvable_perm_card_eq_le_four n).mpr (by omega), by omega⟩

/-- **The boundary is a successor.**  The two faces meet at the Abel–Ruffini
boundary: the greatest solvable cardinality is `4`, the least unsolvable one is
`5`, and they are adjacent (`4 + 1 = 5`).  This packages the parent's
`four_is_max_solvable_card` with this file's `five_is_min_unsolvable_card`. -/
theorem boundary_is_successor :
    (∀ n, IsSolvable (Perm (Fin n)) → n ≤ 4) ∧
      (∀ n, ¬ IsSolvable (Perm (Fin n)) → 5 ≤ n) ∧
      (4 + 1 = 5) :=
  ⟨four_is_max_solvable_card.2, five_is_min_unsolvable_card.2, rfl⟩

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01
