/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01

## The Abel–Ruffini boundary under the type operations `⊕` and `×`

The ancestors of this file pinned solvability of `Perm α` to a single
arithmetic threshold (`Perm α` solvable `↔ Fintype.card α ≤ 4`) and showed the
solvable cardinalities form the down-set `{≤4}`, the unsolvable ones the up-set
`{≥5}`.  Those describe one carrier at a time.

This file asks how the threshold interacts with the **algebra of finite types**:
disjoint union `α ⊕ β` (cardinality `card α + card β`) and product `α × β`
(cardinality `card α · card β`).  The threshold turns each into a purely
arithmetic side-condition:

* `perm_sum_solvable_iff`  — `Perm (α ⊕ β)` solvable `↔ card α + card β ≤ 4`;
* `perm_prod_solvable_iff` — `Perm (α × β)` solvable `↔ card α · card β ≤ 4`.

The pay-off is a genuine asymmetry between the two operations, invisible at the
level of a single carrier:

* **Products reflect solvability to their factors** (`perm_solvable_of_prod_solvable`):
  a factor of a solvable permutation-product is itself solvable, because
  `card α ≤ card α · card β` once `β` is nonempty.  Solvability of a product is
  *inherited downward* by the pieces.
* **Disjoint unions do *not* preserve solvability** (`perm_sum_solvability_not_preserved`):
  `Perm (Fin 2)` and `Perm (Fin 3)` are both solvable, yet `Perm (Fin 2 ⊕ Fin 3)`
  is not — the union has `5` points.  Joining two solvable systems can manufacture
  an unsolvable one.

That failure is *exactly* the Abel–Ruffini phenomenon read combinatorially: the
solvable cardinalities `{0,1,2,3,4}` are **not closed under addition**, and the
smallest sum of two of them that escapes is `2 + 3 = 5` — the least unsolvable
degree (`abel_ruffini_is_additive_escape`).  Multiplicatively the escape costs
more: two factors each `≥ 2` already force a product `≥ 4`, and `2 · 3 = 6`
overshoots the boundary (`perm_prod_not_solvable_of_factors`).

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01 AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01

variable {α β : Type*}

/-! ## §1  The threshold under `⊕` and `×`

`Fintype.card_sum` and `Fintype.card_prod` evaluate the cardinality of the two
constructions, so the intrinsic threshold `perm_solvable_iff_card` rewrites
directly into an arithmetic condition on the cardinalities of the pieces. -/

/-- **Sum threshold.**  `Perm (α ⊕ β)` is solvable iff the *combined* point count
`card α + card β` is at most `4`. -/
theorem perm_sum_solvable_iff [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] :
    IsSolvable (Perm (α ⊕ β)) ↔ Fintype.card α + Fintype.card β ≤ 4 := by
  rw [perm_solvable_iff_card, Fintype.card_sum]

/-- **Product threshold.**  `Perm (α × β)` is solvable iff the *combined* point
count `card α · card β` is at most `4`. -/
theorem perm_prod_solvable_iff [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] :
    IsSolvable (Perm (α × β)) ↔ Fintype.card α * Fintype.card β ≤ 4 := by
  rw [perm_solvable_iff_card, Fintype.card_prod]

/-- **Alternating sum threshold.**  The same arithmetic for `Aₐ`, via the
intrinsic alternating classification: `alternatingGroup (α ⊕ β)` is solvable iff
`card α + card β ≤ 4`. -/
theorem alternating_sum_solvable_iff [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] :
    IsSolvable (alternatingGroup (α ⊕ β)) ↔ Fintype.card α + Fintype.card β ≤ 4 := by
  rw [alternating_solvable_iff_card, Fintype.card_sum]

/-! ## §2  Products reflect solvability to their factors

A nonempty second factor only *grows* the carrier: `card α ≤ card α · card β`.
So if the product permutation group is solvable (`card α · card β ≤ 4`), each
factor already satisfies the threshold.  Solvability of `Perm (α × β)` descends
to `Perm α` and `Perm β` — the product operation never hides an unsolvable
factor. -/

/-- **Products reflect solvability (first factor).**  If `β` is nonempty and
`Perm (α × β)` is solvable, then `Perm α` is solvable. -/
theorem perm_solvable_of_prod_solvable [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] [Nonempty β]
    (h : IsSolvable (Perm (α × β))) : IsSolvable (Perm α) := by
  rw [perm_prod_solvable_iff] at h
  rw [perm_solvable_iff_card]
  have hβ : 0 < Fintype.card β := Fintype.card_pos
  have hle : Fintype.card α ≤ Fintype.card α * Fintype.card β :=
    Nat.le_mul_of_pos_right _ hβ
  omega

/-- **Products reflect solvability (second factor).**  Symmetric statement: if
`α` is nonempty and `Perm (α × β)` is solvable, then `Perm β` is solvable. -/
theorem perm_solvable_of_prod_solvable' [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] [Nonempty α]
    (h : IsSolvable (Perm (α × β))) : IsSolvable (Perm β) := by
  rw [perm_prod_solvable_iff] at h
  rw [perm_solvable_iff_card]
  have hα : 0 < Fintype.card α := Fintype.card_pos
  have hle : Fintype.card β ≤ Fintype.card α * Fintype.card β :=
    Nat.le_mul_of_pos_left _ hα
  omega

/-- **Multiplicative escape.**  Two factors that are each at least moderately
sized already overshoot the boundary: if `2 ≤ card α` and `3 ≤ card β` then
`Perm (α × β)` is *not* solvable (`card α · card β ≥ 6 ≥ 5`).  The minimal
unsolvable product of two factors is `2 · 3`. -/
theorem perm_prod_not_solvable_of_factors [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (ha : 2 ≤ Fintype.card α) (hb : 3 ≤ Fintype.card β) :
    ¬ IsSolvable (Perm (α × β)) := by
  rw [perm_prod_solvable_iff]
  have hmul : 2 * 3 ≤ Fintype.card α * Fintype.card β := Nat.mul_le_mul ha hb
  omega

/-! ## §3  Disjoint unions do *not* preserve solvability

The contrast with §2: solvability of the *pieces* says nothing about solvability
of their union.  Two solvable permutation groups on `2` and `3` points combine to
a permutation group on `5` points, which is unsolvable.  This is the
Abel–Ruffini obstruction in combinatorial form. -/

/-- **Concrete unsolvable union.**  `Perm (Fin 2 ⊕ Fin 3)` is not solvable: the
disjoint union has `2 + 3 = 5` points. -/
theorem perm_sum_fin_two_three_not_solvable :
    ¬ IsSolvable (Perm (Fin 2 ⊕ Fin 3)) := by
  rw [perm_sum_solvable_iff, Fintype.card_fin, Fintype.card_fin]
  omega

/-- **Solvability is not preserved by `⊕`.**  Both pieces `Perm (Fin 2)` and
`Perm (Fin 3)` are solvable, yet their disjoint union `Perm (Fin 2 ⊕ Fin 3)` is
not.  This is the structural opposite of §2's product behaviour: joining solvable
systems can create an unsolvable one. -/
theorem perm_sum_solvability_not_preserved :
    IsSolvable (Perm (Fin 2)) ∧ IsSolvable (Perm (Fin 3)) ∧
      ¬ IsSolvable (Perm (Fin 2 ⊕ Fin 3)) := by
  refine ⟨?_, ?_, perm_sum_fin_two_three_not_solvable⟩
  · rw [perm_solvable_iff_card, Fintype.card_fin]; omega
  · rw [perm_solvable_iff_card, Fintype.card_fin]; omega

/-! ## §4  The boundary as the minimal additive escape

The failure of additive closure is sharp.  Reading the down-set `{≤4}` as a set
of "available" cardinalities, the smallest value reachable as a sum of two of
them that *leaves* the set is `5`, and `5` is precisely the least unsolvable
degree.  So the Abel–Ruffini threshold is the minimal additive escape of the
solvable cardinalities. -/

/-- **The Abel–Ruffini boundary is the minimal additive escape.**  `5` is a sum
of two solvable cardinalities (`2 + 3`, both `≤ 4`); it is unsolvable; and it is
the *least* such escape — any sum of two solvable cardinalities that is unsolvable
is at least `5`.  Combinatorially: the solvable set `{0,1,2,3,4}` first breaks
additive closure exactly at the Abel–Ruffini degree. -/
theorem abel_ruffini_is_additive_escape :
    (∃ m n, m ≤ 4 ∧ n ≤ 4 ∧ m + n = 5 ∧ ¬ IsSolvable (Perm (Fin (m + n)))) ∧
      (∀ m n, m ≤ 4 → n ≤ 4 → ¬ IsSolvable (Perm (Fin (m + n))) → 5 ≤ m + n) := by
  constructor
  · refine ⟨2, 3, by omega, by omega, by omega, ?_⟩
    rw [not_solvable_perm_card_eq_ge_five]
  · intro m n _ _ h
    exact (not_solvable_perm_card_eq_ge_five (m + n)).mp h

/-- **Closure dichotomy.**  Side by side: solvability is reflected by products
(a factor of a solvable product is solvable) but is not preserved by sums (a sum
of solvable pieces can be unsolvable).  The two operations sit on opposite sides
of the Abel–Ruffini boundary. -/
theorem product_reflects_sum_does_not :
    (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
        [Nonempty β], IsSolvable (Perm (α × β)) → IsSolvable (Perm α)) ∧
      ¬ (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
          IsSolvable (Perm α) → IsSolvable (Perm β) → IsSolvable (Perm (α ⊕ β))) := by
  refine ⟨fun α β _ _ _ _ _ h => perm_solvable_of_prod_solvable h, ?_⟩
  intro hbad
  obtain ⟨hs2, hs3, hns⟩ := perm_sum_solvability_not_preserved
  exact hns (hbad (Fin 2) (Fin 3) hs2 hs3)

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01
