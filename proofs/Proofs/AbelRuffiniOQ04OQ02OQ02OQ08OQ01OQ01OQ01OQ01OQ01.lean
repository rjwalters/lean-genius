/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01

## Reflection is symmetric; the escape *cost* is not (additive 5 vs multiplicative 6)

The parent file (`…OQ-01`) contrasted the two type operations by claiming that
**products reflect** solvability to their factors while **sums fail to
preserve** it.  That pairing compares the wrong faces of the two operations.
Reflection (solvability of the whole forces solvability of a piece) and
preservation (solvability of the pieces forces solvability of the whole) are
*different* directions, and the honest accounting is:

* **Both operations reflect.**  A summand injects into the disjoint union
  (`Sum.inl : α ↪ α ⊕ β`) exactly as a factor injects into the product, so
  `card α ≤ card α + card β` and `card α ≤ card α · card β` alike.  Solvability of
  `Perm (α ⊕ β)` *and* of `Perm (α × β)` therefore descends to `Perm α`
  (`both_operations_reflect_solvability`).
* **Neither operation preserves.**  `Perm (Fin 2)` and `Perm (Fin 3)` are
  solvable, yet *both* `Perm (Fin 2 ⊕ Fin 3)` (5 points) and
  `Perm (Fin 2 × Fin 3)` (6 points) are unsolvable
  (`neither_operation_preserves_solvability`).

So `⊕` and `×` sit on the *same* side of reflection and the *same* side of
preservation.  What truly separates them is the **cost of escaping** the
solvable range `{0,1,2,3,4}`:

* **Additive escape is `5`.**  `5 = 2 + 3` is a sum of two solvable
  cardinalities, and `5` is the least unsolvable degree.
* **Multiplicative escape is `6`.**  No product of two solvable cardinalities
  ever equals `5` — `5` is prime, so one factor would have to be `5 > 4`
  (`no_solvable_product_equals_five`).  The first product of two *nontrivial*
  solvable cardinalities that escapes is `2 · 3 = 6`
  (`min_nontrivial_product_escape`).

Hence the multiplicative boundary lies strictly *above* the additive one: the
degree `5` is additively reachable from the solvable range but multiplicatively
skipped (`escape_cost_asymmetry`).  This is the precise arithmetic shadow of the
Abel–Ruffini threshold under the algebra of finite types.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01 AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01

variable {α β : Type*}

/-! ## §1  Reflection is symmetric between `⊕` and `×`

A summand and a factor both inject into the composite carrier, so each only
*grows* the point count: `card α ≤ card α + card β` and
`card α ≤ card α · card β` (the latter once `β` is nonempty).  Solvability of the
composite — an upper bound on the composite's point count — therefore forces the
threshold on each piece.  The parent file proved the product half; here we add
the sum half and package both. -/

/-- **Sums reflect solvability (first summand).**  If `Perm (α ⊕ β)` is solvable
then so is `Perm α`: the summand has no more points than the union. -/
theorem perm_sum_reflects_solvable_left [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (h : IsSolvable (Perm (α ⊕ β))) :
    IsSolvable (Perm α) := by
  rw [perm_sum_solvable_iff] at h
  rw [perm_solvable_iff_card]
  omega

/-- **Sums reflect solvability (second summand).**  Symmetric statement for the
right summand. -/
theorem perm_sum_reflects_solvable_right [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (h : IsSolvable (Perm (α ⊕ β))) :
    IsSolvable (Perm β) := by
  rw [perm_sum_solvable_iff] at h
  rw [perm_solvable_iff_card]
  omega

/-- **Both operations reflect solvability.**  Reflection — solvability of the
composite descends to a piece — holds for the disjoint union *and* for the
product.  (The product half needs a nonempty cofactor so that the factor really
injects; the sum half needs nothing.)  This corrects the parent file's framing:
`⊕` is not the "non-reflecting" operation — it reflects exactly as `×` does. -/
theorem both_operations_reflect_solvability :
    (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        IsSolvable (Perm (α ⊕ β)) → IsSolvable (Perm α)) ∧
      (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
          [Nonempty β], IsSolvable (Perm (α × β)) → IsSolvable (Perm α)) := by
  refine ⟨fun α β _ _ _ _ h => perm_sum_reflects_solvable_left h, ?_⟩
  intro α β _ _ _ _ _ h
  exact perm_solvable_of_prod_solvable h

/-! ## §2  Neither operation preserves solvability

The opposite direction fails for *both* constructions: solvable pieces can build
an unsolvable composite.  The disjoint union of `2` and `3` points has `5`
points; the product has `6`.  Both exceed the Abel–Ruffini threshold. -/

/-- **The product `Perm (Fin 2 × Fin 3)` is not solvable** — it has `6` points. -/
theorem perm_prod_fin_two_three_not_solvable :
    ¬ IsSolvable (Perm (Fin 2 × Fin 3)) := by
  rw [perm_prod_solvable_iff, Fintype.card_fin, Fintype.card_fin]
  omega

/-- **Neither operation preserves solvability.**  For the disjoint union and for
the product alike, there are solvable pieces (`Perm (Fin 2)`, `Perm (Fin 3)`)
whose composite is unsolvable.  Together with
`both_operations_reflect_solvability` this places `⊕` and `×` on the *same* side
of both implications: both reflect, neither preserves. -/
theorem neither_operation_preserves_solvability :
    ¬ (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        IsSolvable (Perm α) → IsSolvable (Perm β) → IsSolvable (Perm (α ⊕ β))) ∧
      ¬ (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
          IsSolvable (Perm α) → IsSolvable (Perm β) → IsSolvable (Perm (α × β))) := by
  obtain ⟨hs2, hs3, hns⟩ := perm_sum_solvability_not_preserved
  refine ⟨fun hbad => hns (hbad (Fin 2) (Fin 3) hs2 hs3), fun hbad => ?_⟩
  exact perm_prod_fin_two_three_not_solvable (hbad (Fin 2) (Fin 3) hs2 hs3)

/-! ## §3  The escape cost: additive `5`, multiplicative `6`

What genuinely distinguishes the two operations is the *least* value outside the
solvable range `{0,1,2,3,4}` that they can manufacture from solvable inputs.

For sums it is `5` (`= 2 + 3`).  For products `5` is unreachable: `5` is prime,
so a product equal to `5` needs a factor `5 > 4`, i.e. a piece that is *already*
unsolvable.  The first product of two solvable cardinalities that escapes
without a pre-unsolvable factor is therefore `2 · 3 = 6`. -/

/-- **No product of two solvable cardinalities equals `5`.**  Since `5` is prime,
`m · n = 5` forces a factor to be `5`, contradicting `m, n ≤ 4`. -/
theorem no_solvable_product_equals_five (m n : ℕ) (hm : m ≤ 4) (hn : n ≤ 4) :
    m * n ≠ 5 := by
  interval_cases m <;> interval_cases n <;> omega

/-- **No product of two nontrivial naturals equals `5`.**  A free-standing
arithmetic fact (`5` prime): if `2 ≤ m` and `2 ≤ n` then `m · n ≠ 5`.  Used to
show the multiplicative escape skips `5`. -/
theorem no_nontrivial_product_equals_five (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    m * n ≠ 5 := by
  rcases le_or_gt 3 m with h3 | h3
  · have : 6 ≤ m * n := by
      calc 6 = 3 * 2 := rfl
        _ ≤ m * n := Nat.mul_le_mul h3 hn
    omega
  · interval_cases m
    omega

/-- **Minimal nontrivial multiplicative escape is `6`.**  Among products of two
factors each at least `2`, every value that leaves the solvable range `{≤4}` is
at least `6` — the value `5` is skipped — and `6 = 2 · 3` is attained.  This is
the multiplicative analogue of "the additive escape is `5`". -/
theorem min_nontrivial_product_escape :
    (∀ m n : ℕ, 2 ≤ m → 2 ≤ n → 4 < m * n → 6 ≤ m * n) ∧
      (2 ≤ 2 ∧ 2 ≤ 3 ∧ 2 * 3 = 6 ∧ 4 < 2 * 3) := by
  refine ⟨fun m n hm hn h => ?_, by norm_num⟩
  have h5 : m * n ≠ 5 := no_nontrivial_product_equals_five m n hm hn
  omega

/-! ## §4  The escape-cost asymmetry, in solvability terms

Side by side: `5` is additively reachable from the solvable range and is
unsolvable; the same `5` is *not* multiplicatively reachable from the solvable
range; and the first multiplicative escape, `2 · 3 = 6`, is unsolvable.  The
multiplicative boundary therefore lies strictly above the additive one. -/

/-- **Escape-cost asymmetry.**  Three facts in one:

1. *Additive escape at `5`*: `5 = 2 + 3` is a sum of two solvable cardinalities
   and `Perm (Fin (2 + 3))` is unsolvable.
2. *No multiplicative escape at `5`*: no product of two solvable cardinalities
   equals `5`.
3. *Multiplicative escape at `6`*: `6 = 2 · 3` is a product of two solvable
   cardinalities and `Perm (Fin (2 * 3))` is unsolvable.

So the degree `5` is additively reachable from `{≤4}` but multiplicatively
skipped: the Abel–Ruffini threshold is crossed one step later under `×` than
under `⊕`. -/
theorem escape_cost_asymmetry :
    (2 ≤ 4 ∧ 3 ≤ 4 ∧ 2 + 3 = 5 ∧ ¬ IsSolvable (Perm (Fin (2 + 3)))) ∧
      (∀ m n, m ≤ 4 → n ≤ 4 → m * n ≠ 5) ∧
      (2 ≤ 4 ∧ 3 ≤ 4 ∧ 2 * 3 = 6 ∧ ¬ IsSolvable (Perm (Fin (2 * 3)))) := by
  refine ⟨⟨by omega, by omega, by omega, ?_⟩,
    no_solvable_product_equals_five, by omega, by omega, by omega, ?_⟩
  · exact (not_solvable_perm_card_eq_ge_five _).mpr (by omega)
  · exact (not_solvable_perm_card_eq_ge_five _).mpr (by omega)

/-- **The multiplicative boundary strictly exceeds the additive boundary.**  The
least unsolvable degree reachable as a sum of two nontrivial solvable
cardinalities is `5`; reachable as a product of two nontrivial solvable
cardinalities it is `6`.  Stated as a strict inequality between the two minimal
escapes. -/
theorem multiplicative_boundary_above_additive :
    (∃ m n, 2 ≤ m ∧ 2 ≤ n ∧ m ≤ 4 ∧ n ≤ 4 ∧ m + n = 5) ∧
      (∀ m n, 2 ≤ m → 2 ≤ n → m * n ≠ 5) ∧
      (5 : ℕ) < 6 := by
  refine ⟨⟨2, 3, by omega, by omega, by omega, by omega, by omega⟩,
    no_nontrivial_product_equals_five, by omega⟩

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01
