/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01

## Drop nontriviality and survival becomes one-directional: `⊕`-survival ⊊ `×`-survival (AM–GM)

The parent file (`…OQ-01`) proved a **preservation coincidence**: for *nontrivial*
solvable pieces (each with at least `2` points), `Perm (α ⊕ β)` is solvable iff
`Perm (α × β)` is, the unique survivor being the single pair `(2,2)` for both
operations.  That symmetry was stated under the standing hypothesis
`card α, card β ≥ 2`.

This file asks the obvious next question: **what happens when the nontriviality
hypothesis is dropped?**  The clean coincidence collapses, but not into chaos —
it degrades into a precise *one-directional containment*, governed by the
arithmetic mean–geometric mean inequality:

* **Containment (unconditional).**  `4·(card α · card β) ≤ (card α + card β)²`
  (`four_mul_le_add_sq`), so `card α + card β ≤ 4` forces `card α · card β ≤ 4`.
  In solvability terms: **`Perm (α ⊕ β)` solvable ⟹ `Perm (α × β)` solvable**, with
  *no* hypothesis on the pieces (`perm_sum_solvable_imp_prod_solvable`).  The
  product is the strictly more permissive operation.
* **Converse fails.**  The pair `(Fin 1, Fin 4)` is a product-survivor that is not
  a sum-survivor: `1 · 4 = 4 ≤ 4` (solvable) while `1 + 4 = 5` (unsolvable)
  (`perm_prod_solvable_sum_not`).  So the inclusion of survivor sets is *strict*.
* **The gap is exactly the trivial pieces.**  Every product-survivor that fails to
  be a sum-survivor has a *trivial* piece (`card ≤ 1`)
  (`survival_gap_requires_trivial`).  Restricting to `card ≥ 2` deletes the entire
  gap, which is precisely *why* the parent's coincidence needed nontriviality:
  among pieces of size `≥ 2`, `card α · card β ≤ 4 ↔ card α + card β ≤ 4`
  (`nontriviality_restores_symmetry`).

So the survival sets of `⊕` and `×` are *nested, not equal*: sum-survival ⊊
product-survival, and the difference is carried entirely by the absorbing/neutral
trivial cardinalities `0` and `1` (`survival_containment_strict`,
`without_nontriviality_only_containment`).  The parent's symmetric picture is the
shadow this containment casts once the degenerate sizes are removed.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01 AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01

variable {α β : Type*}

/-! ## §1  The arithmetic mean–geometric mean core

The whole asymmetry rests on a single elementary inequality of naturals:
`4·a·b ≤ (a + b)²`, i.e. `a·b ≤ ((a+b)/2)²`.  It is the AM–GM inequality, and it
makes the *sum* threshold the harder one to satisfy: bounding `a + b` automatically
bounds `a · b`, but not conversely. -/

/-- **AM–GM for naturals.**  `4·(a·b) ≤ (a + b)²` for all `a b : ℕ`; equivalently
`a·b ≤ ((a+b)/2)²`.  The difference `(a + b)² - 4·a·b = (a - b)²` is a square, so the
inequality is sharp exactly when `a = b`. -/
theorem four_mul_le_add_sq (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]

/-- **Sum cap forces product cap (degree `4`).**  If `a + b ≤ 4` then `a · b ≤ 4`.
This is the AM–GM core specialised to the Abel–Ruffini solvable cap `4`:
`4·(a·b) ≤ (a+b)² ≤ 16`, hence `a·b ≤ 4`. -/
theorem add_le_four_imp_mul_le_four (a b : ℕ) (h : a + b ≤ 4) : a * b ≤ 4 := by
  have h1 : 4 * (a * b) ≤ (a + b) ^ 2 := four_mul_le_add_sq a b
  have h2 : (a + b) ^ 2 ≤ 16 := by
    have hm : (a + b) * (a + b) ≤ 4 * 4 := Nat.mul_le_mul h h
    nlinarith [hm]
  omega

/-! ## §2  Containment: the disjoint union survives less often than the product

The threshold characterisations `perm_sum_solvable_iff` and
`perm_prod_solvable_iff` (from the merged ancestor) turn §1 into a statement about
solvability: every solvable disjoint union is, automatically, a solvable product.
No nontriviality hypothesis is needed. -/

/-- **Sum-survival implies product-survival.**  For *any* finite pieces,
`Perm (α ⊕ β)` solvable ⟹ `Perm (α × β)` solvable.  The `⊕`-survivor set is
contained in the `×`-survivor set; the product is the more permissive operation. -/
theorem perm_sum_solvable_imp_prod_solvable [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β] (h : IsSolvable (Perm (α ⊕ β))) :
    IsSolvable (Perm (α × β)) := by
  rw [perm_sum_solvable_iff] at h
  rw [perm_prod_solvable_iff]
  exact add_le_four_imp_mul_le_four _ _ h

/-! ## §3  Strictness: a product-survivor that is not a sum-survivor

The inclusion of §2 is *strict*.  The witness is the degenerate pair
`(Fin 1, Fin 4)`: the product `Fin 1 × Fin 4` has `4` points and is solvable
(`S₄`), while the disjoint union `Fin 1 ⊕ Fin 4` has `5` points and is not.  A
single trivial factor (`card 1`, the multiplicative neutral) is enough to separate
the two operations. -/

/-- **A product-survivor that fails to be a sum-survivor.**  `Perm (Fin 1 × Fin 4)`
is solvable (`1 · 4 = 4`) but `Perm (Fin 1 ⊕ Fin 4)` is not (`1 + 4 = 5`).  Hence the
containment of §2 is strict. -/
theorem perm_prod_solvable_sum_not :
    IsSolvable (Perm (Fin 1 × Fin 4)) ∧ ¬ IsSolvable (Perm (Fin 1 ⊕ Fin 4)) := by
  refine ⟨perm_prod_solvable_iff.mpr ?_, fun h => ?_⟩
  · simp [Fintype.card_fin]
  · rw [perm_sum_solvable_iff, Fintype.card_fin, Fintype.card_fin] at h
    omega

/-- **Survival containment is strict.**  Packaged: the `⊕`-survivor set is contained
in the `×`-survivor set (for all pieces), and the inclusion is proper (witnessed by
`(Fin 1, Fin 4)`). -/
theorem survival_containment_strict :
    (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        IsSolvable (Perm (α ⊕ β)) → IsSolvable (Perm (α × β))) ∧
      (IsSolvable (Perm (Fin 1 × Fin 4)) ∧ ¬ IsSolvable (Perm (Fin 1 ⊕ Fin 4))) := by
  refine ⟨fun α β _ _ _ _ h => perm_sum_solvable_imp_prod_solvable h,
    perm_prod_solvable_sum_not⟩

/-! ## §4  The gap is exactly the trivial pieces

Why does the parent file's *equivalence* hold only under `card ≥ 2`?  Because every
pair living in the gap — a product-survivor (`a·b ≤ 4`) that is not a sum-survivor
(`a + b > 4`) — must have a *trivial* piece (`a ≤ 1` or `b ≤ 1`).  If both pieces
were `≥ 2`, then `a + b ≥ 5` would force one of them to be `≥ 3`, pushing the
product to `≥ 6 > 4`.  So nontriviality deletes the gap entirely. -/

/-- **The gap requires a trivial piece.**  If `a · b ≤ 4` yet `a + b > 4`, then one
of `a, b` is at most `1`.  Equivalently: among pieces of size `≥ 2`, a product-survivor
is always a sum-survivor.  This is the arithmetic reason the parent's preservation
*coincidence* needs the nontriviality hypothesis. -/
theorem survival_gap_requires_trivial (a b : ℕ) (hprod : a * b ≤ 4)
    (hsum : 4 < a + b) : a ≤ 1 ∨ b ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb⟩ := hcon
  rcases le_or_gt 3 a with h3 | h3
  · have h6 : 3 * 2 ≤ a * b := Nat.mul_le_mul h3 (by omega)
    omega
  · interval_cases a
    omega

/-- **Nontriviality restores the symmetry.**  For naturals `a, b ≥ 2`, the product
cap and the sum cap are *equivalent*: `a · b ≤ 4 ↔ a + b ≤ 4`.  This is the pure
arithmetic heart of the parent file's coincidence — both sides hold exactly at
`a = b = 2`. -/
theorem nontriviality_restores_symmetry (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    a * b ≤ 4 ↔ a + b ≤ 4 := by
  constructor
  · intro hp
    by_contra hs
    push_neg at hs
    rcases survival_gap_requires_trivial a b hp hs with h | h <;> omega
  · exact add_le_four_imp_mul_le_four a b

/-! ## §5  The full picture, side by side

Three facts assembled: the unconditional containment, the strict-inclusion witness,
and the parent's coincidence recovered as the `card ≥ 2` restriction.  The last
conjunct is the parent theorem `sum_prod_survival_coincide`, displayed here as the
*shadow* of the containment once the trivial cardinalities are removed. -/

/-- **Without nontriviality, only containment survives.**  A single statement:

1. *Containment* (any pieces): `Perm (α ⊕ β)` solvable ⟹ `Perm (α × β)` solvable.
2. *Strictness*: `(Fin 1, Fin 4)` is a product-survivor but not a sum-survivor.
3. *Restored symmetry* (`card ≥ 2`): the two are equivalent — the parent's
   coincidence, recovered as the restriction that excises the trivial gap of (2). -/
theorem without_nontriviality_only_containment :
    (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        IsSolvable (Perm (α ⊕ β)) → IsSolvable (Perm (α × β))) ∧
      (IsSolvable (Perm (Fin 1 × Fin 4)) ∧ ¬ IsSolvable (Perm (Fin 1 ⊕ Fin 4))) ∧
      (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        2 ≤ Fintype.card α → 2 ≤ Fintype.card β →
          (IsSolvable (Perm (α ⊕ β)) ↔ IsSolvable (Perm (α × β)))) := by
  refine ⟨fun α β _ _ _ _ h => perm_sum_solvable_imp_prod_solvable h,
    perm_prod_solvable_sum_not, ?_⟩
  intro α β _ _ _ _ ha hb
  exact sum_prod_survival_coincide ha hb

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01OQ01
