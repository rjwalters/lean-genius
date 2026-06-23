/-
# Abel–Ruffini — OQ-04 ▸ OQ-02 ▸ OQ-02 ▸ OQ-08 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01 ▸ OQ-01

## Escape diverges, survival coincides: `(2,2)` is the unique preservation survivor

The parent file (`…OQ-01`) proved an **asymmetry of escape cost**: starting from
the solvable range `{0,1,2,3,4}`, the disjoint union first manufactures an
unsolvable degree at `5 = 2 + 3`, while the product must wait until
`6 = 2 · 3` (the value `5` is prime, hence multiplicatively unreachable from
`{≤4}`).  Additive escape `5`, multiplicative escape `6`.

This file looks at the *opposite* face — **preservation** — and finds the
reverse pattern: the two operations **agree exactly**.  For *nontrivial* solvable
pieces (each with at least `2` points), the composite stays solvable only in one
single case, and it is the *same* case for both operations:

* **Unique additive survivor.**  `Perm (α ⊕ β)` is solvable with
  `card α, card β ≥ 2` iff `card α = card β = 2`
  (`perm_sum_nontrivial_solvable_iff`): any larger piece pushes the sum to `≥ 5`.
* **Unique multiplicative survivor.**  `Perm (α × β)` is solvable with
  `card α, card β ≥ 2` iff `card α = card β = 2`
  (`perm_prod_nontrivial_solvable_iff`): any larger piece pushes the product
  to `≥ 6`.

So although the two operations *escape* the solvable range at different degrees,
their sets of surviving nontrivial pairs are **identical** — the single pair
`(2,2)` — and for nontrivial solvable pieces solvability of the sum-composite is
therefore *equivalent* to solvability of the product-composite
(`sum_prod_survival_coincide`).  Because `2 + 2 = 4 = 2 · 2`, both composites
land on the *same* degree `4` — the largest solvable symmetric degree (`S₄` is
solvable), one step below the Abel–Ruffini threshold `5` (`survivor_at_four`,
`survivor_degree_below_threshold`).  That coincidence `2 + 2 = 2 · 2` is exactly
why the additive and multiplicative survivors land together.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Tactic
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01

open Equiv

namespace AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01

open AbelRuffiniOQ04OQ02OQ02OQ08 AbelRuffiniOQ04OQ02OQ02OQ08OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01 AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01
  AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01

variable {α β : Type*}

/-! ## §1  A nontrivial solvable piece has `2`, `3`, or `4` points

The intrinsic classification `perm_solvable_iff_card` caps a solvable piece at
`4` points; the "nontrivial" hypothesis `2 ≤ card` removes the degenerate `0`/`1`
cases.  So every nontrivial solvable piece sits in `{2,3,4}`. -/

/-- **Nontrivial solvable pieces live in `{2,3,4}`.**  If `Perm α` is solvable and
`α` has at least two points, its cardinality is `2`, `3`, or `4`. -/
theorem card_nontrivial_solvable_mem [DecidableEq α] [Fintype α]
    (hnt : 2 ≤ Fintype.card α) (hsol : IsSolvable (Perm α)) :
    Fintype.card α = 2 ∨ Fintype.card α = 3 ∨ Fintype.card α = 4 := by
  rw [perm_solvable_iff_card] at hsol
  omega

/-! ## §2  The unique additive survivor

A sum of two nontrivial pieces is solvable iff `card α + card β ≤ 4`; with both
summands at least `2`, that linear constraint forces both to equal `2`.  So `⊕`
preserves solvability of nontrivial pieces in exactly one configuration. -/

/-- **Unique additive survivor.**  For pieces with at least `2` points each,
`Perm (α ⊕ β)` is solvable iff both have *exactly* `2` points.  The only
nontrivial disjoint union that stays solvable is `2 + 2 = 4`. -/
theorem perm_sum_nontrivial_solvable_iff [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (ha : 2 ≤ Fintype.card α) (hb : 2 ≤ Fintype.card β) :
    IsSolvable (Perm (α ⊕ β)) ↔
      Fintype.card α = 2 ∧ Fintype.card β = 2 := by
  rw [perm_sum_solvable_iff]
  omega

/-! ## §3  The unique multiplicative survivor

The product is solvable iff `card α · card β ≤ 4`.  This bound is *nonlinear*, so
the cap is forced piece by piece: if either factor reached `3`, the product would
already be `≥ 6`.  Hence both factors equal `2` — the *same* survivor as for the
sum, despite the different (multiplicative) escape cost. -/

/-- **Unique multiplicative survivor.**  For factors with at least `2` points
each, `Perm (α × β)` is solvable iff both have *exactly* `2` points.  The only
nontrivial product that stays solvable is `2 · 2 = 4`. -/
theorem perm_prod_nontrivial_solvable_iff [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (ha : 2 ≤ Fintype.card α) (hb : 2 ≤ Fintype.card β) :
    IsSolvable (Perm (α × β)) ↔
      Fintype.card α = 2 ∧ Fintype.card β = 2 := by
  rw [perm_prod_solvable_iff]
  constructor
  · intro h
    have hα : Fintype.card α ≤ 2 := by
      rcases Nat.lt_or_ge (Fintype.card α) 3 with hlt | hge
      · omega
      · exfalso
        have : 3 * 2 ≤ Fintype.card α * Fintype.card β := Nat.mul_le_mul hge hb
        omega
    have hβ : Fintype.card β ≤ 2 := by
      rcases Nat.lt_or_ge (Fintype.card β) 3 with hlt | hge
      · omega
      · exfalso
        have : 2 * 3 ≤ Fintype.card α * Fintype.card β := Nat.mul_le_mul ha hge
        omega
    omega
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-! ## §4  Survival coincides though escape diverges

Both §2 and §3 reduce solvability of the nontrivial composite to the *same*
condition `card α = card β = 2`.  Chaining the two equivalences shows that for
nontrivial solvable pieces solvability of the **sum**-composite is equivalent to
solvability of the **product**-composite — even though, as the parent file
proved, the two operations leave the solvable range at *different* degrees
(`5` vs `6`).  Escape diverges; survival coincides. -/

/-- **Survival coincides.**  For pieces with at least `2` points each,
`Perm (α ⊕ β)` is solvable iff `Perm (α × β)` is.  Both hold exactly on the unique
survivor `card α = card β = 2`.  This is the preservation-side counterpart to the
parent file's escape-cost *asymmetry*: the operations agree on which nontrivial
pairs survive, while disagreeing on which degree they first break at. -/
theorem sum_prod_survival_coincide [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (ha : 2 ≤ Fintype.card α) (hb : 2 ≤ Fintype.card β) :
    IsSolvable (Perm (α ⊕ β)) ↔ IsSolvable (Perm (α × β)) := by
  rw [perm_sum_nontrivial_solvable_iff ha hb,
    perm_prod_nontrivial_solvable_iff ha hb]

/-- **The survivor is unique up to both operations.**  Among nontrivial solvable
pieces, *if either* composite is solvable then both pieces are `2`-point sets, and
*then both* composites are solvable.  Packaged as a single biconditional with the
arithmetic identity `2 + 2 = 2 · 2 = 4` that makes the two survivors land on the
same degree. -/
theorem unique_survivor_characterization [DecidableEq α] [DecidableEq β]
    [Fintype α] [Fintype β]
    (ha : 2 ≤ Fintype.card α) (hb : 2 ≤ Fintype.card β) :
    (IsSolvable (Perm (α ⊕ β)) ∨ IsSolvable (Perm (α × β))) ↔
      (Fintype.card α = 2 ∧ Fintype.card β = 2) := by
  constructor
  · rintro (h | h)
    · exact (perm_sum_nontrivial_solvable_iff ha hb).mp h
    · exact (perm_prod_nontrivial_solvable_iff ha hb).mp h
  · intro h
    exact Or.inl ((perm_sum_nontrivial_solvable_iff ha hb).mpr h)

/-! ## §5  The survivor, concretely: degree `4`

The unique survivor is `(Fin 2, Fin 2)`.  Both composites — the disjoint union
`Fin 2 ⊕ Fin 2` and the product `Fin 2 × Fin 2` — have `4` points, and `Perm` on
`4` points (`S₄`) is solvable.  The coincidence `2 + 2 = 4 = 2 · 2` is the reason
the additive and multiplicative survivors collapse to a single degree. -/

/-- **The survivor at degree `4`.**  Both `Perm (Fin 2 ⊕ Fin 2)` and
`Perm (Fin 2 × Fin 2)` are solvable, and `2 + 2 = 4 = 2 · 2`.  This is `S₄`, the
largest solvable symmetric group, realised simultaneously as a sum and as a
product of two copies of the `2`-point system. -/
theorem survivor_at_four :
    IsSolvable (Perm (Fin 2 ⊕ Fin 2)) ∧ IsSolvable (Perm (Fin 2 × Fin 2)) ∧
      (2 + 2 = 4) ∧ (2 * 2 = 4) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · rw [perm_sum_solvable_iff, Fintype.card_fin]
  · rw [perm_prod_solvable_iff, Fintype.card_fin]

/-- **The survivor sits one step below the threshold.**  The surviving composite
has `4` points; adding a single further point reaches `5`, where `Perm (Fin 5)` is
unsolvable.  So the unique preservation survivor lives at the very top of the
solvable range, immediately below the Abel–Ruffini degree. -/
theorem survivor_degree_below_threshold :
    Fintype.card (Fin 2 ⊕ Fin 2) = 4 ∧ Fintype.card (Fin 2 × Fin 2) = 4 ∧
      ¬ IsSolvable (Perm (Fin 5)) ∧ 4 + 1 = 5 := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [Fintype.card_sum, Fintype.card_fin]
  · rw [Fintype.card_prod, Fintype.card_fin]
  · rw [not_solvable_perm_card_eq_ge_five]

/-! ## §6  Escape-vs-survival, side by side

The closing statement places the parent's *escape* asymmetry next to this file's
*survival* coincidence.  Escape: the minimal nontrivial additive escape (`5`)
strictly precedes the multiplicative one (`6`).  Survival: the unique nontrivial
survivor is the *same* pair `(2,2)` for both operations, landing on the *same*
degree `4`.  Two faces of the boundary `{≤4}`: where it breaks differs by
operation; where it holds does not. -/

/-- **Escape diverges, survival coincides.**  A single statement contrasting the
two faces:

* *Escape (asymmetric).*  There is a nontrivial additive escape at `5`
  (`2 + 3`, both `≤ 4`) but **no** product of two factors `≥ 2` equals `5`, so the
  least nontrivial multiplicative escape is `6` — strictly above the additive `5`.
* *Survival (symmetric).*  For nontrivial solvable pieces, the sum-composite is
  solvable iff the product-composite is, and both happen exactly on the unique
  pair `(2,2)`, with `2 + 2 = 4 = 2 · 2`. -/
theorem escape_diverges_survival_coincides :
    -- escape diverges
    ((∃ m n : ℕ, 2 ≤ m ∧ 2 ≤ n ∧ m ≤ 4 ∧ n ≤ 4 ∧ m + n = 5) ∧
        (∀ m n : ℕ, 2 ≤ m → 2 ≤ n → m * n ≠ 5) ∧ (5 : ℕ) < 6) ∧
      -- survival coincides
      (∀ (α β : Type) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β],
        2 ≤ Fintype.card α → 2 ≤ Fintype.card β →
          (IsSolvable (Perm (α ⊕ β)) ↔ IsSolvable (Perm (α × β)))) := by
  refine ⟨⟨⟨2, 3, by omega, by omega, by omega, by omega, by omega⟩, ?_, by omega⟩, ?_⟩
  · exact no_nontrivial_product_equals_five
  · intro α β _ _ _ _ ha hb
    exact sum_prod_survival_coincide ha hb

end AbelRuffiniOQ04OQ02OQ02OQ08OQ01OQ01OQ01OQ01OQ01OQ01
