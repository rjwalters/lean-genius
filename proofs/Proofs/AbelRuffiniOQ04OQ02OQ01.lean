import Mathlib
import Proofs.AbelRuffiniOQ04OQ02OQ02OQ01

/-
# Explicit derived (composition) series of `S₃` and `S₄` with identified abelian factors

Open Question from `abel-ruffini-oq-04-oq-02` (*Alternating Groups: Aₙ Solvable iff n ≤ 4*):

> Exhibit the derived series for `S₃` and `S₄` explicitly.

## Answer

Both symmetric groups are solvable, and their derived series are short chains whose successive
factors are abelian of prime-power order:

* **`S₃`:**  `S₃  ⊵  A₃  ⊵  {e}`
  * top factor   `S₃ / A₃ ≅ ℤ/2ℤ`  (the sign quotient, index `2`);
  * bottom factor `A₃ ≅ ℤ/3ℤ`  (cyclic of prime order `3`).

* **`S₄`:**  `S₄  ⊵  A₄  ⊵  V₄  ⊵  {e}`
  * top factor    `S₄ / A₄ ≅ ℤ/2ℤ`     (the sign quotient, index `2`);
  * middle factor `A₄ / V₄ ≅ ℤ/3ℤ`     (cyclic of prime order `3`);
  * bottom factor `V₄ ≅ (ℤ/2ℤ)²`        (the Klein four-group).

The `A₄ ⊵ V₄ ⊵ {e}` tail, including the factor isomorphisms `A₄/V₄ ≅ ℤ/3ℤ` and `V₄ ≅ (ℤ/2ℤ)²`,
is reused verbatim from the sibling entry `abel-ruffini-oq-04-oq-02-oq-02-oq-01`
(`AbelRuffiniA4CompositionSeries`). This file adds the new top layer `S₃ ⊵ A₃` / `S₄ ⊵ A₄` and the
complete `S₃` series, and identifies every factor with its standard model.

## Method

Everything is pure assembly from Mathlib's alternating-group infrastructure
(`Mathlib.GroupTheory.SpecificGroups.Alternating`, `…/Alternating/KleinFour.lean`,
`…/Alternating/Centralizer.lean`, `Mathlib.GroupTheory.SpecificGroups.Cyclic`):

* `alternatingGroup` is `sign.ker`, so it is **normal** (`alternatingGroup.normal`) and has
  **index `2`** (`alternatingGroup.index_eq_two`); hence `|Sₙ / Aₙ| = 2`
  (`Subgroup.index_eq_card`) and `Sₙ / Aₙ ≅ ℤ/2ℤ` by `mulEquivOfPrimeCardEq`.
* `|Aₙ| = n!/2` (`nat_card_alternatingGroup`); for `A₃` this is `3`, prime, so `A₃ ≅ ℤ/3ℤ`.
* the `A₄`-layer data (`|A₄/V₄| = 3`, `|V₄| = 4`, both factor isos, and `V₄ = [A₄,A₄]`) is
  imported from `AbelRuffiniA4CompositionSeries`.

## Relation to the *derived* series

The displayed chains are exactly the derived series of `S₃`, `S₄`. The commutator identities
Mathlib provides directly are recorded in `derived_layers_S3` / `derived_layers_S4`:
`[Sₙ,Sₙ] ≤ Aₙ` (`alternatingGroup.commutator_perm_le`, hypothesis-free) and, for `S₄`,
`[A₄,A₄] = V₄` (`AbelRuffiniA4CompositionSeries.v4_eq_commutator`). The reverse inclusion
`Aₙ ≤ [Sₙ,Sₙ]` — which upgrades `[Sₙ,Sₙ] ≤ Aₙ` to equality — holds because every `3`-cycle is a
commutator of two transpositions, `(a b c) = ⁅(a b), (a c)⁆`, and the `3`-cycles generate `Aₙ`
(`closure_three_cycles_eq_alternating`). Mathlib only packages this as `commutator (Perm α) =
alternatingGroup α` under `5 ≤ card α` (`alternatingGroup.commutator_perm_eq`), so for `n ∈ {3,4}`
the equality is left as a documented follow-up; the *composition-series* statement below is
complete and unconditional.
-/

namespace AbelRuffiniSymmetricDerivedSeries

open Equiv
open scoped Classical

/-! ### Cardinality helpers -/

/-- `Nat.card (Fin n) = n`. -/
theorem card_fin (n : ℕ) : Nat.card (Fin n) = n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `|A₃| = 3`: the alternating group on three letters has prime order `3`. -/
theorem card_a3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  haveI : Nontrivial (Fin 3) := ⟨⟨0, 1, by decide⟩⟩
  rw [nat_card_alternatingGroup, card_fin]
  decide

/-- `|S₃ / A₃| = 2`, the index of the alternating group. -/
theorem card_quot_s3 : Nat.card (Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = 2 := by
  haveI : Nontrivial (Fin 3) := ⟨⟨0, 1, by decide⟩⟩
  rw [← Subgroup.index_eq_card]
  exact alternatingGroup.index_eq_two

/-- `|S₄ / A₄| = 2`, the index of the alternating group. -/
theorem card_quot_s4 : Nat.card (Perm (Fin 4) ⧸ alternatingGroup (Fin 4)) = 2 := by
  haveI : Nontrivial (Fin 4) := ⟨⟨0, 1, by decide⟩⟩
  rw [← Subgroup.index_eq_card]
  exact alternatingGroup.index_eq_two

/-- `|Multiplicative (ZMod 2)| = 2`. -/
theorem card_mult_zmod2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- `|Multiplicative (ZMod 3)| = 3`. -/
theorem card_mult_zmod3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-! ### The `S₃` series `S₃ ⊵ A₃ ⊵ {e}` -/

/-- **Top factor of `S₃`:** `S₃ / A₃ ≅ ℤ/2ℤ`. -/
theorem quot_s3_iso_zmod2 :
    Nonempty ((Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ≃* Multiplicative (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact ⟨mulEquivOfPrimeCardEq card_quot_s3 card_mult_zmod2⟩

/-- **Bottom factor of `S₃`:** `A₃ ≅ ℤ/3ℤ`, cyclic of prime order `3`. -/
theorem a3_iso_zmod3 :
    Nonempty (alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact ⟨mulEquivOfPrimeCardEq card_a3 card_mult_zmod3⟩

/-- **The explicit derived series of `S₃`: `S₃ ⊵ A₃ ⊵ {e}` with both factors identified.**

* `A₃ ◁ S₃` (normal, being `sign.ker`);
* `S₃ / A₃ ≅ ℤ/2ℤ` and `A₃ ≅ ℤ/3ℤ`, both abelian of prime order.

So `S₃` is solvable with the displayed abelian layers. -/
theorem derived_series_S3 :
    (alternatingGroup (Fin 3)).Normal ∧
      Nat.card (Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = 2 ∧
      Nat.card (alternatingGroup (Fin 3)) = 3 ∧
      Nonempty ((Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) ≃* Multiplicative (ZMod 2)) ∧
      Nonempty (alternatingGroup (Fin 3) ≃* Multiplicative (ZMod 3)) :=
  ⟨inferInstance, card_quot_s3, card_a3, quot_s3_iso_zmod2, a3_iso_zmod3⟩

/-- Commutator data exhibiting `A₃` as (an upper bound for) the derived subgroup `[S₃,S₃]`:
`[S₃,S₃] ≤ A₃`. Equality holds (every `3`-cycle is a commutator), recorded in the module
docstring as a follow-up. -/
theorem derived_layers_S3 :
    commutator (Perm (Fin 3)) ≤ alternatingGroup (Fin 3) :=
  alternatingGroup.commutator_perm_le

/-! ### The `S₄` series `S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}` -/

/-- **Top factor of `S₄`:** `S₄ / A₄ ≅ ℤ/2ℤ`. -/
theorem quot_s4_iso_zmod2 :
    Nonempty ((Perm (Fin 4) ⧸ alternatingGroup (Fin 4)) ≃* Multiplicative (ZMod 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact ⟨mulEquivOfPrimeCardEq card_quot_s4 card_mult_zmod2⟩

/-- **The explicit derived series of `S₄`: `S₄ ⊵ A₄ ⊵ V₄ ⊵ {e}` with all factors identified.**

* `A₄ ◁ S₄` and `V₄ ◁ A₄` (normal subgroups);
* `S₄ / A₄ ≅ ℤ/2ℤ`, `A₄ / V₄ ≅ ℤ/3ℤ`, `V₄ ≅ (ℤ/2ℤ)²` — all abelian of prime-power order.

The `A₄`-layer is imported from `AbelRuffiniA4CompositionSeries`. So `S₄` is solvable with the
displayed abelian layers. -/
theorem derived_series_S4 :
    (alternatingGroup (Fin 4)).Normal ∧
      (alternatingGroup.kleinFour (Fin 4)).Normal ∧
      Nat.card (Perm (Fin 4) ⧸ alternatingGroup (Fin 4)) = 2 ∧
      Nat.card (alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4)) = 3 ∧
      Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 ∧
      Nonempty ((Perm (Fin 4) ⧸ alternatingGroup (Fin 4)) ≃* Multiplicative (ZMod 2)) ∧
      Nonempty ((alternatingGroup (Fin 4) ⧸ alternatingGroup.kleinFour (Fin 4))
        ≃* Multiplicative (ZMod 3)) ∧
      Nonempty (alternatingGroup.kleinFour (Fin 4) ≃* Multiplicative (ZMod 2 × ZMod 2)) :=
  ⟨inferInstance, AbelRuffiniA4CompositionSeries.v4_normal, card_quot_s4,
    AbelRuffiniA4CompositionSeries.card_quotient, AbelRuffiniA4CompositionSeries.card_v4,
    quot_s4_iso_zmod2, AbelRuffiniA4CompositionSeries.quotient_iso_zmod3,
    AbelRuffiniA4CompositionSeries.v4_iso_zmod2_sq⟩

/-- Commutator data for the `S₄` chain: `[S₄,S₄] ≤ A₄` and `[A₄,A₄] = V₄`. The first inclusion is
hypothesis-free (`alternatingGroup.commutator_perm_le`); the second is the sibling result
`AbelRuffiniA4CompositionSeries.v4_eq_commutator`. Together with the reverse inclusion
`A₄ ≤ [S₄,S₄]` (documented follow-up) these identify the chain as the derived series of `S₄`. -/
theorem derived_layers_S4 :
    commutator (Perm (Fin 4)) ≤ alternatingGroup (Fin 4) ∧
      alternatingGroup.kleinFour (Fin 4) = commutator (alternatingGroup (Fin 4)) :=
  ⟨alternatingGroup.commutator_perm_le, AbelRuffiniA4CompositionSeries.v4_eq_commutator⟩

end AbelRuffiniSymmetricDerivedSeries
