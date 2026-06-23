import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# Burnside Counting, OQ-04-OQ-01: Axiom-free binary bracelets of length 4

## What This Proves

The parent entry `burnside-counting` and its dihedral extension `burnside-counting-oq-04`
establish that there are exactly `6` binary **bracelets** of length 4 (orbits of the
2-colourings of a square under the full dihedral symmetry group `D_4` of rotations *and*
reflections).  Both close the final numeric count with `native_decide`, which trusts the
Lean compiler and therefore depends on the `Lean.ofReduceBool` axiom.

This file removes that dependency.  We build a *concrete* action of `DihedralGroup 4` on the
positions `ZMod 4` of the square (rotation `r i : x ↦ x + i`, reflection `sr i : x ↦ -x - i`),
lift it to the `16` colourings `Coloring = ZMod 4 → Fin 2` via the standard arrow action
`(g • c) x = c (g⁻¹ • x)`, and count the orbits with Mathlib's Burnside lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`.

The single computational step — the total number of colourings fixed across all `8` group
elements equals `48` — is discharged by ordinary kernel `decide` (the carrier has only `16`
elements, so the enumeration is small), **not** `native_decide`.  Burnside then forces the
orbit count:

  `48 = (#orbits) · 8`,  so  `#orbits = 6`.

So `|bracelets(4,2)| = 6` is genuinely verified: `#print axioms bracelet_count_4_2`
lists only `propext`, `Classical.choice`, `Quot.sound` — no `Lean.ofReduceBool`.

## Why this matters

It upgrades a headline combinatorial count from *axiomatized* (via `native_decide`) to
*verified*, and it exhibits a reusable, fully kernel-checked pattern: define a concrete finite
group action, lift it to colourings by the arrow action, and discharge Burnside's
fixed-point side by `decide`.

## Mathlib Dependencies
- `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` : Burnside's lemma
- `arrowAction` : the action of `G` on `A → B` induced by an action on `A`
- `Mathlib.GroupTheory.SpecificGroups.Dihedral` : `DihedralGroup n`, `DihedralGroup.card`
-/

namespace BurnsideCountingOQ04OQ01

open MulAction Finset

/-- The `16` two-colourings of the four positions of a square.
`ZMod 4` is definitionally `Fin 4`, so this is the parent's `Coloring 4 2 = Fin 4 → Fin 2`. -/
abbrev Coloring := ZMod 4 → Fin 2

/-! ## Part I: A concrete `D₄` action on the positions of the square -/

/-- The geometric action of the dihedral group on the four positions `ZMod 4`:
a rotation `r i` sends `x ↦ x + i`, a reflection `sr i` sends `x ↦ -x - i`.
These formulas make the map `D₄ → (ZMod 4 → ZMod 4)` a genuine group homomorphism
(verified by `decide` in `posMulAction`). -/
def posAct : DihedralGroup 4 → ZMod 4 → ZMod 4
  | .r i, x => x + i
  | .sr i, x => -x - i

/-- `DihedralGroup 4` acts on the positions `ZMod 4` by `posAct`.
Both action laws are finite identities, discharged by kernel `decide`. -/
instance posMulAction : MulAction (DihedralGroup 4) (ZMod 4) where
  smul := posAct
  one_smul := by decide
  mul_smul := by decide

@[simp] lemma posAct_r (i x : ZMod 4) : (DihedralGroup.r i) • x = x + i := rfl
@[simp] lemma posAct_sr (i x : ZMod 4) : (DihedralGroup.sr i) • x = -x - i := rfl

/-! ## Part II: Lift to colourings by the arrow action -/

/-- The induced action of `D₄` on colourings: `(g • c) x = c (g⁻¹ • x)`.
This is Mathlib's `arrowAction`, available because `D₄` is a group acting on `ZMod 4`. -/
instance colMulAction : MulAction (DihedralGroup 4) Coloring := arrowAction

/-- A colouring is fixed by `g` iff `g • c = c`; this is decidable because colourings have
decidable equality, hence each fixed-point set is a `Fintype`. -/
instance fixedByDecidablePred (g : DihedralGroup 4) :
    DecidablePred (· ∈ fixedBy Coloring g) :=
  fun c => decidable_of_iff (g • c = c) mem_fixedBy.symm

/-- The orbit quotient of the (finite) colouring set is finite. We only need *some* `Fintype`
instance for Burnside's lemma — the orbit count it computes is independent of the choice. -/
noncomputable instance : Fintype (orbitRel.Quotient (DihedralGroup 4) Coloring) :=
  Fintype.ofFinite _

/-! ## Part III: The bracelet count via Burnside's lemma -/

/-- The total number of `(g, c)` with `g • c = c`, summed over the eight elements of `D₄`,
equals `48`.  Concretely the eight fixed-point counts are
`16, 2, 4, 2` for the rotations `r 0, r 1, r 2, r 3` and `8, 4, 8, 4` for the reflections
`sr 0, sr 1, sr 2, sr 3`, totalling `48`.  The carrier `ZMod 4 → Fin 2` has only `16`
elements, so this finite enumeration is checked by ordinary kernel `decide`. -/
theorem sum_fixedBy_eq :
    (∑ g : DihedralGroup 4, Fintype.card (fixedBy Coloring g)) = 48 := by
  decide

/-- **Binary bracelets of length 4.**
There are exactly `6` orbits of the `16` two-colourings of a square under the full dihedral
group `D₄`.  Proved from Burnside's lemma and the kernel-checked fixed-point total `48`:
`#orbits · |D₄| = 48` and `|D₄| = 8`, so `#orbits = 6`.

Unlike the parent's `native_decide` count, this proof is `Lean.ofReduceBool`-free. -/
theorem bracelet_count_4_2 :
    Fintype.card (orbitRel.Quotient (DihedralGroup 4) Coloring) = 6 := by
  have key := sum_card_fixedBy_eq_card_orbits_mul_card_group (DihedralGroup 4) Coloring
  rw [sum_fixedBy_eq] at key
  -- Burnside's lemma states its orbit side with the spelling `Quotient (orbitRel …)` and its own
  -- synthesised `Fintype` instance, whereas the goal uses the API name `orbitRel.Quotient …`.
  -- These are definitionally equal but *syntactically* distinct, so we move both sides to the
  -- instance-independent `Nat.card` and reconcile the two spellings with a `rfl` bridge before
  -- reading off the count.
  simp only [← Nat.card_eq_fintype_card] at key ⊢
  have hsp : Nat.card (orbitRel.Quotient (DihedralGroup 4) Coloring)
           = Nat.card (Quotient (orbitRel (DihedralGroup 4) Coloring)) := rfl
  have hG : Nat.card (DihedralGroup 4) = 8 := by
    rw [Nat.card_eq_fintype_card]; exact DihedralGroup.card
  rw [hsp]
  rw [hG] at key
  -- `key : 48 = Nat.card (Quotient (orbitRel …)) * 8`,  goal : `Nat.card (Quotient (orbitRel …)) = 6`
  omega

-- Axiom audit: confirms the count is `Lean.ofReduceBool`-free (kernel `decide`, not
-- `native_decide`); only the standard foundational axioms appear.
#print axioms bracelet_count_4_2

end BurnsideCountingOQ04OQ01
