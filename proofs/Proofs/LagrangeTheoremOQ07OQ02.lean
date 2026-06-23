/-
Additive Finite Group Annihilation: n • x = 0 for Every Element of an Order-n Group

Source: Open question oq-02 of lagrange-theorem-oq-07 (gallery)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry proves the multiplicative finite-group exponent theorem
`g ^ |G| = 1` for every element of a finite group, derived from Lagrange's
theorem. The open question asks whether the *same exponent-divides-order
argument* formalises cleanly for the additive structure, recovering

  n • x = 0   for every element x of a finite (abelian) group of order n.

This file answers it. The argument is literally the additive image of the
parent's chain under Mathlib's `to_additive`:

  Lagrange (addOrderOf x ∣ |G|)
    → |G| • x = 0                     (additive annihilation)
    → AddMonoid.exponent G ∣ |G|      (the additive exponent divides the order)
    → n • x = 0 in ZMod n             (the canonical order-n abelian group)

Mathlib provides the headline lemma `card_nsmul_eq_zero` directly. The value of
this entry, mirroring the parent, is (i) the explicit derivation from additive
Lagrange (`addOrderOf_dvd_card`), (ii) the additive exponent descent, (iii) the
concrete recovery `n • x = 0` in `ZMod n` with `AddMonoid.exponent (ZMod n) = n`,
and (iv) a structural bridge proving the additive theorem *is* the parent's
multiplicative theorem transported through `Multiplicative`, making the
"same argument" claim of the open question literal rather than rhetorical.
-/

import Mathlib

open scoped Nat

namespace AdditiveFiniteGroupAnnihilation

variable {G : Type*} [AddGroup G] [Fintype G]

/-! ## Part I: The core theorem — `|G| • x = 0`

Additive Lagrange (`addOrderOf_dvd_card`) says the additive order of any element
divides the group order. Combined with `addOrderOf_dvd_iff_nsmul_eq_zero` this
gives `|G| • x = 0` directly — the exact additive image of the parent's
`pow_card_eq_one_of_lagrange`. -/

/-- Additive Lagrange for elements: the additive order of `g` divides `|G|`. This
is the `to_additive` image of `orderOf_dvd_card`. -/
theorem addOrderOf_dvd_groupCard (g : G) : addOrderOf g ∣ Fintype.card G :=
  addOrderOf_dvd_card

/-- **Additive finite-group annihilation.** Acting by the group order kills every
element, derived explicitly from additive Lagrange (`addOrderOf_dvd_card`) via
`addOrderOf_dvd_iff_nsmul_eq_zero`. -/
theorem card_nsmul_eq_zero_of_lagrange (g : G) : Fintype.card G • g = 0 :=
  addOrderOf_dvd_iff_nsmul_eq_zero.mp addOrderOf_dvd_card

/-- Our Lagrange-derived statement agrees with Mathlib's library lemma
`card_nsmul_eq_zero`. -/
theorem card_nsmul_eq_zero_agrees (g : G) :
    card_nsmul_eq_zero_of_lagrange g = card_nsmul_eq_zero := rfl

/-- `Nat.card` form. This holds for *any* additive group with no finiteness
hypothesis: if `G` is infinite then `Nat.card G = 0` and `0 • g = 0`
vacuously. The additive image of the parent's `pow_natCard_eq_one`. -/
theorem nsmul_natCard_eq_zero {H : Type*} [AddGroup H] (g : H) :
    Nat.card H • g = 0 :=
  card_nsmul_eq_zero'

/-! ## Part II: The additive exponent divides the order

The additive exponent of `G` is the least `N > 0` with `N • g = 0` for all `g`
(`AddMonoid.exponent`). Part I shows `|G|` is one such common period, so the
exponent — being the minimum — divides `|G|`. Additive image of the parent's
Part II. -/

/-- The group order is a common period for every element. This is the property
the additive exponent is the least positive instance of. -/
theorem card_is_common_period : ∀ g : G, Fintype.card G • g = 0 :=
  fun g => card_nsmul_eq_zero_of_lagrange g

/-- The additive exponent of a finite additive group divides its order. -/
theorem addExponent_dvd_card : AddMonoid.exponent G ∣ Fintype.card G :=
  AddGroup.exponent_dvd_card

/-- Repackaged via the universal property of the additive exponent: `|G|`
annihilates every element, hence the exponent divides it. This makes the logical
content of `AddGroup.exponent_dvd_card` explicit. -/
theorem addExponent_dvd_card_via_universal :
    AddMonoid.exponent G ∣ Fintype.card G :=
  AddMonoid.exponent_dvd_iff_forall_nsmul_eq_zero.mpr card_is_common_period

/-! ## Part III: The concrete order-`n` abelian group `ZMod n`

`ZMod n` is the canonical abelian group of order `n`. Specialising Part I gives
the recovery asked for by the open question, `n • x = 0`, and the additive
exponent is *exactly* `n` (sharp, since `1` has additive order `n`). -/

/-- **The recovery.** In the order-`n` group `ZMod n`, scaling any element by `n`
yields `0`. This is `card_nsmul_eq_zero` together with `|ZMod n| = n`. -/
theorem zmod_nsmul_eq_zero (n : ℕ) [NeZero n] (x : ZMod n) : n • x = 0 := by
  have h : Fintype.card (ZMod n) • x = 0 := card_nsmul_eq_zero_of_lagrange x
  rwa [ZMod.card] at h

/-- The additive exponent of `ZMod n` is exactly `n`: it divides `n` by Part II,
and `n = addOrderOf (1 : ZMod n)` divides it since the exponent annihilates `1`.
So the bound `exponent ∣ card` of Part II is sharp for cyclic groups. -/
theorem addExponent_zmod (n : ℕ) [NeZero n] : AddMonoid.exponent (ZMod n) = n := by
  refine Nat.dvd_antisymm ?_ ?_
  · have h : AddMonoid.exponent (ZMod n) ∣ Fintype.card (ZMod n) :=
      addExponent_dvd_card
    rwa [ZMod.card] at h
  · have h : addOrderOf (1 : ZMod n) ∣ AddMonoid.exponent (ZMod n) :=
      AddMonoid.addOrder_dvd_exponent (1 : ZMod n)
    rwa [ZMod.addOrderOf_one] at h

/-- The same recovery stated for an arbitrary finite additive *commutative* group
of order `n`, matching the open question's phrasing literally (commutativity is
not actually needed — see `card_nsmul_eq_zero_of_lagrange`). -/
theorem comm_card_nsmul_eq_zero {A : Type*} [AddCommGroup A] [Fintype A]
    (n : ℕ) (hn : Fintype.card A = n) (x : A) : n • x = 0 := by
  rw [← hn]; exact card_nsmul_eq_zero_of_lagrange x

/-! ## Part IV: Structural bridge — the additive theorem *is* the parent's

The open question asks whether "the same exponent-divides-order argument"
transfers. It does so literally: the additive annihilation theorem is the
parent's multiplicative `pow_card_eq_one`, read on the type tag `Multiplicative G`
through `Multiplicative.ofAdd` (which sends `n • g` to `(ofAdd g) ^ n` and `0`
to `1`). This reproves Part I *without* re-invoking Lagrange — it transports the
parent's conclusion instead. -/

/-- The additive annihilation theorem obtained by transporting the parent's
multiplicative `pow_card_eq_one` through `Multiplicative`. Demonstrates that the
two theorems are one and the same under `to_additive`. -/
theorem card_nsmul_eq_zero_via_multiplicative (g : G) :
    Fintype.card G • g = 0 := by
  -- The parent's theorem on the type tag `Multiplicative G`.
  have h : (Multiplicative.ofAdd g) ^ Fintype.card (Multiplicative G) = 1 :=
    pow_card_eq_one
  rw [Fintype.card_multiplicative, ← ofAdd_nsmul] at h
  -- h : Multiplicative.ofAdd (Fintype.card G • g) = 1
  have h0 : Multiplicative.ofAdd (Fintype.card G • g) = Multiplicative.ofAdd (0 : G) := by
    rw [h, ofAdd_zero]
  exact Multiplicative.ofAdd.injective h0

/-! ## Part V: The chain, end to end

A single statement tying additive Lagrange (the foundation) to the concrete
order-`n` recovery in `ZMod n` (the apex), paralleling the parent's
`chain_lagrange_to_euler`. -/

/-- The complete additive chain: Lagrange's element-order divisibility implies the
annihilation identity, which specialises on `ZMod n` to `n • x = 0`. -/
theorem chain_lagrange_to_zmod (n : ℕ) [NeZero n] (x : ZMod n) :
    (addOrderOf x ∣ Fintype.card (ZMod n)) ∧ n • x = 0 :=
  ⟨addOrderOf_dvd_card, zmod_nsmul_eq_zero n x⟩

end AdditiveFiniteGroupAnnihilation
