/-
Finite Group Exponent: g ^ |G| = 1 for Every Element

Source: Open question from lagrange-theorem gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

In any finite group G, every element g satisfies g ^ |G| = 1: raising an
element to the power equal to the group's order returns the identity. This is
the immediate corollary of Lagrange's theorem -- the order of g divides |G| --
and it is the structural root of the two classical number-theoretic
congruences:

  Chain:  Lagrange (orderOf g ∣ |G|)
            → g ^ |G| = 1            (finite group exponent)
            → exponent G ∣ |G|       (the exponent is a divisor of the order)
            → Euler's theorem        (apply to the unit group (ZMod n)ˣ)
            → Fermat's little theorem (the prime special case φ(p) = p − 1)

Mathlib provides `pow_card_eq_one` directly. The value of this entry is the
explicit derivation from Lagrange and the descent to Euler's and Fermat's
theorems, which are *exactly* this theorem applied to the unit group (ZMod n)ˣ
whose order is the totient φ(n).
-/

import Mathlib

open scoped Nat

namespace FiniteGroupExponent

variable {G : Type*} [Group G] [Fintype G]

/-! ## Part I: The core theorem — g ^ |G| = 1

Lagrange's theorem says the order of any element divides the group order
(`orderOf_dvd_card`). Combined with `orderOf_dvd_iff_pow_eq_one`, this gives
`g ^ |G| = 1` directly. -/

/-- Lagrange for elements: the order of `g` divides `|G|`. The order of `g` is
the cardinality of the cyclic subgroup it generates, so this is Lagrange's
theorem specialised to cyclic subgroups. -/
theorem orderOf_dvd_groupCard (g : G) : orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card

/-- **Finite group exponent.** Every element raised to the group order is the
identity, derived explicitly from Lagrange (`orderOf_dvd_card`) via
`orderOf_dvd_iff_pow_eq_one`. -/
theorem pow_card_eq_one_of_lagrange (g : G) : g ^ Fintype.card G = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp orderOf_dvd_card

/-- Our Lagrange-derived statement agrees with Mathlib's library lemma
`pow_card_eq_one`. -/
theorem pow_card_eq_one_agrees (g : G) :
    pow_card_eq_one_of_lagrange g = pow_card_eq_one := rfl

/-- `Nat.card` form. Note this holds for *any* group with no finiteness
hypothesis: if `G` is infinite then `Nat.card G = 0` and `g ^ 0 = 1`
vacuously. -/
theorem pow_natCard_eq_one {H : Type*} [Group H] (g : H) :
    g ^ Nat.card H = 1 :=
  pow_card_eq_one'

/-! ## Part II: The group exponent divides the order

The exponent of `G` is the *least* `N > 0` with `g ^ N = 1` for all `g`
(`Monoid.exponent`). Part I shows `|G|` is one such common period, so the
exponent — being the minimum — divides `|G|`. -/

/-- The group order is a common period for every element. This is the property
the exponent is the least positive instance of. -/
theorem card_is_common_period : ∀ g : G, g ^ Fintype.card G = 1 :=
  fun g => pow_card_eq_one_of_lagrange g

/-- The exponent of a finite group divides its order. -/
theorem exponent_dvd_card : Monoid.exponent G ∣ Fintype.card G :=
  Group.exponent_dvd_card

/-- Repackaged via the universal property of the exponent: `|G|` annihilates
every element, hence the exponent divides it. This makes the logical content of
`Group.exponent_dvd_card` explicit. -/
theorem exponent_dvd_card_via_universal :
    Monoid.exponent G ∣ Fintype.card G :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr card_is_common_period

/-! ## Part III: Euler's and Fermat's theorems as corollaries

Euler's theorem is *exactly* the finite-group exponent theorem applied to the
unit group `(ZMod n)ˣ`, whose order is Euler's totient `φ(n)`
(`ZMod.card_units_eq_totient`). Fermat's little theorem is the prime special
case `φ(p) = p − 1`. -/

/-- **Euler's theorem.** For `x` a unit of `ZMod n`, `x ^ φ(n) = 1`. Derived
from the finite-group exponent theorem applied to `(ZMod n)ˣ` together with
`|(ZMod n)ˣ| = φ(n)`. -/
theorem euler_from_exponent (n : ℕ) [NeZero n] (x : (ZMod n)ˣ) :
    x ^ Nat.totient n = 1 := by
  rw [← ZMod.card_units_eq_totient n]
  exact pow_card_eq_one

/-- **Fermat's little theorem** (unit-group form). For prime `p`, every unit of
`ZMod p` satisfies `x ^ (p − 1) = 1`. This is Euler's theorem specialised to
`φ(p) = p − 1`. -/
theorem fermat_units (p : ℕ) [Fact p.Prime] (x : (ZMod p)ˣ) :
    x ^ (p - 1) = 1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := euler_from_exponent p x
  rwa [Nat.totient_prime Fact.out] at h

/-- **Fermat's little theorem** (field form, concrete capstone). For prime `p`
and `a ≠ 0` in `ZMod p`, `a ^ (p − 1) = 1`. Mathlib derives this directly from
the same circle of ideas (`ZMod.pow_card_sub_one_eq_one`). -/
theorem fermat_zmod (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 :=
  ZMod.pow_card_sub_one_eq_one ha

/-! ## Part IV: The chain, end to end

A single statement tying the foundation (Lagrange divisibility) to the apex
corollary (Euler), to make the dependency chain explicit. -/

/-- The complete chain: Lagrange's element-order divisibility implies the
finite-group exponent identity, which specialises on `(ZMod n)ˣ` to Euler's
theorem. -/
theorem chain_lagrange_to_euler (n : ℕ) [NeZero n] (x : (ZMod n)ˣ) :
    (orderOf x ∣ Fintype.card (ZMod n)ˣ) ∧ x ^ Nat.totient n = 1 :=
  ⟨orderOf_dvd_card, euler_from_exponent n x⟩

end FiniteGroupExponent
