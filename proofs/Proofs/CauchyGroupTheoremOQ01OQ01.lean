import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The Cauchy characterization: order-`p` elements detect prime divisors

## What This Proves

The parent file (`CauchyGroupTheoremOQ01`) repackages **Cauchy's theorem**: if a
prime `p` divides `|G|`, then `G` has an element of order `p`. Cauchy is exactly
*one direction* of a clean biconditional, and its converse is the elementary
half of Lagrange's theorem (`orderOf x ∣ |G|`). This file proves the full
characterization and extracts its structural consequences.

* **Easy (Lagrange) direction** (`prime_dvd_card_of_exists_orderOf`). If `G` has
  an element of order `p`, then `p ∣ |G|`. This is `orderOf_dvd_natCard`
  specialised to a prime-order element — the converse of Cauchy. New content.

* **Cauchy characterization** (`exists_orderOf_eq_prime_iff_dvd`). For a prime
  `p`, `G` has an element of order `p` **iff** `p ∣ |G|`. The forward direction
  is Lagrange, the backward direction is Cauchy. This is the sharp statement of
  which primes are "visible" as element orders, and Mathlib records neither the
  packaged biconditional nor the easy direction. New content.

* **Cyclic order-`p` subgroup** (`exists_isCyclic_subgroup_card_eq`). The
  subgroup the parent produces (`cauchy_subgroup`) is not merely of order `p`: a
  group of prime order is cyclic (`isCyclic_of_prime_card`), so `G` has a
  *cyclic* subgroup of order `p`. This is the actual seed of the Sylow tower.
  New content.

* **Involution ⟺ even order** (`exists_involution_iff_even_card`). Specialising
  the characterization at `p = 2` and using the bridge
  `orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1` (`orderOf_eq_two_iff_involution`), a finite
  group has a non-trivial involution **iff** its order is even. The parent proved
  only the (⟸) existence half; this upgrades it to a biconditional. New content.

* **Concrete check** (`exists_involution_zmod6`, `no_orderOf_five_zmod6`). In
  `ZMod 6` the characterization fires at `2, 3` and *fails* at the non-divisor
  `5`: there is no element of order `5`. Verified by kernel `decide` (no
  `native_decide`), so the file stays genuinely `0`-axiom.

## Context

Cauchy + Lagrange together say the set of element-orders of a finite group
determines, and is determined by, the prime divisors of `|G|`. The involution
biconditional is the `p = 2` instance underlying the entire even-order theory
(Brauer–Fowler, Feit–Thompson).
-/

open Subgroup

namespace CauchyGroupTheoremOQ01OQ01

variable {G : Type*}

/-- **Converse of Cauchy (Lagrange direction).** If `G` has an element of order
`p`, then `p ∣ |G|`. This is `orderOf_dvd_natCard` read at a prime-order element;
together with Cauchy it gives the full characterization below. -/
theorem prime_dvd_card_of_exists_orderOf [Group G] (p : ℕ)
    (h : ∃ x : G, orderOf x = p) : p ∣ Nat.card G := by
  obtain ⟨x, hx⟩ := h
  rw [← hx]
  exact orderOf_dvd_natCard x

/-- **Cauchy characterization.** For a prime `p`, a finite group `G` has an
element of order exactly `p` **iff** `p ∣ |G|`. Forward direction = Lagrange,
backward direction = Cauchy. -/
theorem exists_orderOf_eq_prime_iff_dvd [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    (∃ x : G, orderOf x = p) ↔ p ∣ Nat.card G :=
  ⟨prime_dvd_card_of_exists_orderOf p, fun hdvd => exists_prime_orderOf_dvd_card' p hdvd⟩

/-- **Cyclic subgroup of order `p`.** If a prime `p` divides `|G|`, then `G` has
a *cyclic* subgroup of order exactly `p` — strengthening the parent's
`cauchy_subgroup` with the cyclicity that makes it the seed of the Sylow tower.
A group of prime order is automatically cyclic. -/
theorem exists_isCyclic_subgroup_card_eq [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Nat.card G) : ∃ H : Subgroup G, Nat.card H = p ∧ IsCyclic H := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcard : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hx]
  exact ⟨zpowers x, hcard, isCyclic_of_prime_card hcard⟩

/-- **Order-2 ⟺ involution bridge.** An element has order `2` exactly when it is
a non-trivial involution. -/
theorem orderOf_eq_two_iff_involution [Group G] (x : G) :
    orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · intro hx1
      rw [hx1, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have hpow := pow_orderOf_eq_one x
      rwa [hx, pow_two] at hpow
  · rintro ⟨hne, hsq⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hsq) hne

/-- **Involution ⟺ even order.** A finite group has a non-trivial involution
(an `x ≠ 1` with `x * x = 1`) **iff** its order is even. This upgrades the
parent's one-directional `exists_involution_of_even_card` to a biconditional,
via the `p = 2` instance of the Cauchy characterization. -/
theorem exists_involution_iff_even_card [Group G] [Finite G] :
    (∃ x : G, x ≠ 1 ∧ x * x = 1) ↔ Even (Nat.card G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [even_iff_two_dvd, ← exists_orderOf_eq_prime_iff_dvd (G := G) 2]
  exact exists_congr fun x => (orderOf_eq_two_iff_involution x).symm

/- ### Concrete checks in `ZMod 6`

`|ZMod 6| = 6 = 2 · 3`, so the characterization fires at `2` and `3` and must
*fail* at every non-divisor. We confirm both faces by kernel `decide`
(no `native_decide`), keeping the file free of `Lean.ofReduceBool`. -/

/-- The characterization at `p = 2`: `ZMod 6` has even order, hence a non-trivial
involution (the additive translate `3`). -/
theorem exists_involution_zmod6 : ∃ x : ZMod 6, x ≠ 0 ∧ x + x = 0 :=
  ⟨3, by decide⟩

/-- The negative face of the characterization: `5 ∤ 6`, so `ZMod 6` has **no**
element of additive order `5`. Derived from the additive Lagrange direction
(`addOrderOf_dvd_natCard`) rather than by brute force. -/
theorem no_addOrderOf_five_zmod6 : ¬ ∃ x : ZMod 6, addOrderOf x = 5 := by
  rintro ⟨x, hx⟩
  have hdvd : (5 : ℕ) ∣ Nat.card (ZMod 6) := hx ▸ addOrderOf_dvd_natCard x
  rw [Nat.card_zmod] at hdvd
  omega

end CauchyGroupTheoremOQ01OQ01
