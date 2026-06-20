import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The unit-group Chinese Remainder isomorphism `(ZMod (mn))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`

**Open Question (`chinese-remainder-constructive-oq-05`)**: give the *structural*
form of the Chinese Remainder Theorem — not just the existential solver of the
earlier siblings, but the canonical isomorphism witnessing the decomposition.

The sibling `ChineseRemainderConstructiveOQ04OQ02` already bridges the existential
solver to Mathlib's **ring** isomorphism `ZMod.chineseRemainder h : ZMod (m*n) ≃+*
ZMod m × ZMod n`.  This file develops the next structural layer, which Mathlib
does **not** package as a named object: the induced **multiplicative-group**
isomorphism on units,

  `unitsChineseRemainder h : (ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.

Mathlib uses this equivalence only *inline*, anonymously, inside the proof of
`Nat.totient_mul` (`Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv` composed
with `MulEquiv.prodUnits`).  Here it is exposed as a first-class `MulEquiv`,
characterised by the reduction map (`unitsChineseRemainder_coe`), with the
order-multiplicativity corollary stated at the level of the **unit groups
themselves** —

  `card_units_mul h : Nat.card (ZMod (m*n))ˣ = Nat.card (ZMod m)ˣ * Nat.card (ZMod n)ˣ`

— deliberately *not* in terms of Euler's totient (that multiplicativity,
`Nat.totient_mul`, lives in the `euler-totient` family); this entry isolates the
group-theoretic content that underlies it.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace ChineseRemainderConstructiveOQ05

/-- **The unit-group Chinese Remainder isomorphism.**  For coprime `m, n`, the
group of units of `ZMod (m*n)` is canonically isomorphic to the product of the
unit groups, `(ZMod (m*n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ`.  It is the units functor
applied to the ring isomorphism `ZMod.chineseRemainder`, followed by the
splitting of units of a product, `MulEquiv.prodUnits`. -/
def unitsChineseRemainder {m n : ℕ} (h : Nat.Coprime m n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- **Characterisation by the reduction map.**  The unit isomorphism is the
underlying ring CRT map: the pair of residues of a unit `u` under reduction
mod `m` and mod `n` is exactly `ZMod.chineseRemainder h` applied to `u`. -/
theorem unitsChineseRemainder_coe {m n : ℕ} (h : Nat.Coprime m n)
    (u : (ZMod (m * n))ˣ) :
    (((unitsChineseRemainder h u).1 : ZMod m), ((unitsChineseRemainder h u).2 : ZMod n))
      = ZMod.chineseRemainder h (u : ZMod (m * n)) :=
  rfl

/-- The inverse sends a pair of units back to the unit reconstructed by the
inverse ring CRT map (`ZMod.chineseRemainder h |>.symm`). -/
theorem unitsChineseRemainder_symm_coe {m n : ℕ} (h : Nat.Coprime m n)
    (p : (ZMod m)ˣ × (ZMod n)ˣ) :
    (((unitsChineseRemainder h).symm p : ZMod (m * n)))
      = (ZMod.chineseRemainder h).symm ((p.1 : ZMod m), (p.2 : ZMod n)) :=
  rfl

/-- **Multiplicativity of the unit-group order under CRT.**  For coprime `m, n`,
`|（ZMod (m*n))ˣ| = |(ZMod m)ˣ| · |(ZMod n)ˣ|`.  This is the group-theoretic
content behind the multiplicativity of Euler's totient, stated purely in terms of
the unit groups via the isomorphism `unitsChineseRemainder`. -/
theorem card_units_mul {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.card (ZMod (m * n))ˣ = Nat.card (ZMod m)ˣ * Nat.card (ZMod n)ˣ := by
  rw [Nat.card_congr (unitsChineseRemainder h).toEquiv, Nat.card_prod]

/-- A unit of `ZMod (m*n)` is trivial iff both of its CRT components are trivial
(an immediate consequence of the isomorphism being injective). -/
theorem unitsChineseRemainder_eq_one_iff {m n : ℕ} (h : Nat.Coprime m n)
    (u : (ZMod (m * n))ˣ) :
    unitsChineseRemainder h u = 1 ↔ u = 1 := by
  rw [← map_one (unitsChineseRemainder h), (unitsChineseRemainder h).apply_eq_iff_eq]

end ChineseRemainderConstructiveOQ05
