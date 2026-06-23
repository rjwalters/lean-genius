import Mathlib

/-
# Carmichael's Function is Multiplicative: λ(m·n) = lcm(λ(m), λ(n)) for coprime m, n

## Open Question (euler-totient-oq-01-oq-01)

Strengthen `carmichael_dvd_totient` (parent: `EulerTotientOQ01.lean`) toward the
full structural characterization
  λ(n) = lcm of the cyclic-factor orders of (ℤ/nℤ)*.

The keystone is **multiplicativity over coprime factors**:
  λ(m·n) = lcm(λ(m), λ(n))     whenever gcd(m, n) = 1.

Iterating this over the prime-power factorization n = ∏ pᵢ^kᵢ yields
  λ(n) = lcm_i λ(pᵢ^kᵢ),
and since each (ℤ/pᵏℤ)* is cyclic (p odd) or a product of cyclic groups (p = 2),
this is exactly "λ(n) = lcm of cyclic group orders".  This file proves the
keystone; the factorization corollary is left as a routine induction (see the
`Next Steps` note in `research/problems/.../knowledge.md`).

## Proof

λ(n) is defined as the group-theoretic exponent of the unit group (ℤ/nℤ)*.
For coprime m, n the Chinese Remainder ring isomorphism
  ZMod (m·n) ≃+* ZMod m × ZMod n
induces a multiplicative isomorphism on unit groups
  (ℤ/mnℤ)* ≃* (ℤ/mℤ)* × (ℤ/nℤ)*.
The exponent is invariant under multiplicative isomorphism
(`Monoid.exponent_eq_of_mulEquiv`), and the exponent of a product is the lcm of
the exponents (`Monoid.exponent_prod`), giving the result.

## Honesty note

This is routine given current Mathlib (`Monoid.exponent_prod`,
`ZMod.chineseRemainder`, `Units.mapEquiv`, `MulEquiv.prodUnits`).  The unit-group
splitting used here is the same composition Mathlib uses in
`RingTheory/ZMod/UnitsCyclic.lean`.  The contribution is the explicit
Carmichael-function statement for the gallery, not new mathematics.
-/

namespace CarmichaelMultiplicative

open ZMod

/-- Carmichael's function λ(n): the exponent of the unit group (ℤ/nℤ)*.
    (Same definition as `CarmichaelFunction.carmichael` in the parent file;
    redefined here so this file is build-independent of the parent.) -/
noncomputable def carmichael (n : ℕ) : ℕ :=
  Monoid.exponent (ZMod n)ˣ

/-- For coprime m, n, the unit group of `ZMod (m * n)` splits multiplicatively as
    the product of the unit groups of `ZMod m` and `ZMod n`.  This is the
    Chinese-Remainder ring isomorphism transported to units, then split with
    `MulEquiv.prodUnits`. -/
noncomputable def unitsChineseRemainder {m n : ℕ} (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- **Multiplicativity of Carmichael's function.**
    For coprime `m`, `n`: λ(m·n) = lcm(λ(m), λ(n)). -/
theorem carmichael_mul_coprime {m n : ℕ} (h : m.Coprime n) :
    carmichael (m * n) = Nat.lcm (carmichael m) (carmichael n) := by
  unfold carmichael
  rw [Monoid.exponent_eq_of_mulEquiv (unitsChineseRemainder h),
      Monoid.exponent_prod, lcm_eq_nat_lcm]

/-- Every unit's order divides λ(n): the universal-exponent property, restated
    for the Carmichael function.  Combined with `carmichael_mul_coprime`, this
    gives that λ(n) is a common multiple of all element orders in each factor. -/
theorem order_dvd_carmichael (n : ℕ) (a : (ZMod n)ˣ) :
    orderOf a ∣ carmichael n := by
  unfold carmichael
  exact Monoid.order_dvd_exponent a

end CarmichaelMultiplicative
