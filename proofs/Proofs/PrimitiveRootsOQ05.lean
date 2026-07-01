import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Lifting a Primitive Root from `p` to `p²` (the Hensel step)

## What This Proves

Let `p` be an odd prime and let `u ∈ (ℤ/p²ℤ)ˣ` be a unit whose reduction mod `p`
is a **primitive root** modulo `p` (i.e. a generator of the cyclic group `(ℤ/pℤ)ˣ`,
equivalently an element of order `p − 1`). The classical *Hensel step* for primitive
roots asks: **which lifts of a primitive root mod `p` are primitive roots mod `p²`?**

The complete answer is a clean order dichotomy. Writing `φ(p²) = p(p−1)` for the order
of `(ℤ/p²ℤ)ˣ`, any lift `u` of a primitive root has multiplicative order **either**
`p − 1` **or** `p(p−1)`, and:

> `u` is a primitive root mod `p²`  ⇔  `orderOf u = p(p−1)`  ⇔  `u^(p−1) ≠ 1 (mod p²)`.

This is the sharp criterion (`primitiveRoot_psq_iff`): among the `p` lifts of a fixed
primitive root `g` mod `p`, the ones that fail are exactly those with `u^(p−1) = 1`.

We also prove existence (`exists_primitiveRoot_psq`): a primitive root mod `p²` exists
and its reduction is a primitive root mod `p`, so the lifting is always realizable.

## Why this is not already `Mathlib`

`Mathlib` proves the *abstract* statement that `(ℤ/p^nℤ)ˣ` is cyclic
(`isCyclic_units_of_prime_pow`) via the order of `1 + p` in the kernel of reduction,
but it does **not** package the classical *explicit* lifting criterion relating the
order of a lift mod `p²` to the single congruence `u^(p−1) ≠ 1`. That criterion — the
practical content of the Hensel step, telling you *which* lifts generate — is the
subject of this file.

## Approach

The engine is the reduction homomorphism `red : (ℤ/p²ℤ)ˣ →* (ℤ/pℤ)ˣ` (`ZMod.unitsMap`).
The whole dichotomy is elementary divisibility:

* `orderOf (red u) ∣ orderOf u`  (any hom shrinks orders), so if `red u` is a
  primitive root then `(p − 1) ∣ orderOf u`.
* `orderOf u ∣ |(ℤ/p²ℤ)ˣ| = p(p − 1)`.
* Since `p` is prime, a multiple of `p − 1` dividing `p(p − 1)` is `p − 1` or `p(p − 1)`.

No kernel computation is needed for the criterion; existence uses Mathlib's cyclicity.

## Status
- [x] Complete proof, no sorries, no extra axioms.
- [x] Criterion `primitiveRoot_psq_iff` and existence `exists_primitiveRoot_psq`.
-/

namespace PrimitiveRootsOQ05

open scoped Classical

variable {p : ℕ}

/-- The reduction homomorphism `(ℤ/p²ℤ)ˣ →* (ℤ/pℤ)ˣ`. -/
def red (p : ℕ) : (ZMod (p ^ 2))ˣ →* (ZMod p)ˣ :=
  ZMod.unitsMap (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0))

/-- `(ℤ/pℤ)ˣ` has order `p − 1`. -/
theorem card_units_p [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 :=
  ZMod.card_units p

/-- `(ℤ/p²ℤ)ˣ` has order `p(p − 1) = φ(p²)`. -/
theorem card_units_psq [Fact p.Prime] :
    Fintype.card (ZMod (p ^ 2))ˣ = p * (p - 1) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (by norm_num)]
  simp

/-- Reduction cannot increase the order of an element: `orderOf (red u) ∣ orderOf u`. -/
theorem orderOf_red_dvd (u : (ZMod (p ^ 2))ˣ) : orderOf (red p u) ∣ orderOf u := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← map_pow, pow_orderOf_eq_one, map_one]

/-- **Order dichotomy.** If `p − 1` divides the order of a unit mod `p²`
(which happens exactly when its reduction is a primitive root mod `p`), then the order
is either `p − 1` or the full group order `p(p − 1)`. -/
theorem order_dichotomy [Fact p.Prime] (u : (ZMod (p ^ 2))ˣ)
    (h1 : (p - 1) ∣ orderOf u) :
    orderOf u = p - 1 ∨ orderOf u = p * (p - 1) := by
  have hp : p.Prime := Fact.out
  have hcard : orderOf u ∣ p * (p - 1) := by
    rw [← card_units_psq]; exact orderOf_dvd_card
  obtain ⟨k, hk⟩ := h1
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  rw [hk] at hcard
  have hkp : k ∣ p := by
    have h2 : (p - 1) * k ∣ (p - 1) * p := by rwa [mul_comm p (p - 1)] at hcard
    exact (mul_dvd_mul_iff_left (by omega : (p - 1) ≠ 0)).mp h2
  rcases hp.eq_one_or_self_of_dvd k hkp with h | h
  · left; rw [hk, h, mul_one]
  · right; rw [hk, h]; ring

/-- **The Hensel step (sharp criterion).**

Let `p` be prime and `u` a unit mod `p²` whose reduction mod `p` is a primitive root
(`orderOf (red p u) = p − 1`). Then `u` is a primitive root mod `p²`
(`orderOf u = p(p − 1)`) **iff** `u^(p−1) ≠ 1`.

Thus among the `p` lifts of a primitive root `g` mod `p`, the non-generators are exactly
those satisfying the single congruence `u^(p−1) ≡ 1 (mod p²)`. -/
theorem primitiveRoot_psq_iff [Fact p.Prime] (u : (ZMod (p ^ 2))ˣ)
    (hred : orderOf (red p u) = p - 1) :
    orderOf u = p * (p - 1) ↔ u ^ (p - 1) ≠ 1 := by
  have hp : p.Prime := Fact.out
  have h1 : (p - 1) ∣ orderOf u := hred ▸ orderOf_red_dvd u
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  constructor
  · intro hord hpow1
    have hdvd : orderOf u ∣ (p - 1) := orderOf_dvd_of_pow_eq_one hpow1
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd hp1 hdvd
    nlinarith [hp.two_le]
  · intro hpow
    rcases order_dichotomy u h1 with h | h
    · exfalso; apply hpow
      rw [← h]; exact pow_orderOf_eq_one u
    · exact h

/-- **Existence of a lifted primitive root.**

For an odd prime `p`, there is a primitive root mod `p²` (order `p(p − 1)`) whose
reduction mod `p` is a primitive root mod `p` (order `p − 1`). Equivalently, every
primitive root mod `p` admits a lift generating `(ℤ/p²ℤ)ˣ`. -/
theorem exists_primitiveRoot_psq [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ u : (ZMod (p ^ 2))ˣ, orderOf u = p * (p - 1) ∧ orderOf (red p u) = p - 1 := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcyc : IsCyclic (ZMod (p ^ 2))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 2
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  have hsurj : Function.Surjective (red p) := ZMod.unitsMap_surjective _
  refine ⟨γ, ?_, ?_⟩
  · rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, card_units_psq]
  · have hmem : ∀ y : (ZMod p)ˣ, y ∈ Subgroup.zpowers (red p γ) := by
      intro y
      obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨k, hk⟩ := hγ x
      refine ⟨k, ?_⟩
      simp only at hk ⊢
      rw [← map_zpow, hk]
    rw [orderOf_eq_card_of_forall_mem_zpowers hmem, Nat.card_eq_fintype_card, card_units_p]

end PrimitiveRootsOQ05
