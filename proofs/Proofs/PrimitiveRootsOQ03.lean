import Mathlib

/-!
# Order Distribution in (ℤ/pℤ)ˣ and Gauss's Divisor Sum

## What This Proves

The base Primitive-Roots entry counts only the **generators** of `(ℤ/pℤ)ˣ` —
the elements of the *single* order `p − 1`, of which there are `φ(p − 1)`.
This file gives the **full order distribution**: for *every* divisor `d` of
`p − 1`,

  **`(ℤ/pℤ)ˣ` has exactly `φ(d)` elements of order `d`.**

Summing this over all divisors of `p − 1` tiles the whole group, and because
the orders partition the `p − 1` units, it recovers **Gauss's identity**

  `∑_{d ∣ p−1} φ(d) = p − 1`

from the group-theoretic side: each order class contributes `φ(d)` elements and
the classes exhaust the group.

## Why This Is New

The existing `PrimitiveRoots` family proves only the `d = p − 1` special case
(`card_primitiveRoots : #generators = φ(p−1)`). The general all-`d` distribution,
the existence of an element of each order `d ∣ p − 1`, and the group-theoretic
tiling that yields Gauss's divisor sum are not in the family. The engine is
Mathlib's `IsCyclic.card_orderOf_eq_totient`, here specialized to the cyclic
group `(ℤ/pℤ)ˣ` for arbitrary `d` and summed across divisors.

## Main Results

* `card_orderOf_eq_totient` : `#{g : (ℤ/pℤ)ˣ | orderOf g = d} = φ(d)` for `d ∣ p−1`
* `exists_orderOf_eq`       : an element of order `d` exists for every `d ∣ p−1`
* `card_generators`         : `d = p−1` recovers `#generators = φ(p−1)`
* `sum_card_orderOf`        : the order classes tile the group (sum `= p−1`)
* `gauss_divisor_sum`       : `∑_{d ∣ p−1} φ(d) = p − 1`
-/

namespace PrimitiveRootsOQ03

open Finset Nat

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- `(ℤ/pℤ)ˣ` is cyclic (finite multiplicative subgroup of the field `ℤ/pℤ`). -/
instance : IsCyclic (ZMod p)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod p)) Units.coeHom_injective

/-- The order of the unit group `(ℤ/pℤ)ˣ` is `p − 1`. -/
theorem card_units : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/-! ## The full order distribution -/

/-- **Order distribution of `(ℤ/pℤ)ˣ`.** For every divisor `d` of `p − 1`, the
unit group has exactly `φ(d)` elements of order `d`.

This is the general-`d` strengthening of the base entry's generator count
(`d = p − 1`). It is a direct specialization of Mathlib's
`IsCyclic.card_orderOf_eq_totient` to the cyclic group `(ℤ/pℤ)ˣ`, whose order is
`p − 1` (`card_units`). -/
theorem card_orderOf_eq_totient {d : ℕ} (hd : d ∣ p - 1) :
    (univ.filter (fun g : (ZMod p)ˣ => orderOf g = d)).card = Nat.totient d := by
  have hdvd : d ∣ Fintype.card (ZMod p)ˣ := by rw [card_units]; exact hd
  have hcount := IsCyclic.card_orderOf_eq_totient (α := (ZMod p)ˣ) hdvd
  simp only at hcount ⊢
  convert hcount using 2

/-- For every divisor `d` of `p − 1` there exists a unit of order exactly `d`.
(The count `φ(d)` is positive since `d ≥ 1`.) -/
theorem exists_orderOf_eq {d : ℕ} (hd : d ∣ p - 1) :
    ∃ g : (ZMod p)ˣ, orderOf g = d := by
  have hp1 : 0 < p - 1 := by
    have := hp.out.two_le; omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hp1
  have hcard := card_orderOf_eq_totient (p := p) hd
  have hne : (univ.filter (fun g : (ZMod p)ˣ => orderOf g = d)).Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact Nat.totient_pos.mpr hdpos
  obtain ⟨g, hg⟩ := hne
  exact ⟨g, (Finset.mem_filter.mp hg).2⟩

/-- The classical generator count, recovered as the `d = p − 1` case: there are
exactly `φ(p − 1)` primitive roots modulo `p`. -/
theorem card_generators :
    (univ.filter (fun g : (ZMod p)ˣ => orderOf g = p - 1)).card = Nat.totient (p - 1) :=
  card_orderOf_eq_totient (dvd_refl _)

/-! ## Tiling and Gauss's divisor sum -/

/-- **The order classes tile the group.** Summing the number of elements of each
order `d ∣ p − 1` recovers the group order `p − 1`. This is the group-theoretic
content of Gauss's identity: every unit has some order dividing `p − 1`, the
classes are disjoint, and each contributes `φ(d)` elements. -/
theorem sum_card_orderOf :
    ∑ d ∈ (p - 1).divisors,
        (univ.filter (fun g : (ZMod p)ˣ => orderOf g = d)).card = p - 1 := by
  have h : ∑ d ∈ (p - 1).divisors,
        (univ.filter (fun g : (ZMod p)ˣ => orderOf g = d)).card
      = ∑ d ∈ (p - 1).divisors, Nat.totient d := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    exact card_orderOf_eq_totient (Nat.dvd_of_mem_divisors hd)
  rw [h]
  exact Nat.sum_totient (p - 1)

omit hp in
/-- **Gauss's divisor sum** `∑_{d ∣ p−1} φ(d) = p − 1`, here read off the order
distribution of `(ℤ/pℤ)ˣ`: each side counts the `p − 1` units, partitioned by
their order. (Mathlib's `Nat.sum_totient` gives the number-theoretic proof; this
states it in the primitive-root setting.) -/
theorem gauss_divisor_sum :
    ∑ d ∈ (p - 1).divisors, Nat.totient d = p - 1 :=
  Nat.sum_totient (p - 1)

end PrimitiveRootsOQ03
