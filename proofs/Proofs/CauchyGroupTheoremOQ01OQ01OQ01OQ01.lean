import Mathlib

/-!
# Counting the solutions of `xⁿ = 1` in a cyclic group: the exact count is `gcd(n, |G|)`

## What this proves

For a finite **cyclic** group `α` of order `m = |α|` and any exponent `n : ℕ`, the equation
`xⁿ = 1` has **exactly `gcd(n, m)` solutions**:

```
#{a : α | a ^ n = 1} = Nat.gcd n (Fintype.card α)     (`card_pow_eq_one_eq_gcd`)
```

This is the sharp, cyclic-group instance of **Frobenius's theorem**, which says that in *any*
finite group the number of solutions of `xⁿ = 1` is divisible by `gcd(n, |G|)`. In the cyclic
case the Frobenius lower bound `gcd(n, |G|) ∣ #{xⁿ = 1}` is achieved with *equality*
(`gcd_dvd_card_pow_eq_one`): a cyclic group has the *fewest* possible `n`-th unity solutions.

Read additively (`α ≅ ZMod m`), the statement counts the solutions of the linear congruence
`n · x ≡ 0 (mod m)`, of which there are precisely `gcd(n, m)` — the classical count.

## The parent chain

* `cauchy-group-theorem-oq-01` — Cauchy's theorem: a prime `p ∣ |G|` forces an order-`p` element.
* `…-oq-01-oq-01-oq-01` — the **power-map dichotomy**: `x ↦ xⁿ` is a *bijection* iff
  `gcd(n, |G|) = 1`.

The dichotomy is the boundary `gcd = 1` of the present, finer statement: the power map is
injective exactly when its only `n`-th unity solution is the identity, i.e. when the count
here equals `1` (`card_pow_eq_one_eq_one_iff_coprime`). This file replaces the qualitative
"bijective / not bijective" answer with the exact *fibre count* `gcd(n, |G|)`.

## The proof

Three Mathlib facts about cyclic groups assemble the count, with no new analytic input:

1. `xⁿ = 1` and `x^{gcd(n,m)} = 1` cut out the **same** set: `orderOf x ∣ n` together with the
   automatic `orderOf x ∣ m` is equivalent to `orderOf x ∣ gcd(n, m)`.
2. `sum_card_orderOf_eq_card_pow_eq_one` partitions that set by element order:
   `#{x^{g} = 1} = ∑_{d ∣ g} #{orderOf x = d}`.
3. In a cyclic group `#{orderOf x = d} = φ(d)` for `d ∣ m` (`IsCyclic.card_orderOf_eq_totient`),
   and Gauss's `∑_{d ∣ g} φ(d) = g` (`Nat.sum_totient`) collapses the sum to `gcd(n, m)`.

Everything is fully machine-checked with no `sorry` and no extra axioms.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01

open Finset

variable {α : Type*} [Group α] [Fintype α] [DecidableEq α] [IsCyclic α]

/-- **Main counting theorem.** In a finite cyclic group `α` of order `m`, the equation
`xⁿ = 1` has exactly `gcd(n, m)` solutions. This is the sharp cyclic case of Frobenius's
theorem on the number of solutions of `xⁿ = 1`. -/
theorem card_pow_eq_one_eq_gcd (n : ℕ) :
    #{a : α | a ^ n = 1} = Nat.gcd n (Fintype.card α) := by
  have hmpos : 0 < Fintype.card α := Fintype.card_pos
  have hg0 : Nat.gcd n (Fintype.card α) ≠ 0 := by
    rw [Ne, Nat.gcd_eq_zero_iff]; rintro ⟨-, h⟩; exact absurd h hmpos.ne'
  -- Step 1: `xⁿ = 1` and `x^{gcd n m} = 1` carve out the same set, because `orderOf x ∣ m`.
  have key : ∀ a : α, (a ^ n = 1) ↔ (a ^ Nat.gcd n (Fintype.card α) = 1) := by
    intro a
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
    exact ⟨fun h => Nat.dvd_gcd h orderOf_dvd_card, fun h => h.trans (Nat.gcd_dvd_left _ _)⟩
  simp only [key]
  -- Step 2: partition the solution set by element order, then sum totients.
  rw [← sum_card_orderOf_eq_card_pow_eq_one hg0,
    Finset.sum_congr rfl fun d hd => IsCyclic.card_orderOf_eq_totient
      ((Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right _ _))]
  exact Nat.sum_totient _

/-- The same count phrased with `Nat.card`. -/
theorem card_pow_eq_one_eq_gcd_natCard (n : ℕ) :
    #{a : α | a ^ n = 1} = Nat.gcd n (Nat.card α) := by
  rw [card_pow_eq_one_eq_gcd, Nat.card_eq_fintype_card]

/-- **Frobenius divisibility, achieved with equality.** `gcd(n, |G|)` divides the number of
solutions of `xⁿ = 1`. Frobenius's theorem gives this divisibility for an arbitrary finite
group; in the cyclic case the count *equals* `gcd(n, |G|)`, so the bound is sharp. -/
theorem gcd_dvd_card_pow_eq_one (n : ℕ) :
    Nat.gcd n (Fintype.card α) ∣ #{a : α | a ^ n = 1} := by
  rw [card_pow_eq_one_eq_gcd]

/-- The bridge back to the parent **power-map dichotomy**: `xⁿ = 1` has the identity as its
*only* solution iff `n` is coprime to `|G|` — exactly when `x ↦ xⁿ` is a bijection. -/
theorem card_pow_eq_one_eq_one_iff_coprime (n : ℕ) :
    #{a : α | a ^ n = 1} = 1 ↔ Nat.Coprime n (Fintype.card α) := by
  rw [card_pow_eq_one_eq_gcd]

/-! ### A concrete instance: the cyclic group `C₁₂` -/

/-- In the cyclic group `C₁₂` of order `12`, the equation `x⁸ = 1` has `gcd(8, 12) = 4`
solutions (the elements of the unique order-dividing-`4` subgroup). -/
example : #{a : Multiplicative (ZMod 12) | a ^ 8 = 1} = 4 := by
  rw [card_pow_eq_one_eq_gcd]; decide

/-- When the exponent is coprime to the order, the only solution of `xⁿ = 1` is the identity:
in `C₁₂`, `x⁷ = 1` has the single solution `x = 1` since `gcd(7, 12) = 1`. -/
example : #{a : Multiplicative (ZMod 12) | a ^ 7 = 1} = 1 := by
  rw [card_pow_eq_one_eq_gcd]; decide

end CauchyGroupTheoremOQ01OQ01OQ01OQ01
