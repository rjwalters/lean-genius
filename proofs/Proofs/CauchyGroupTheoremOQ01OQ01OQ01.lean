import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# When is the n-th power map a bijection? The coprimality criterion

## What This Proves

The sibling file `CauchyGroupTheoremOQ01OQ01` settles the **squaring** map
`x ↦ x²` on a finite group: it is a bijection exactly when `|G|` is odd, i.e.
exactly when `gcd(2, |G|) = 1`. This file proves the full generalization to the
`n`-th power map `x ↦ xⁿ`, the sharp two-directional criterion:

> On a finite group `G`, the map `x ↦ xⁿ` is a bijection **iff**
> `gcd(n, |G|) = 1`.

Mathlib supplies only the *forward* implication, packaged as
`Nat.Coprime.pow_left_bijective` (built from the explicit inverse
`powCoprime`). The **converse** — bijectivity forces coprimality — is not in
Mathlib. It is the genuinely new content here, and it is what turns the
one-directional Mathlib lemma into an `iff` and recovers the parent's
squaring boundary as the special case `n = 2`.

## The mathematics

* **Forward** (`pow_bijective_of_coprime`). If `gcd(|G|, n) = 1` then `x ↦ xⁿ`
  is a bijection. Bézout gives `a·|G| + b·n = 1`, so `(xⁿ)^b = x^{b·n} =
  x^{1 - a·|G|} = x · (x^{|G|})^{-a} = x` since `x^{|G|} = 1`. The inverse map
  is `x ↦ x^b`. This is `Nat.Coprime.pow_left_bijective`.

* **Converse** (`coprime_of_pow_bijective`, NEW). If `gcd(|G|, n) ≠ 1`, pick a
  prime `p ∣ gcd(|G|, n)`. Since `p ∣ |G|`, Cauchy's theorem
  (`exists_prime_orderOf_dvd_card'`) produces an element `x` of order exactly
  `p`; in particular `x ≠ 1`. Since `p ∣ n` and `orderOf x = p`, we get
  `xⁿ = 1 = 1ⁿ`. So `x` and `1` are two distinct elements with the same
  `n`-th power: the map is not injective, contradicting bijectivity.

* **Criterion** (`pow_bijective_iff_coprime`). The two directions combine into
  the clean equivalence. On a finite set a self-map is injective iff surjective
  iff bijective, so the criterion holds verbatim for each of the three notions
  (`pow_injective_iff_coprime`, `pow_surjective_iff_coprime`).

* **Specializations.** Setting `n = 2` recovers the parent boundary
  `x ↦ x²` is a bijection `↔ |G| odd` (`pow_bijective_iff_odd_card`). A
  `Fintype.card` restatement (`pow_bijective_iff_coprime_card`) matches the usual
  `gcd(n, |G|)` phrasing.

All statements hold for an arbitrary finite group — abelian or not — because the
power map, while not a homomorphism in the nonabelian case, still acts within
each cyclic subgroup `⟨x⟩` where everything commutes.
-/

open Function

variable {G : Type*} [Group G] [Finite G] {n : ℕ}

omit [Finite G] in
/-- **Forward direction.** If `gcd(|G|, n) = 1` then the `n`-th power map is a
bijection. This is Mathlib's `Nat.Coprime.pow_left_bijective`, restated here for
the criterion below; the explicit inverse is `x ↦ x ^ (gcdB |G| n)`. -/
theorem pow_bijective_of_coprime (h : (Nat.card G).Coprime n) :
    Bijective (· ^ n : G → G) :=
  Nat.Coprime.pow_left_bijective h

/-- **Converse direction (new).** If the `n`-th power map on a finite group is a
bijection, then `gcd(|G|, n) = 1`. Not available in Mathlib. -/
theorem coprime_of_pow_bijective (h : Bijective (· ^ n : G → G)) :
    (Nat.card G).Coprime n := by
  by_contra hcop
  -- `gcd(|G|, n) ≠ 1`, so it has a prime factor `p`.
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcop
  have hpcard : p ∣ Nat.card G := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpn : p ∣ n := hpdvd.trans (Nat.gcd_dvd_right _ _)
  haveI : Fact p.Prime := ⟨hp⟩
  -- Cauchy: an element of order exactly `p`.
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpcard
  -- `p ∣ n` and `orderOf x = p` give `xⁿ = 1`.
  have hxn : x ^ n = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hx]; exact hpn
  -- `x ≠ 1` because its order is the prime `p ≠ 1`.
  have hne : x ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hx; exact hp.ne_one hx.symm
  -- `x` and `1` collide under the power map: contradiction with injectivity.
  exact hne (h.injective (by simpa using hxn))

/-- **The criterion.** On a finite group, the `n`-th power map is a bijection iff
`gcd(|G|, n) = 1`. -/
theorem pow_bijective_iff_coprime :
    Bijective (· ^ n : G → G) ↔ (Nat.card G).Coprime n :=
  ⟨coprime_of_pow_bijective, pow_bijective_of_coprime⟩

/-- Injective form of the criterion (on a finite set, injective = bijective). -/
theorem pow_injective_iff_coprime :
    Injective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  rw [← pow_bijective_iff_coprime, Finite.injective_iff_bijective]

/-- Surjective form of the criterion (on a finite set, surjective = bijective). -/
theorem pow_surjective_iff_coprime :
    Surjective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  rw [← pow_bijective_iff_coprime, Finite.surjective_iff_bijective]

/-- `Fintype.card` restatement matching the usual `gcd(n, |G|)` phrasing. -/
theorem pow_bijective_iff_coprime_card [Fintype G] :
    Bijective (· ^ n : G → G) ↔ (Fintype.card G).Coprime n := by
  rw [pow_bijective_iff_coprime, Nat.card_eq_fintype_card]

/-- **Recovering the parent boundary.** Squaring is a bijection iff `|G|` is odd.
The case `n = 2` of the criterion, via `gcd(|G|, 2) = 1 ↔ Odd |G|`. This is
exactly the squaring boundary of the sibling file, now a corollary. -/
theorem pow_bijective_iff_odd_card :
    Bijective (· ^ 2 : G → G) ↔ Odd (Nat.card G) := by
  rw [pow_bijective_iff_coprime, Nat.coprime_two_right]

/-- Sanity instance: on the cyclic group of order `5`, cubing is a bijection
(`gcd(3, 5) = 1`). -/
example : Bijective (· ^ 3 : Multiplicative (ZMod 5) → Multiplicative (ZMod 5)) := by
  rw [pow_bijective_iff_coprime, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]
  decide

/-- Sanity instance: on the cyclic group of order `6`, cubing is **not** a
bijection (`gcd(3, 6) = 3 ≠ 1`). -/
example : ¬ Bijective (· ^ 3 : Multiplicative (ZMod 6) → Multiplicative (ZMod 6)) := by
  rw [pow_bijective_iff_coprime, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]
  decide
