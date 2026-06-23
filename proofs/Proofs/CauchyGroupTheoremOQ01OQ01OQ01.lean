import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The power-map dichotomy: `x ↦ xⁿ` is a bijection iff `gcd(n, |G|) = 1`

## What This Proves

For a finite group `G` and an exponent `n : ℕ`, the `n`-th power map
`x ↦ xⁿ : G → G` is a bijection **if and only if** `n` is coprime to the
order of `G`:

```
Function.Bijective (· ^ n : G → G)  ↔  (Nat.card G).Coprime n
```

This is the exact uniform threshold governing when raising to a power permutes
a finite group, and it sharpens the parent file `CauchyGroupTheoremOQ01OQ01`
(which handles only the squaring case `n = 2`: squaring is a bijection iff the
order is odd) into the full statement for every exponent.

### The two directions

* **Coprime ⟹ bijection** (`pow_left_bijective_of_coprime`). This is the easy
  half and is already in Mathlib as `Nat.Coprime.pow_left_bijective`: if
  `gcd(n,|G|)=1`, Bézout gives integers `a, b` with `an + b|G| = 1`, so
  `x ↦ x ^ a` inverts `x ↦ x ^ n` (using `x ^ |G| = 1`). Notably this works for
  *every* finite group, abelian or not — the inverse is again a power map.

* **Bijection ⟹ coprime** (`not_injective_pow_of_not_coprime`). This is the
  content of the file. We prove the contrapositive: if `gcd(n,|G|) ≠ 1`, pick a
  prime `p` dividing the gcd (its `minFac`). Then `p ∣ |G|`, so **Cauchy's
  theorem** (`exists_prime_orderOf_dvd_card'`) produces an element `g` of order
  exactly `p`. Since also `p ∣ n` we have `gⁿ = 1 = 1ⁿ` while `g ≠ 1`, so the
  power map collapses two points — it is not injective, hence not a bijection.

### Consequences packaged here

* **Headline equivalence** (`pow_bijective_iff_coprime`).
* **Injective / surjective forms** (`pow_injective_iff_coprime`,
  `pow_surjective_iff_coprime`): on a finite group injectivity, surjectivity and
  bijectivity of the power map all coincide and are each equivalent to
  coprimality (`Finite.injective_iff_surjective`).
* **Recovering the parent** (`sq_bijective_iff_odd_card`): the `n = 2`
  specialisation, `x ↦ x²` is a bijection iff `|G|` is odd, via
  `Nat.coprime_two_right`. The parent's odd-order squaring result is exactly
  this slice.
* **Concrete instances on the symmetric group** (`card_perm_fin3`,
  `pow5_bijective_perm_fin3`, `pow2_not_bijective_perm_fin3`): on
  `Equiv.Perm (Fin 3)` (order `6`), the fifth-power map is a bijection
  (`gcd(5,6)=1`) while squaring is not (`gcd(2,6)=2`). Coprimality is decided by
  `decide` on `Nat.gcd` — no `native_decide`, so the file stays genuinely
  `0`-axiom.

## Context

Cauchy's theorem detects a prime divisor `p` of `|G|` by producing an element
of order `p`. That single element is exactly the obstruction to the power map
`x ↦ x^p` being injective. Quantifying over all prime divisors of `gcd(n,|G|)`
turns Cauchy's existence statement into the sharp iff above. The result is the
multiplicative analogue of "multiplication by `n` is invertible mod `m` iff
`gcd(n,m)=1`", and it is the structural fact behind RSA-style exponentiation in
finite abelian groups.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01

open Function

variable {G : Type*} [Group G]

/-- **Easy direction** (Mathlib's `Nat.Coprime.pow_left_bijective`): if `n` is
coprime to `|G|`, the `n`-th power map is a bijection. Recorded here under a
descriptive name. -/
theorem pow_left_bijective_of_coprime [Finite G] {n : ℕ}
    (h : (Nat.card G).Coprime n) : Bijective (· ^ n : G → G) :=
  h.pow_left_bijective

/-- **Hard direction (contrapositive).** If `n` is *not* coprime to `|G|`, the
`n`-th power map fails to be injective: a prime `p ∣ gcd(n,|G|)` produces, via
Cauchy's theorem, an element of order `p` that the map sends to `1` alongside
`1` itself. -/
theorem not_injective_pow_of_not_coprime [Finite G] {n : ℕ}
    (h : ¬ (Nat.card G).Coprime n) : ¬ Injective (· ^ n : G → G) := by
  -- `gcd(|G|, n) ≠ 1`, so it has a prime factor `p := minFac`.
  have hd1 : (Nat.card G).gcd n ≠ 1 := h
  set p := ((Nat.card G).gcd n).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hd1
  have hdvd : p ∣ (Nat.card G).gcd n := Nat.minFac_dvd _
  have hpG : p ∣ Nat.card G := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_right _ _)
  haveI : Fact p.Prime := ⟨hpp⟩
  -- Cauchy: an element `g` of order exactly `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpG
  -- `p ∣ n` and `orderOf g = p` give `gⁿ = 1`.
  have hon : orderOf g ∣ n := by rw [hg]; exact hpn
  have hgn : g ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hon
  -- `g ≠ 1` because `orderOf g = p ≥ 2`.
  have hgne : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hpp.ne_one hg.symm
  -- The map sends both `g` and `1` to `1`.
  intro hinj
  exact hgne (hinj (show g ^ n = (1 : G) ^ n by simp [hgn]))

/-- **The power-map dichotomy.** On a finite group, `x ↦ xⁿ` is a bijection iff
`n` is coprime to the order of the group. -/
theorem pow_bijective_iff_coprime [Finite G] (n : ℕ) :
    Bijective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  constructor
  · intro hbij
    by_contra hc
    exact not_injective_pow_of_not_coprime hc hbij.injective
  · exact pow_left_bijective_of_coprime

/-- Injective form: on a finite group injectivity of the power map already forces
coprimality (and conversely). -/
theorem pow_injective_iff_coprime [Finite G] (n : ℕ) :
    Injective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  rw [← pow_bijective_iff_coprime]
  exact ⟨fun hinj => ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, Bijective.injective⟩

/-- Surjective form: on a finite group surjectivity of the power map already
forces coprimality (and conversely). -/
theorem pow_surjective_iff_coprime [Finite G] (n : ℕ) :
    Surjective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  rw [← pow_bijective_iff_coprime]
  exact ⟨fun hsurj => ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩,
    Bijective.surjective⟩

/-- **Recovering the parent (`n = 2`).** Squaring is a bijection iff the order of
the group is odd — the `n = 2` slice of `pow_bijective_iff_coprime`, matching
`CauchyGroupTheoremOQ01OQ01`. -/
theorem sq_bijective_iff_odd_card [Finite G] :
    Bijective (· ^ 2 : G → G) ↔ Odd (Nat.card G) := by
  rw [pow_bijective_iff_coprime, Nat.coprime_two_right]

/-- The symmetric group on three letters has order `6`. -/
theorem card_perm_fin3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl

/-- Concrete bijection: on `S₃` (order `6`), the fifth-power map is a bijection,
since `gcd(5, 6) = 1`. -/
theorem pow5_bijective_perm_fin3 :
    Bijective (· ^ 5 : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) := by
  rw [pow_bijective_iff_coprime, card_perm_fin3]
  decide

/-- Concrete failure: on `S₃` (order `6`), squaring is *not* a bijection, since
`gcd(2, 6) = 2 ≠ 1`. (Indeed every transposition squares to `1`.) -/
theorem pow2_not_bijective_perm_fin3 :
    ¬ Bijective (· ^ 2 : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) := by
  rw [pow_bijective_iff_coprime, card_perm_fin3]
  decide

end CauchyGroupTheoremOQ01OQ01OQ01
