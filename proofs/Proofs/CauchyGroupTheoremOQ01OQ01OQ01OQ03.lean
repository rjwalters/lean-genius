import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-
# The power-map dichotomy over finite monoids: the unit-group threshold

## What This Proves

The parent file `CauchyGroupTheoremOQ01OQ01OQ01` established the sharp
dichotomy for a finite **group** `G`:

```
Function.Bijective (· ^ n : G → G)  ↔  (Nat.card G).Coprime n .
```

Its proof of the hard direction rests on **Cauchy's theorem**
(`exists_prime_orderOf_dvd_card'`), which is a statement about groups: it needs
every element to be invertible. This file asks what survives when `G` is only a
finite **monoid** `M`, where non-invertible elements exist and Cauchy's theorem
is unavailable.

### The bridge: units are detected by any positive power

The key structural fact, valid in *any* monoid, is

```
n ≠ 0  →  (IsUnit (xⁿ) ↔ IsUnit x)                      (`isUnit_pow_iff`)
```

so the power map `x ↦ xⁿ` neither creates nor destroys units: it maps the unit
group `Mˣ` into itself and maps non-units to non-units. Consequently a bijective
power map on `M` **restricts to a bijection on the unit group** `Mˣ`
(`units_pow_bijective_of_pow_bijective`). Feeding that restriction into the
group dichotomy applied to `Mˣ` yields the

* **Necessary condition** (`coprime_card_units_of_pow_bijective`): if
  `x ↦ xⁿ` is a bijection on a finite monoid `M` with `n ≠ 0`, then `n` is
  coprime to `|Mˣ|`.

### The converse fails — the monoid threshold is only necessary

Over monoids the coprimality condition is **no longer sufficient**
(`converse_fails`). The obstruction is nilpotence, which the unit group cannot
see. Concretely take `M = ZMod 4` and `n = 3`:

* `|(ZMod 4)ˣ| = φ(4) = 2`, and `gcd(3, 2) = 1`, so `3` is coprime to the order
  of the unit group;
* yet `2³ = 8 = 0 = 0³` in `ZMod 4` while `2 ≠ 0`, so `x ↦ x³` is not even
  injective.

Thus the clean group iff degrades to a one-directional implication for monoids,
with the gap governed exactly by the non-unit (e.g. nilpotent) part of `M`.

### Consistency with the parent

On a finite group every element is a unit, so `Mˣ ≃ G`, the non-unit part is
empty, and the necessary condition becomes the parent's iff again
(`group_consistency`). The group dichotomy is recovered as the special case
where the counterexample above cannot occur.

## Context

This is the multiplicative-monoid refinement of "multiplication by `n` is
invertible mod `m` iff `gcd(n,m)=1`". For a finite commutative monoid it isolates
precisely which arithmetic information — the order of the unit group — the power
map can encode, and shows that everything outside the unit group (idempotents,
nilpotents, absorbing elements) is invisible to the coprimality threshold.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ03

open Function

/-! ### The group dichotomy (recalled self-contained from the parent) -/

section Group

variable {G : Type*} [Group G]

/-- **Hard direction (contrapositive), via Cauchy's theorem.** On a finite group,
if `n` is not coprime to `|G|` then the `n`-th power map is not injective: a prime
`p ∣ gcd(n, |G|)` gives, by Cauchy, an element of order `p` sent to `1` alongside
`1`. (Self-contained copy of the parent's core argument.) -/
theorem not_injective_pow_of_not_coprime [Finite G] {n : ℕ}
    (h : ¬ (Nat.card G).Coprime n) : ¬ Injective (· ^ n : G → G) := by
  have hd1 : (Nat.card G).gcd n ≠ 1 := h
  set p := ((Nat.card G).gcd n).minFac with hp
  have hpp : p.Prime := Nat.minFac_prime hd1
  have hdvd : p ∣ (Nat.card G).gcd n := Nat.minFac_dvd _
  have hpG : p ∣ Nat.card G := hdvd.trans (Nat.gcd_dvd_left _ _)
  have hpn : p ∣ n := hdvd.trans (Nat.gcd_dvd_right _ _)
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpG
  have hon : orderOf g ∣ n := by rw [hg]; exact hpn
  have hgn : g ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hon
  have hgne : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact hpp.ne_one hg.symm
  intro hinj
  exact hgne (hinj (show g ^ n = (1 : G) ^ n by simp [hgn]))

/-- **The power-map dichotomy on a finite group.** `x ↦ xⁿ` is a bijection iff
`n` is coprime to `|G|`. -/
theorem pow_bijective_iff_coprime [Finite G] (n : ℕ) :
    Bijective (· ^ n : G → G) ↔ (Nat.card G).Coprime n := by
  constructor
  · intro hbij
    by_contra hc
    exact not_injective_pow_of_not_coprime hc hbij.injective
  · exact fun h => h.pow_left_bijective

end Group

/-! ### The monoid bridge -/

section Monoid

variable {M : Type*} [Monoid M]

/-- Units are detected by any positive power: `xⁿ` is a unit iff `x` is (Mathlib's
`isUnit_pow_iff`, in any monoid). This is the structural fact that lets the power
map see the unit group. -/
theorem isUnit_pow_iff_pos {n : ℕ} (hn : n ≠ 0) (x : M) :
    IsUnit (x ^ n) ↔ IsUnit x :=
  isUnit_pow_iff hn

/-- **Key restriction lemma.** If the `n`-th power map is bijective on a finite
monoid `M` (with `n ≠ 0`), then it restricts to a bijection on the unit group
`Mˣ`. Injectivity is inherited from `M`; surjectivity uses `isUnit_pow_iff` to
pull a preimage back into `Mˣ`. -/
theorem units_pow_bijective_of_pow_bijective [Finite M] {n : ℕ} (hn : n ≠ 0)
    (h : Bijective (· ^ n : M → M)) : Bijective (· ^ n : Mˣ → Mˣ) := by
  haveI : Finite Mˣ := Finite.of_injective _ Units.val_injective
  constructor
  · -- injective: reflect equality of powers through the coercion `Mˣ → M`
    intro u v huv
    have huv' : u ^ n = v ^ n := huv
    apply Units.val_injective
    apply h.injective
    show ((u : M)) ^ n = ((v : M)) ^ n
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, huv']
  · -- surjective: a preimage of a unit is itself a unit
    intro u
    obtain ⟨x, hx⟩ := h.surjective (u : M)
    have hxn : x ^ n = (u : M) := hx
    have hxu : IsUnit x := (isUnit_pow_iff hn).mp (by rw [hxn]; exact u.isUnit)
    refine ⟨hxu.unit, Units.val_injective ?_⟩
    show ((hxu.unit ^ n : Mˣ) : M) = (u : M)
    rw [Units.val_pow_eq_pow_val, hxu.unit_spec]
    exact hxn

/-- **The monoid necessary condition.** On a finite monoid, if `x ↦ xⁿ` is a
bijection (`n ≠ 0`) then `n` is coprime to the order of the unit group `Mˣ`. -/
theorem coprime_card_units_of_pow_bijective [Finite M] {n : ℕ} (hn : n ≠ 0)
    (h : Bijective (· ^ n : M → M)) : (Nat.card Mˣ).Coprime n := by
  haveI : Finite Mˣ := Finite.of_injective _ Units.val_injective
  exact (pow_bijective_iff_coprime (G := Mˣ) n).mp
    (units_pow_bijective_of_pow_bijective hn h)

/-- The power-map dichotomy on the unit group of a finite monoid: the group
result of the parent, applied verbatim to `Mˣ`. -/
theorem pow_bijective_units_iff_coprime [Finite M] (n : ℕ) :
    Bijective (· ^ n : Mˣ → Mˣ) ↔ (Nat.card Mˣ).Coprime n := by
  haveI : Finite Mˣ := Finite.of_injective _ Units.val_injective
  exact pow_bijective_iff_coprime (G := Mˣ) n

end Monoid

/-! ### The converse fails: coprimality does not suffice over monoids -/

/-- The unit group of `ZMod 4` has order `φ(4) = 2`. -/
theorem card_units_zmod4 : Nat.card (ZMod 4)ˣ = 2 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  decide

/-- `3` is coprime to `|(ZMod 4)ˣ| = 2`. -/
theorem coprime_three_card_units_zmod4 : (Nat.card (ZMod 4)ˣ).Coprime 3 := by
  rw [card_units_zmod4]
  decide

/-- Yet cubing is not injective on `ZMod 4`: `2³ = 0 = 0³` while `2 ≠ 0`. -/
theorem pow3_not_injective_zmod4 : ¬ Injective (· ^ 3 : ZMod 4 → ZMod 4) := by
  intro h
  have h20 : (2 : ZMod 4) = 0 := h (by decide : (2 : ZMod 4) ^ 3 = (0 : ZMod 4) ^ 3)
  exact (by decide : (2 : ZMod 4) ≠ 0) h20

/-- Hence cubing is not bijective on `ZMod 4`. -/
theorem pow3_not_bijective_zmod4 : ¬ Bijective (· ^ 3 : ZMod 4 → ZMod 4) :=
  fun hb => pow3_not_injective_zmod4 hb.injective

/-- **The converse of the monoid dichotomy fails.** There is an exponent coprime
to the order of the unit group whose power map is nonetheless not bijective —
witnessed by `M = ZMod 4`, `n = 3`. So `coprime_card_units_of_pow_bijective`
cannot be upgraded to an iff over monoids. -/
theorem converse_fails :
    ∃ n : ℕ, (Nat.card (ZMod 4)ˣ).Coprime n ∧ ¬ Bijective (· ^ n : ZMod 4 → ZMod 4) :=
  ⟨3, coprime_three_card_units_zmod4, pow3_not_bijective_zmod4⟩

/-! ### Consistency with the parent (group) case -/

/-- On a finite group every element is a unit, so the non-unit gap is empty and
the monoid necessary condition coincides with the parent's iff. -/
theorem group_consistency {G : Type*} [Group G] [Finite G] (n : ℕ) :
    Bijective (· ^ n : G → G) ↔ (Nat.card G).Coprime n :=
  pow_bijective_iff_coprime n

end CauchyGroupTheoremOQ01OQ01OQ01OQ03
