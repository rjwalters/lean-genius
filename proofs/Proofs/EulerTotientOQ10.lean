import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

/-
# Menon's Identity (OQ-10)

## Open Question

Beyond the basic theory of the Euler totient `φ`, a classical identity over the
units of `ℤ/nℤ` is **Menon's identity** (P. Kesava Menon, 1965):

> For every `n ≥ 1`,
>   `∑_{1 ≤ k ≤ n, gcd(k,n)=1} gcd(k − 1, n) = φ(n) · d(n)`,
> where `d(n)` is the number of divisors of `n`.

We give the slick **counting proof**, fully uniform in `n` (no factorisation, no
multiplicativity bookkeeping).  Indexing the sum by the units `a ∈ (ℤ/nℤ)ˣ`, the
summand is `gcd((a − 1).val, n)`.

## Proof (counting over the divisor lattice)

1. **Divisor expansion.**  For any `v` and `n ≠ 0`,
     `gcd(v, n) = ∑_{d ∣ n, d ∣ v} φ(d)`,
   because `∑_{e ∣ g} φ(e) = g` (Gauss, `Nat.sum_totient`) applied to
   `g = gcd(v, n)`, whose divisors are exactly the common divisors of `v` and `n`.

2. **Swap the order of summation.**
     `LHS = ∑_{d ∣ n} φ(d) · #{a ∈ (ℤ/nℤ)ˣ : d ∣ (a − 1).val}`.

3. **Count each fibre.**  The reduction `unitsMap : (ℤ/nℤ)ˣ → (ℤ/dℤ)ˣ` is a
   *surjective* group homomorphism (`ZMod.unitsMap_surjective`), and
     `d ∣ (a − 1).val ⟺ a ∈ ker(unitsMap)`.
   For a surjective homomorphism of finite groups `|G| = |H| · |ker|`
   (Lagrange + first isomorphism), so
     `φ(d) · #{a : d ∣ (a − 1).val} = φ(d) · |ker| = φ(n)`.

4. **Collapse.**  Every divisor `d ∣ n` contributes exactly `φ(n)`, hence
     `LHS = ∑_{d ∣ n} φ(n) = φ(n) · d(n)`.

This is genuinely new relative to Mathlib, which has the totient and the
`unitsMap` reduction but **not** Menon's identity.

## Summary Statistics

- Sorries: 0
- Axioms: `propext`, `Classical.choice`, `Quot.sound` (standard)
-/

open Finset

namespace EulerTotientOQ10

/-- **Divisor expansion of the gcd.**  For `n ≠ 0`,
`gcd v n = ∑_{d ∣ n} (if d ∣ v then φ d else 0)`. -/
theorem gcd_eq_sum_totient (v : ℕ) {n : ℕ} (hn : n ≠ 0) :
    Nat.gcd v n = ∑ d ∈ n.divisors, (if d ∣ v then Nat.totient d else 0) := by
  have hgne : Nat.gcd v n ≠ 0 := (Nat.gcd_pos_iff.mpr (Or.inr (Nat.pos_of_ne_zero hn))).ne'
  have hgcd : (Nat.gcd v n).divisors = n.divisors.filter (· ∣ v) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hv, hnn⟩, -⟩
      exact ⟨⟨hnn, hn⟩, hv⟩
    · rintro ⟨⟨hnn, -⟩, hv⟩
      exact ⟨⟨hv, hnn⟩, hgne⟩
  calc Nat.gcd v n
      = (Nat.gcd v n).divisors.sum Nat.totient := (Nat.sum_totient _).symm
    _ = ∑ d ∈ n.divisors.filter (· ∣ v), Nat.totient d := by rw [hgcd]
    _ = ∑ d ∈ n.divisors, (if d ∣ v then Nat.totient d else 0) := by
          rw [Finset.sum_filter]

/-- **The reduction-to-`1` criterion.**  A unit `a` of `ℤ/nℤ` reduces to `1` in
`(ℤ/dℤ)ˣ` exactly when `d` divides the natural representative of `a − 1`. -/
theorem dvd_val_sub_one_iff {n : ℕ} [NeZero n] {d : ℕ} (hd : d ∣ n)
    (a : (ZMod n)ˣ) :
    d ∣ ((a : ZMod n) - 1).val ↔ ZMod.unitsMap hd a = 1 := by
  have cast_eq : ∀ i : ZMod n, ((i.val : ℕ) : ZMod d) = ZMod.castHom hd (ZMod d) i := by
    intro i
    rw [ZMod.natCast_val, ZMod.castHom_apply]
  rw [← ZMod.natCast_eq_zero_iff, cast_eq, map_sub, map_one, sub_eq_zero,
      Units.ext_iff, ZMod.unitsMap_val, Units.val_one, ZMod.castHom_apply]

/-- **Fibre count.**  For `d ∣ n`, the number of units of `ℤ/nℤ` congruent to `1`
modulo `d`, weighted by `φ(d)`, is exactly `φ(n)`. -/
theorem totient_mul_fiber_card {n : ℕ} [NeZero n] {d : ℕ} (hd : d ∣ n)
    [DecidablePred (fun a : (ZMod n)ˣ => d ∣ ((a : ZMod n) - 1).val)] :
    (Finset.univ.filter
      (fun a : (ZMod n)ˣ => d ∣ ((a : ZMod n) - 1).val)).card * Nat.totient d
      = Nat.totient n := by
  have hdne : d ≠ 0 := fun h => (NeZero.ne n) (Nat.eq_zero_of_zero_dvd (h ▸ hd))
  have : NeZero d := ⟨hdne⟩
  classical
  -- The fibre is the kernel of the (surjective) reduction homomorphism.
  have hfilter : (Finset.univ.filter
      (fun a : (ZMod n)ˣ => d ∣ ((a : ZMod n) - 1).val))
      = Finset.univ.filter (fun a : (ZMod n)ˣ => a ∈ (ZMod.unitsMap hd).ker) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_ker,
      dvd_val_sub_one_iff hd a]
  rw [hfilter]
  have hcard : (Finset.univ.filter (fun a : (ZMod n)ˣ => a ∈ (ZMod.unitsMap hd).ker)).card
      = Nat.card (ZMod.unitsMap hd).ker := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_subtype _).symm
  rw [hcard]
  -- |G| = |H| * |ker| for the surjective reduction map.
  have hsurj := ZMod.unitsMap_surjective (m := n) hd
  have key := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZMod.unitsMap hd).ker
  rw [Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (ZMod.unitsMap hd) hsurj).toEquiv] at key
  have hn' : Nat.card (ZMod n)ˣ = Nat.totient n := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hd' : Nat.card (ZMod d)ˣ = Nat.totient d := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  rw [hn', hd'] at key
  -- key : φ n = φ d * Nat.card ker ; goal : Nat.card ker * φ d = φ n
  rw [key, mul_comm]

/-- **Menon's identity.**  Summing `gcd(k − 1, n)` over the units `k` of `ℤ/nℤ`
yields `φ(n) · d(n)`. -/
theorem menon_identity (n : ℕ) [NeZero n] :
    ∑ a : (ZMod n)ˣ, Nat.gcd (((a : ZMod n) - 1).val) n
      = Nat.totient n * n.divisors.card := by
  have hn : n ≠ 0 := NeZero.ne n
  classical
  calc ∑ a : (ZMod n)ˣ, Nat.gcd (((a : ZMod n) - 1).val) n
      = ∑ a : (ZMod n)ˣ, ∑ d ∈ n.divisors,
          (if d ∣ ((a : ZMod n) - 1).val then Nat.totient d else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        exact gcd_eq_sum_totient _ hn
    _ = ∑ d ∈ n.divisors, ∑ a : (ZMod n)ˣ,
          (if d ∣ ((a : ZMod n) - 1).val then Nat.totient d else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ n.divisors, Nat.totient n := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdn : d ∣ n := (Nat.mem_divisors.mp hd).1
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        exact totient_mul_fiber_card hdn
    _ = Nat.totient n * n.divisors.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Worked example (small case) -/

-- `n = 6`: units are `{1,5}`; `gcd(0,6)+gcd(4,6) = 6+2 = 8 = φ(6)·d(6) = 2·4`.
example : ∑ a : (ZMod 6)ˣ, Nat.gcd (((a : ZMod 6) - 1).val) 6
    = Nat.totient 6 * (Nat.divisors 6).card := menon_identity 6

end EulerTotientOQ10
