import Mathlib
import Proofs.ConjugacyClassEquationOQ01

/-!
# The numeric class equation in centralizer-index form, and the `p`-group center

Building on the per-class divisibility identity
`conjClass_card_eq_index_centralizer` (which says `|class(g)| = [G : C_G(g)]`), this
file assembles the **full numeric class equation** and applies it to recover the
classical theorem that a finite `p`-group has a nontrivial center.

## Main results

* `classEquation_centralizer_index` :
  `|Z(G)| + ∑_{x ∈ noncenter} [G : C_G(x.out)] = |G|`.
  The cardinality of the center plus the sum, over the noncentral conjugacy classes,
  of the centralizer indices of chosen representatives, equals the group order.  This
  is the standard "numeric class equation" with every noncentral summand written as a
  centralizer index, obtained from Mathlib's
  `Group.nat_card_center_add_sum_card_noncenter_eq_card` by rewriting each class size
  via the per-class identity.

* `prime_dvd_card_center` :
  for a nontrivial finite `p`-group, `p ∣ |Z(G)|`.

* `pgroup_center_nontrivial` :
  a nontrivial finite `p`-group has nontrivial center, `Nontrivial (Z(G))`.

The divisibility/center results are the textbook *class-equation* derivation: `p`
divides `|G|` and divides every noncentral class size `[G : C_G(g_i)]` (a divisor of
`|G| = p^n` that exceeds `1`, hence a positive power of `p`), so `p` divides the
remaining summand `|Z(G)|`; since `|Z(G)| ≥ 1`, this forces `|Z(G)| > 1`.

Mathlib proves `IsPGroup.center_nontrivial` instead via a *fixed-point* (Burnside)
counting argument; the proof here is the independent class-equation route, made
possible by the centralizer-index packaging of the class equation.
-/

open MulAction ConjAct ConjClasses

namespace ConjugacyClassEquationOQ01OQ01

variable {G : Type*} [Group G]

/-- The conjugacy class of a chosen representative `x.out` is `x` itself. -/
theorem mk_out (x : ConjClasses G) : ConjClasses.mk x.out = x := by
  rw [← ConjClasses.quotient_mk_eq_mk]; exact Quotient.out_eq x

/-- For every conjugacy class `x`, the size of its carrier equals the index of the
centralizer of a chosen representative `x.out`: `|x| = [G : C_G(x.out)]`. This is the
per-class identity `conjClass_card_eq_index_centralizer` transported along `mk x.out = x`. -/
theorem card_carrier_eq_index (x : ConjClasses G) :
    Nat.card x.carrier =
      (Subgroup.centralizer ({ConjAct.toConjAct x.out} : Set (ConjAct G))).index := by
  conv_lhs => rw [← mk_out x]
  exact ConjugacyClassEquationOQ01.conjClass_card_eq_index_centralizer x.out

/-- **The numeric class equation in centralizer-index form.** The order of the center
plus the sum, over the noncentral conjugacy classes, of the centralizer indices
`[G : C_G(x.out)]` of representatives, equals the group order:
`|Z(G)| + ∑_{x ∈ noncenter} [G : C_G(x.out)] = |G|`. -/
theorem classEquation_centralizer_index [Finite G] :
    Nat.card (Subgroup.center G) +
        ∑ᶠ x ∈ ConjClasses.noncenter G,
          (Subgroup.centralizer ({ConjAct.toConjAct x.out} : Set (ConjAct G))).index =
      Nat.card G := by
  rw [← Group.nat_card_center_add_sum_card_noncenter_eq_card G]
  congr 1
  exact finsum_mem_congr rfl fun x _ => (card_carrier_eq_index x).symm

/-- For a nontrivial finite `p`-group, the prime `p` divides the order of the center.

This is the class-equation argument: `p ∣ |G|`, and `p` divides each noncentral class
size (a divisor of `|G| = p^n` greater than `1`), so by the class equation
`|Z(G)| + ∑ |class| = |G|` we get `p ∣ |Z(G)|`. -/
theorem prime_dvd_card_center {p : ℕ} [hp : Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : p ∣ Nat.card (Subgroup.center G) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : ∀ x : ConjClasses G, Fintype x.carrier := fun _ => Fintype.ofFinite _
  haveI : Fintype (Subgroup.center G) := Fintype.ofFinite _
  haveI : Fintype (ConjClasses.noncenter G) := Fintype.ofFinite _
  -- `p ∣ |G|`, using `|G| = p ^ n` with `n > 0`.
  obtain ⟨n, hn0, hcard⟩ := hG.nontrivial_iff_card.mp ‹Nontrivial G›
  have hpG : p ∣ Nat.card G := by rw [hcard]; exact dvd_pow_self p hn0.ne'
  have hpG' : p ∣ Fintype.card G := by rwa [← Nat.card_eq_fintype_card]
  -- The class equation in Mathlib's `Fintype` form.
  have hCE := Group.card_center_add_sum_card_noncenter_eq_card G
  -- `p` divides every noncentral class size, hence the whole sum.
  have hsum : p ∣ ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card := by
    apply Finset.dvd_sum
    intro x hx
    rw [Set.mem_toFinset, ConjClasses.mem_noncenter] at hx
    -- rewrite the summand as `Nat.card x.carrier`
    have hc : x.carrier.toFinset.card = Nat.card x.carrier := by
      rw [Set.toFinset_card, Nat.card_eq_fintype_card]
    -- the class size divides `|G| = p ^ n`
    have hdvd : Nat.card x.carrier ∣ Nat.card G := by
      rw [← mk_out x]; exact ConjugacyClassEquationOQ01.conjClass_card_dvd_card x.out
    -- and exceeds `1` because the class is noncentral
    have hgt : 1 < Nat.card x.carrier :=
      Finite.one_lt_card_iff_nontrivial.mpr (Set.nontrivial_coe_sort.mpr hx)
    -- a divisor of `p ^ n` exceeding `1` is divisible by `p`
    rw [hc]
    rw [hcard] at hdvd
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk, hk0, pow_zero] at hgt; exact absurd hgt (lt_irrefl 1)
    · rw [hk]; exact dvd_pow_self p hk0.ne'
  -- combine: `center = |G| - sum`, both divisible by `p`.
  have hsplit : Fintype.card (Subgroup.center G) =
      Fintype.card G - ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card := by
    omega
  have : p ∣ Fintype.card (Subgroup.center G) := by
    rw [hsplit]; exact Nat.dvd_sub hpG' hsum
  rwa [Nat.card_eq_fintype_card]

/-- **A nontrivial finite `p`-group has nontrivial center** (class-equation proof).
Recovered from `prime_dvd_card_center`: since `p ∣ |Z(G)|` and `|Z(G)| ≥ 1`, the prime
`p` forces `|Z(G)| > 1`, i.e. `Z(G)` is nontrivial. -/
theorem pgroup_center_nontrivial {p : ℕ} [hp : Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  have hdvd := prime_dvd_card_center hG
  have hpos : 0 < Nat.card (Subgroup.center G) := Nat.card_pos
  have hple : p ≤ Nat.card (Subgroup.center G) := Nat.le_of_dvd hpos hdvd
  have : 1 < Nat.card (Subgroup.center G) := lt_of_lt_of_le hp.out.one_lt hple
  exact Finite.one_lt_card_iff_nontrivial.mp this

/-- Concrete instance: the center theorem applied to the smallest nontrivial `p`-group,
the cyclic group of order `2` (`Multiplicative (ZMod 2)`, a `2`-group), yields a
nontrivial center. -/
example : Nontrivial (Subgroup.center (Multiplicative (ZMod 2))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pgroup_center_nontrivial (p := 2)
    (IsPGroup.of_card (n := 1) (by simp [Nat.card_eq_fintype_card]))

end ConjugacyClassEquationOQ01OQ01
