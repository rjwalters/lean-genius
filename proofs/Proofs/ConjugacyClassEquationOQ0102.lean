import Mathlib
import Proofs.ConjugacyClassEquationOQ01

/-!
# Finite `p`-groups have nontrivial center, via the class equation

This file answers the second open question recorded on the parent entry
`conjugacy-class-equation-oq-01` (Proofs/ConjugacyClassEquationOQ01.lean):

> Deduce that a nontrivial finite `p`-group has nontrivial center by combining
> per-class divisibility with the observation that every noncentral class size
> is a positive power of `p`.

The argument is the **class-equation route**, which is genuinely different from the
proof Mathlib ships (`IsPGroup.center_nontrivial`, which counts the fixed points of
the conjugation action via `IsPGroup.card_modEq_card_fixedPoints`).  Here we instead:

1. lift the parent's per-class divisibility `|class(g)| ∣ |G|` from chosen
   representatives to arbitrary conjugacy classes (`conjClass_carrier_card_dvd_card`);
2. observe that for a `p`-group `|G| = pⁿ`, so every conjugacy class size is a power
   of `p`, and a *noncentral* class — one whose carrier has more than one element —
   has size a **positive** power of `p`, hence is divisible by `p`
   (`noncentral_class_card_eq_prime_pow`);
3. feed this into Mathlib's numeric class equation
   `Group.nat_card_center_add_sum_card_noncenter_eq_card`,

       |Z(G)| + Σ_{noncentral classes} |class| = |G|,

   to get `p ∣ |Z(G)|` (both `|G|` and the noncentral sum are divisible by `p`);
4. conclude `1 < |Z(G)|`, i.e. `Z(G)` is nontrivial (`center_nontrivial_of_isPGroup`).

Everything is `0`-axiom and builds on the parent's `conjClass_card_dvd_card`.
Mathlib already knows the headline theorem; the content here is the explicit
class-equation derivation requested by the open question, with the intermediate
"noncentral classes have size a positive power of `p`" stated as its own result.
-/

open MulAction ConjClasses Subgroup

namespace ConjugacyClassEquationOQ0102

variable {G : Type*} [Group G]

/-- **Per-class divisibility for arbitrary conjugacy classes.** The cardinality of any
conjugacy class `x : ConjClasses G` divides the order of the group.  This lifts the
parent's `conjClass_card_dvd_card`, which is stated for the class of a chosen
representative `g`, to a statement about the quotient `ConjClasses G` directly. -/
theorem conjClass_carrier_card_dvd_card (x : ConjClasses G) :
    Nat.card x.carrier ∣ Nat.card G := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
  exact ConjugacyClassEquationOQ01.conjClass_card_dvd_card g

variable {p : ℕ}

/-- **Noncentral classes of a finite `p`-group have size a positive power of `p`.**
If `G` is a finite `p`-group and `x` is a conjugacy class with more than one element
(i.e. `x ∈ ConjClasses.noncenter G`), then `|x| = p^k` for some `k > 0`; in particular
`p ∣ |x|`.  This is the key arithmetic input to the class equation. -/
theorem noncentral_class_card_eq_prime_pow [Fact p.Prime] [Finite G] (hG : IsPGroup p G)
    {x : ConjClasses G} (hx : x ∈ noncenter G) :
    ∃ k > 0, Nat.card x.carrier = p ^ k := by
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hG
  have hdvd : Nat.card x.carrier ∣ p ^ n := hcard ▸ conjClass_carrier_card_dvd_card x
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  -- a noncentral class carrier is a nontrivial set, so it has more than one element
  have h1lt : 1 < Nat.card x.carrier :=
    Finite.one_lt_card_iff_nontrivial.mpr
      (Set.nontrivial_coe_sort.mpr ((mem_noncenter x).mp hx))
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hk, pow_zero] at h1lt
    exact absurd h1lt (lt_irrefl 1)
  · exact hk0

/-- **A nontrivial finite `p`-group has nontrivial center** (class-equation proof).

`p` divides the order `|G| = pⁿ` (with `n > 0` since `G` is nontrivial) and divides the
total size of the noncentral conjugacy classes (each summand is a positive power of `p`),
so by the class equation `|Z(G)| + Σ = |G|` it divides `|Z(G)|`.  Since `Z(G)` is a
nonempty finite set with `p ∣ |Z(G)|` and `p ≥ 2`, we get `1 < |Z(G)|`. -/
theorem center_nontrivial_of_isPGroup [Fact p.Prime] [Finite G] [Nontrivial G]
    (hG : IsPGroup p G) : Nontrivial (Subgroup.center G) := by
  classical
  have hp : p.Prime := Fact.out
  -- `p ∣ |G|`, since `|G| = pⁿ` with `n > 0`
  obtain ⟨n, hn0, hcard⟩ := hG.nontrivial_iff_card.mp ‹Nontrivial G›
  have hpG : p ∣ Nat.card G := hcard ▸ dvd_pow_self p hn0.ne'
  -- `p` divides the sum of the noncentral class sizes
  have hpsum : p ∣ ∑ᶠ x ∈ noncenter G, Nat.card x.carrier := by
    have key : ∀ x ∈ noncenter G, p ∣ Nat.card x.carrier := by
      intro x hx
      obtain ⟨k, hk0, hk⟩ := noncentral_class_card_eq_prime_pow hG hx
      exact hk ▸ dvd_pow_self p hk0.ne'
    have hfin : (noncenter G).Finite := Set.toFinite _
    have hrw : (∑ᶠ x ∈ noncenter G, Nat.card x.carrier)
        = ∑ x ∈ hfin.toFinset, Nat.card x.carrier := by
      rw [← finsum_mem_coe_finset, hfin.coe_toFinset]
    rw [hrw]
    exact Finset.dvd_sum fun x hx => key x (hfin.mem_toFinset.mp hx)
  -- the class equation: `|Z(G)| + Σ = |G|`
  have heq := Group.nat_card_center_add_sum_card_noncenter_eq_card G
  -- therefore `p ∣ |Z(G)|`
  have hcenter_eq : Nat.card (Subgroup.center G)
      = Nat.card G - ∑ᶠ x ∈ noncenter G, Nat.card x.carrier := by omega
  have hpc : p ∣ Nat.card (Subgroup.center G) := hcenter_eq ▸ Nat.dvd_sub hpG hpsum
  -- a nonempty finite set with `p ∣ card` and `p ≥ 2` has `> 1` element
  have hpos : 0 < Nat.card (Subgroup.center G) := Finite.card_pos
  have h1lt : 1 < Nat.card (Subgroup.center G) :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hpc)
  exact Finite.one_lt_card_iff_nontrivial.mp h1lt

/-- Concrete instance: apply the theorem to the order-`4` `2`-group
`Multiplicative (ZMod 4)`.  Its center is nontrivial (in fact the group is abelian, so
the center is everything — but the point is that the class-equation theorem fires). -/
example : Nontrivial (Subgroup.center (Multiplicative (ZMod 4))) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Nontrivial (ZMod 4) := ⟨0, 1, by decide⟩
  haveI : Nontrivial (Multiplicative (ZMod 4)) := inferInstanceAs (Nontrivial (ZMod 4))
  have hG : IsPGroup 2 (Multiplicative (ZMod 4)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_eq_fintype_card]; decide)
  exact center_nontrivial_of_isPGroup hG

end ConjugacyClassEquationOQ0102
