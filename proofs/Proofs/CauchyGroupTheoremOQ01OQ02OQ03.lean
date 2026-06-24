import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic
import Proofs.CauchyGroupTheoremOQ01OQ02

/-
# Squarefree group order forces every Sylow subgroup cyclic of prime order

## What This Proves

The parent file `CauchyGroupTheoremOQ01OQ02` climbs the Cauchy → Sylow ladder,
extracting the maximal `p`-power subgroup of order `p ^ (multiplicity of p in |G|)`
and pinning down the `S₃` picture: order `6 = 2 · 3` gives a Sylow `2`-subgroup
of order `2` and a Sylow `3`-subgroup of order `3`. Its closing open question
asks **how sharp the nontriviality boundary is in the non-prime-power direction**:

> "a packaged statement that `|G|` squarefree forces every Sylow subgroup to be
> cyclic of prime order, recovering this entry's `S₃` picture in general."

This file answers exactly that. When `|G|` is **squarefree** the entire Sylow
structure collapses to the simplest possible shape:

* **The multiplicity is `1`** (`factorization_eq_one_of_squarefree_dvd`). For a
  prime `p ∣ |G|`, squarefreeness forces `v_p(|G|) = 1` — no prime appears to a
  power above one.

* **Every Sylow `p`-subgroup has order exactly `p`**
  (`sylow_card_eq_prime_of_squarefree`). Composing the multiplicity collapse with
  the parent's `Sylow.card_eq_multiplicity` (`|P| = p ^ v_p(|G|)`) gives
  `|P| = p¹ = p`. The "merely large `p`-subgroup" of the general theory becomes a
  group of prime order.

* **Hence every Sylow `p`-subgroup is cyclic of prime order**
  (`sylow_isCyclic_of_squarefree_dvd`). A group of prime order is cyclic
  (`isCyclic_of_prime_card`), so each Sylow subgroup is `ℤ/pℤ`.

* **The full dichotomy** (`sylow_card_eq_one_or_prime_of_squarefree`). For *any*
  prime `p`, a Sylow `p`-subgroup has order `1` (when `p ∤ |G|`) or `p` (when
  `p ∣ |G|`) — never a higher power. The boundary of `sylow_nontrivial_iff_dvd`
  becomes razor-sharp.

* **Every Sylow subgroup is cyclic, no hypothesis on `p`**
  (`sylow_isCyclic_of_squarefree`). Trivial Sylow subgroups (for `p ∤ |G|`) are
  cyclic by `isCyclic_of_subsingleton`; the rest are cyclic of prime order. So in
  a squarefree-order group *every* Sylow subgroup is cyclic.

* **The `S₃` picture in general** (`sylow2_perm_fin3_cyclic`,
  `sylow3_perm_fin3_cyclic`). Specializing to `S₃` (`|S₃| = 6`, squarefree)
  recovers the parent's concrete numbers as instances of the general theorem:
  the Sylow `2`-subgroup is cyclic of order `2`, the Sylow `3`-subgroup cyclic
  of order `3`.

## Context

A finite group whose order is squarefree is *metacyclic* (indeed supersolvable),
and the first structural fact in that classification is precisely the one proved
here: every Sylow subgroup is cyclic of prime order. The deeper statement —
that the whole group is a semidirect product of cyclic groups, classified by
Hölder — builds on this collapse of the Sylow data. Mathlib has the existence
and order of Sylow subgroups (`Sylow.card_eq_multiplicity`) and the squarefree
factorization collapse (`Nat.factorization_eq_one_of_squarefree`), but records
none of the packaged "squarefree ⟹ cyclic Sylow" corollary. This file supplies
it, completing the Cauchy → Sylow → squarefree arc of the entry. Everything is
`0`-axiom, deriving from Mathlib's Sylow API and elementary factorization facts.
-/

open Subgroup

namespace CauchyGroupTheoremOQ01OQ02OQ03

variable {G : Type*} [Group G] [Finite G]

/-! ### The multiplicity collapse -/

omit [Group G] [Finite G] in
/-- **Squarefree order kills multiplicities.** If `|G|` is squarefree and a prime
`p` divides it, then the `p`-adic valuation of `|G|` is exactly `1`: no prime can
appear to a power above one in a squarefree number. This is the engine that turns
the Sylow `p`-subgroup (order `p ^ v_p(|G|)`) into a group of prime order. -/
theorem factorization_eq_one_of_squarefree_dvd
    (hsf : Squarefree (Nat.card G)) {p : ℕ} (hp : p.Prime) (hpd : p ∣ Nat.card G) :
    (Nat.card G).factorization p = 1 :=
  Nat.factorization_eq_one_of_squarefree hsf hp hpd

/-! ### Every Sylow subgroup of prime order -/

/-- **Sylow subgroups have prime order under squarefreeness.** If `|G|` is
squarefree and `p ∣ |G|`, then every Sylow `p`-subgroup `P` has order exactly
`p`. Proof: `|P| = p ^ v_p(|G|)` (parent's `Sylow.card_eq_multiplicity`) and
`v_p(|G|) = 1`, so `|P| = p¹ = p`. -/
theorem sylow_card_eq_prime_of_squarefree
    (hsf : Squarefree (Nat.card G)) (p : ℕ) [Fact p.Prime]
    (hpd : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card P = p := by
  rw [P.card_eq_multiplicity,
    Nat.factorization_eq_one_of_squarefree hsf Fact.out hpd, pow_one]

/-- **Cyclic of prime order.** Under squarefreeness, every Sylow `p`-subgroup with
`p ∣ |G|` is cyclic — being a group of prime order `p`, it is `ℤ/pℤ`. This is the
literal statement requested by the parent's open question. -/
theorem sylow_isCyclic_of_squarefree_dvd
    (hsf : Squarefree (Nat.card G)) (p : ℕ) [Fact p.Prime]
    (hpd : p ∣ Nat.card G) (P : Sylow p G) :
    IsCyclic P :=
  isCyclic_of_prime_card (sylow_card_eq_prime_of_squarefree hsf p hpd P)

/-! ### The sharp dichotomy and full cyclicity -/

/-- **The order dichotomy.** Under squarefreeness, a Sylow `p`-subgroup has order
`1` (precisely when `p ∤ |G|`) or `p` (precisely when `p ∣ |G|`) — never a higher
power of `p`. This makes the parent's `sylow_nontrivial_iff_dvd` boundary razor
sharp: the only nontrivial possibility is prime order. -/
theorem sylow_card_eq_one_or_prime_of_squarefree
    (hsf : Squarefree (Nat.card G)) (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Nat.card P = 1 ∨ Nat.card P = p := by
  by_cases hpd : p ∣ Nat.card G
  · exact Or.inr (sylow_card_eq_prime_of_squarefree hsf p hpd P)
  · refine Or.inl ?_
    rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpd, pow_zero]

/-- **Every Sylow subgroup is cyclic** — no hypothesis on `p`. In a squarefree
order group, a Sylow `p`-subgroup is either trivial (`p ∤ |G|`, cyclic by
`isCyclic_of_subsingleton`) or cyclic of prime order (`p ∣ |G|`). Either way it is
cyclic. -/
theorem sylow_isCyclic_of_squarefree
    (hsf : Squarefree (Nat.card G)) (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    IsCyclic P := by
  by_cases hpd : p ∣ Nat.card G
  · exact sylow_isCyclic_of_squarefree_dvd hsf p hpd P
  · have hcard : Nat.card P = 1 := by
      rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hpd, pow_zero]
    have hss : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact @isCyclic_of_subsingleton _ _ hss

/-- **Packaged conclusion.** The complete answer to the parent's open question:
if `|G|` is squarefree and `p ∣ |G|`, then every Sylow `p`-subgroup is
simultaneously of order exactly `p` and cyclic — i.e. cyclic of prime order. -/
theorem sylow_cyclic_of_prime_order_of_squarefree
    (hsf : Squarefree (Nat.card G)) (p : ℕ) [Fact p.Prime]
    (hpd : p ∣ Nat.card G) (P : Sylow p G) :
    Nat.card P = p ∧ IsCyclic P :=
  ⟨sylow_card_eq_prime_of_squarefree hsf p hpd P,
    sylow_isCyclic_of_squarefree_dvd hsf p hpd P⟩

/-! ### Recovering the `S₃` picture in general -/

/-- `|S₃| = 6` is squarefree, so the general theorem applies to the symmetric
group on three letters. -/
theorem squarefree_card_perm_fin3 :
    Squarefree (Nat.card (Equiv.Perm (Fin 3))) := by
  rw [CauchyGroupTheoremOQ01OQ02.card_perm_fin3, show (6 : ℕ) = 2 * 3 from rfl,
    Nat.squarefree_mul_iff]
  exact ⟨by norm_num, Nat.prime_two.prime.squarefree, Nat.prime_three.prime.squarefree⟩

/-- **Sylow `2`-subgroup of `S₃`, recovered from the general theorem.** Every
Sylow `2`-subgroup of `S₃` is cyclic of order `2` — the parent's concrete number
`2`, now an instance of `sylow_cyclic_of_prime_order_of_squarefree`. -/
theorem sylow2_perm_fin3_cyclic (P : Sylow 2 (Equiv.Perm (Fin 3))) :
    Nat.card P = 2 ∧ IsCyclic P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpd : (2 : ℕ) ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [CauchyGroupTheoremOQ01OQ02.card_perm_fin3]; norm_num
  exact sylow_cyclic_of_prime_order_of_squarefree squarefree_card_perm_fin3 2 hpd P

/-- **Sylow `3`-subgroup of `S₃`, recovered from the general theorem.** Every
Sylow `3`-subgroup of `S₃` is cyclic of order `3` — the parent's concrete number
`3`, now an instance of `sylow_cyclic_of_prime_order_of_squarefree`. -/
theorem sylow3_perm_fin3_cyclic (P : Sylow 3 (Equiv.Perm (Fin 3))) :
    Nat.card P = 3 ∧ IsCyclic P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpd : (3 : ℕ) ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [CauchyGroupTheoremOQ01OQ02.card_perm_fin3]; norm_num
  exact sylow_cyclic_of_prime_order_of_squarefree squarefree_card_perm_fin3 3 hpd P

end CauchyGroupTheoremOQ01OQ02OQ03
