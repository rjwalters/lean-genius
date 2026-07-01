import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite

/-
# Groups of Order p² are Abelian — the Full Structural Dichotomy

A classical consequence of the class equation is that every finite `p`-group has a
nontrivial centre, and hence that any group of order `p²` is **abelian**.  Mathlib
already packages the abelian conclusion as `IsPGroup.commutative_of_card_eq_prime_sq`,
so restating it alone would add nothing.

This file goes one step further and pins down the *isomorphism type*.  A finite abelian
group of order `p²` is, by the structure theorem, either the cyclic group `ℤ/p²` or the
elementary abelian group `(ℤ/p)²`.  The purely group-theoretic content separating these
two cases — which Mathlib does **not** package — is a clean dichotomy on element orders:

> A group of order `p²` is **either cyclic, or every element `g` satisfies `g ^ p = 1`**
> (equivalently, its exponent is exactly `p`).

The mechanism is Lagrange's theorem: the order of any element divides `p²`, so it is one
of `1, p, p²`.  If some element attains order `p²` the group is cyclic; otherwise every
element has order dividing `p`.  Combined with the abelian result this is precisely the
`ℤ/p²`  vs.  `(ℤ/p)²`  classification.

## Main results

* `mul_comm_of_card_eq_prime_sq` — groups of order `p²` are abelian (via Mathlib).
* `isCyclic_or_pow_prime_eq_one` — the structural dichotomy: cyclic, or exponent divides `p`.
* `isCyclic_iff_exists_orderOf_eq` — cyclic ⇔ an element of maximal order `p²` exists.
* `exponent_eq_prime_of_not_isCyclic` — the non-cyclic case has exponent exactly `p`
  (the elementary-abelian branch).

All results are fully machine-checked with no `sorry`, no `axiom`, and no `native_decide`;
they depend only on Mathlib.
-/

namespace SylowTheoremOQ05

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

/-- **Groups of order `p²` are abelian.**  Every finite `p`-group has a nontrivial centre
`Z`; for order `p²` this forces `G/Z` to be cyclic, and a group whose central quotient is
cyclic is abelian.  Mathlib packages the whole chain as
`IsPGroup.commutative_of_card_eq_prime_sq`; we expose it here as the base of the
classification. -/
theorem mul_comm_of_card_eq_prime_sq [Fact p.Prime] (hG : Nat.card G = p ^ 2) (a b : G) :
    a * b = b * a :=
  IsPGroup.commutative_of_card_eq_prime_sq hG a b

/-- **The structural dichotomy for order `p²`.**  A group of order `p²` is either cyclic,
or every element satisfies `g ^ p = 1` (its exponent divides `p`).

Proof: by Lagrange the order of any `g` divides `p²`, hence equals `p ^ m` with `m ≤ 2`.
If `m = 2` then `orderOf g = Nat.card G`, so `g` generates `G` and `G` is cyclic.  In the
remaining cases `m ≤ 1`, so `orderOf g ∣ p` and therefore `g ^ p = 1`. -/
theorem isCyclic_or_pow_prime_eq_one [Fact p.Prime] (hG : Nat.card G = p ^ 2) :
    IsCyclic G ∨ ∀ g : G, g ^ p = 1 := by
  have hp : p.Prime := Fact.out
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero 2 hp.ne_zero)
  by_cases hcyc : IsCyclic G
  · exact Or.inl hcyc
  · refine Or.inr fun g => ?_
    have hdvd : orderOf g ∣ p ^ 2 := hG ▸ orderOf_dvd_natCard g
    obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · -- `m ≤ 1`, so `orderOf g ∣ p`.
      have hmle : m ≤ 1 := by omega
      have hop : orderOf g ∣ p := by rw [hmeq]; simpa using pow_dvd_pow p hmle
      exact orderOf_dvd_iff_pow_eq_one.1 hop
    · -- `m = 2`, so `g` has maximal order and `G` is cyclic — contradicting `hcyc`.
      have hm2 : m = 2 := le_antisymm hm hge
      exact absurd (isCyclic_of_orderOf_eq_card g (by rw [hmeq, hm2, hG])) hcyc

/-- **Cyclic ⇔ an element of maximal order.**  A group of order `p²` is cyclic exactly when
some element attains the full order `p²`. -/
theorem isCyclic_iff_exists_orderOf_eq [Fact p.Prime] (hG : Nat.card G = p ^ 2) :
    IsCyclic G ↔ ∃ g : G, orderOf g = p ^ 2 := by
  have hp : p.Prime := Fact.out
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hG]; exact pow_ne_zero 2 hp.ne_zero)
  constructor
  · intro h
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 h
    exact ⟨g, by rw [hg, hG]⟩
  · rintro ⟨g, hg⟩
    exact isCyclic_of_orderOf_eq_card g (by rw [hg, hG])

/-- **The elementary-abelian branch.**  If a group of order `p²` is *not* cyclic, then its
exponent is exactly `p`: every element satisfies `g ^ p = 1`, and `p` is genuinely
attained (the exponent is not `1`, since the group is nontrivial).  Together with
`mul_comm_of_card_eq_prime_sq` this identifies the non-cyclic case as `(ℤ/p)²`. -/
theorem exponent_eq_prime_of_not_isCyclic [Fact p.Prime] (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) : Monoid.exponent G = p := by
  have hp : p.Prime := Fact.out
  have hall : ∀ g : G, g ^ p = 1 := (isCyclic_or_pow_prime_eq_one hG).resolve_left hnc
  have hdvd : Monoid.exponent G ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hall
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | hpp
  · -- `exponent = 1` would make `G` a subsingleton, contradicting `Nat.card G = p² > 1`.
    have hss : Subsingleton G := Monoid.exp_eq_one_iff.1 h1
    have hc1 : Nat.card G = 1 := Nat.card_eq_one_iff_unique.2 ⟨hss, ⟨1⟩⟩
    rw [hG] at hc1
    nlinarith [hc1, hp.two_le]
  · exact hpp

end SylowTheoremOQ05
