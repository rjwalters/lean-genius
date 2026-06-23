import Mathlib
import Proofs.ConjugacyClassEquationOQ01

/-!
# The numeric class equation assembled from centralizer indices

The parent development (`Proofs.ConjugacyClassEquationOQ01`) proves the *per-class*
form of the class equation: for a single element `g` of a finite group `G`, the size of
its conjugacy class equals the index of its centralizer,
`conjClass_card_eq_index_centralizer : |class(g)| = [G : C_G(g)]`.

Mathlib already provides the *summed* class equation in cardinality form,
`Group.nat_card_center_add_sum_card_noncenter_eq_card`:
`|Z(G)| + ∑ᶠ x ∈ noncenter G, |x.carrier| = |G|`,
where the sum runs over the nontrivial (noncentral) conjugacy classes.

This file assembles the two into the **textbook numeric class equation**

`|G| = |Z(G)| + ∑_{noncentral classes} [G : C_G(g_i)]`,

i.e. every noncentral class contributes the *index of the centralizer* of a chosen
representative `g_i = x.out`.  This is the form in which the class equation is actually
used in practice (counting arguments, `p`-group theorems), and it is precisely the shape
that Mathlib's cardinality statement does **not** package.

As the standard application we extract the arithmetic engine behind the class equation:

* `prime_dvd_card_center_of_dvd_indices` : if a prime (indeed any `p : ℕ`) divides `|G|`
  and divides every noncentral centralizer index `[G : C_G(g_i)]`, then it divides the
  order of the center `|Z(G)|`.

This is exactly the step that yields "a nontrivial finite `p`-group has nontrivial
center": for a `p`-group every noncentral index is a positive power of `p`, so `p ∣ |Z(G)|`
and the center cannot be trivial.

The representative of a class `x : ConjClasses G` is `Quotient.out x`, which satisfies
`ConjClasses.mk (Quotient.out x) = x` (`Quotient.out_eq`); this lets us transport the
per-class identity to each summand.
-/

open MulAction Subgroup ConjAct ConjClasses

namespace ConjugacyClassEquationOQ01OQ01

open ConjugacyClassEquationOQ01

variable {G : Type*} [Group G]

/-- The centralizer index of the chosen representative of a conjugacy class equals the
cardinality of that class.  This is the per-class identity
`conjClass_card_eq_index_centralizer`, transported along `ConjClasses.mk (x.out) = x`. -/
theorem index_centralizer_out_eq_card_carrier (x : ConjClasses G) :
    (Subgroup.centralizer ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index =
      Nat.card x.carrier := by
  have hmk : ConjClasses.mk (Quotient.out x) = x := Quotient.out_eq x
  rw [← conjClass_card_eq_index_centralizer (Quotient.out x), hmk]

/-- **The numeric class equation, centralizer-index form.**

`|G| = |Z(G)| + ∑_{noncentral classes x} [G : C_G(x.out)]`,

the sum running over the nontrivial conjugacy classes, each contributing the index of the
centralizer of a chosen representative `x.out`.  Assembled from the per-class identity
`conjClass_card_eq_index_centralizer` and Mathlib's summed cardinality class equation. -/
theorem card_center_add_sum_index_eq_card [Finite G] :
    Nat.card (Subgroup.center G) +
        ∑ᶠ x ∈ ConjClasses.noncenter G,
          (Subgroup.centralizer ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index =
      Nat.card G := by
  have key :
      (∑ᶠ x ∈ ConjClasses.noncenter G,
          (Subgroup.centralizer ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index) =
        ∑ᶠ x ∈ ConjClasses.noncenter G, Nat.card x.carrier :=
    finsum_mem_congr rfl (fun x _ => index_centralizer_out_eq_card_carrier x)
  rw [key]
  exact Group.nat_card_center_add_sum_card_noncenter_eq_card G

/-- **The arithmetic engine of the class equation.** If `p : ℕ` divides the group order
`|G|` and divides the centralizer index `[G : C_G(x.out)]` of every noncentral conjugacy
class, then `p` divides the order of the center `|Z(G)|`.

Taking `p` a prime and `G` a nontrivial finite `p`-group, every noncentral index is a
positive power of `p`, so `p ∣ |Z(G)|`: the center of a finite `p`-group is nontrivial. -/
theorem prime_dvd_card_center_of_dvd_indices [Finite G] {p : ℕ}
    (hpG : p ∣ Nat.card G)
    (hidx : ∀ x ∈ ConjClasses.noncenter G,
        p ∣ (Subgroup.centralizer ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index) :
    p ∣ Nat.card (Subgroup.center G) := by
  -- `p` divides the whole noncentral sum, since it divides each term.
  have hfin : (ConjClasses.noncenter G).Finite := Set.toFinite _
  have hsum :
      p ∣ ∑ᶠ x ∈ ConjClasses.noncenter G,
          (Subgroup.centralizer ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine Finset.dvd_sum (fun x hx => hidx x ?_)
    rwa [Set.Finite.mem_toFinset] at hx
  -- From `|Z| + ∑ = |G|` and `p ∣ |G|`, `p ∣ ∑`, conclude `p ∣ |Z|`.
  have heq := card_center_add_sum_index_eq_card (G := G)
  have hcenter :
      Nat.card (Subgroup.center G) =
        Nat.card G -
          ∑ᶠ x ∈ ConjClasses.noncenter G,
            (Subgroup.centralizer
              ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct G))).index :=
    Nat.eq_sub_of_add_eq heq
  rw [hcenter]
  exact Nat.dvd_sub hpG hsum

/-- Concrete instance: in `S₃ = Equiv.Perm (Fin 3)` (order `6`) the numeric class equation
holds — the center has order `1` and the two noncentral classes (the three transpositions
and the two `3`-cycles) have centralizer indices `3` and `2`, summing with the center to `6`. -/
example : Nat.card (Subgroup.center (Equiv.Perm (Fin 3))) +
    ∑ᶠ x ∈ ConjClasses.noncenter (Equiv.Perm (Fin 3)),
      (Subgroup.centralizer
        ({ConjAct.toConjAct (Quotient.out x)} : Set (ConjAct (Equiv.Perm (Fin 3))))).index =
    Nat.card (Equiv.Perm (Fin 3)) :=
  card_center_add_sum_index_eq_card

end ConjugacyClassEquationOQ01OQ01
