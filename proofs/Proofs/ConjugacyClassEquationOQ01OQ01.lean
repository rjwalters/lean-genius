import Mathlib

/-!
# The class equation in index form: `|G| = |Z(G)| + Σ [G : C_G(gᵢ)]`

The parent file `ConjugacyClassEquationOQ01` proved the *per-class* form of the class
equation via orbit–stabilizer for conjugation:

* `|class(g)| = [G : C_G(g)]` — the size of the conjugacy class of `g` is the index of
  its centralizer (`conjClass_card_eq_index_centralizer`).

Mathlib supplies the *summed* class equation in cardinality form
(`Group.nat_card_center_add_sum_card_noncenter_eq_card`):

  `|Z(G)| + Σ_{noncentral classes K} |K| = |G|`.

This file **assembles the standard textbook form** of the class equation by feeding the
per-class index identity into Mathlib's summed equation, replacing each noncentral class
size `|K|` by the centralizer index `[G : C_G(gᵢ)]` of a chosen representative `gᵢ`:

  `|Z(G)| + Σ_{noncentral classes K} [G : C_G(g_K)] = |G|`.

This is the arithmetic engine behind the classical corollaries (e.g. a nontrivial
`p`-group has nontrivial center, since `p ∣ [G : C_G(gᵢ)]` for each noncentral `gᵢ`).
Mathlib packages the cardinality form but not this index form.

We work with `Nat.card` and the finitary sum `∑ᶠ`, so the only typeclass hypothesis is
`[Finite G]`. Representatives are chosen with `ConjClasses.exists_rep`.
-/

open MulAction Subgroup ConjAct

namespace ConjugacyClassEquationOQ01OQ01

variable {G : Type*} [Group G]

/-- **Per-class index identity** (re-derived from the parent file's
`conjClass_card_eq_index_centralizer`). The size of the conjugacy class of `g`
equals the index of its centralizer: `|class(g)| = [G : C_G(g)]`. -/
theorem conjClass_card_eq_index_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier =
      (Subgroup.centralizer ({ConjAct.toConjAct g} : Set (ConjAct G))).index := by
  have horbit : (ConjClasses.mk g).carrier = orbit (ConjAct G) g :=
    (ConjAct.orbit_eq_carrier_conjClasses g).symm
  rw [← ConjAct.stabilizer_eq_centralizer, horbit, Nat.card_coe_set_eq,
    MulAction.index_stabilizer]

/-- A chosen representative of a conjugacy class. -/
noncomputable def classRep (x : ConjClasses G) : G := (ConjClasses.exists_rep x).choose

@[simp] theorem mk_classRep (x : ConjClasses G) : ConjClasses.mk (classRep x) = x :=
  (ConjClasses.exists_rep x).choose_spec

/-- **Pointwise bridge.** The size of any conjugacy class `x` equals the index of the
centralizer of its chosen representative: `|x| = [G : C_G(classRep x)]`. -/
theorem card_carrier_eq_index_centralizer (x : ConjClasses G) :
    Nat.card x.carrier =
      (Subgroup.centralizer ({ConjAct.toConjAct (classRep x)} : Set (ConjAct G))).index := by
  have h := conjClass_card_eq_index_centralizer (classRep x)
  rw [mk_classRep] at h
  exact h

/-- **The class equation, index form.** For a finite group `G`,

  `|Z(G)| + Σ_{noncentral classes x} [G : C_G(classRep x)] = |G|`.

Obtained from Mathlib's summed class equation
(`Group.nat_card_center_add_sum_card_noncenter_eq_card`) by replacing each noncentral
class size with the index of the centralizer of a representative
(`card_carrier_eq_index_centralizer`). -/
theorem classEquation_centralizer_index_form [Finite G] :
    Nat.card (Subgroup.center G) +
        ∑ᶠ x ∈ ConjClasses.noncenter G,
          (Subgroup.centralizer ({ConjAct.toConjAct (classRep x)} : Set (ConjAct G))).index =
      Nat.card G := by
  rw [← Group.nat_card_center_add_sum_card_noncenter_eq_card G]
  congr 1
  exact finsum_mem_congr rfl (fun x _ => (card_carrier_eq_index_centralizer x).symm)

/-- **Corollary.** The sum of centralizer indices over the noncentral conjugacy classes
accounts for exactly the noncentral elements: `Σ [G : C_G(gᵢ)] = |G| − |Z(G)|`. -/
theorem sum_noncenter_index_eq_card_sub_center [Finite G] :
    ∑ᶠ x ∈ ConjClasses.noncenter G,
        (Subgroup.centralizer ({ConjAct.toConjAct (classRep x)} : Set (ConjAct G))).index =
      Nat.card G - Nat.card (Subgroup.center G) := by
  have h := classEquation_centralizer_index_form (G := G)
  omega

end ConjugacyClassEquationOQ01OQ01
