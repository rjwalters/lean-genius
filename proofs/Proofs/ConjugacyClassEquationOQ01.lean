import Mathlib

/-!
# The conjugacy class equation: per-class divisibility (orbit–stabilizer for conjugation)

For a finite group `G` and an element `g : G`, the **conjugacy class** of `g` is the
orbit of `g` under the conjugation action `ConjAct G ↷ G`.  Specializing the
orbit–stabilizer theorem to this action gives the *class equation* in its sharpest
per-class form:

* `conjClass_card_mul_card_centralizer` :
  `|class(g)| · |C_G(g)| = |G|`, where `C_G(g)` is the centralizer of `g`.
* `conjClass_card_eq_index_centralizer` :
  `|class(g)| = [G : C_G(g)]` (the class size is the index of the centralizer).
* `conjClass_card_dvd_card` :
  `|class(g)| ∣ |G|` — **every conjugacy class size divides the group order**.

Mathlib already contains the orbit–stabilizer theorem
(`MulAction.index_stabilizer`, `Subgroup.index_mul_card`), the bridge identifying the
conjugation orbit with the conjugacy-class carrier (`ConjAct.orbit_eq_carrier_conjClasses`),
the bridge identifying its stabilizer with the centralizer
(`ConjAct.stabilizer_eq_centralizer`), and the *summed* class equation
(`Group.card_center_add_sum_card_noncenter_eq_card`).  It does **not** package the clean
per-class divisibility identity proved here, which is the arithmetic engine behind the
class equation and its standard corollaries (e.g. `p`-groups have nontrivial center).

The final `example` exhibits the result concretely: in `Equiv.Perm (Fin 3)` (order `6`)
every conjugacy class has cardinality dividing `6`.
-/

open MulAction Subgroup ConjAct

namespace ConjugacyClassEquationOQ01

variable {G : Type*} [Group G]

/-- **Orbit–stabilizer for conjugation.** The size of the conjugacy class of `g` times the
order of its centralizer equals the order of the group: `|class(g)| · |C_G(g)| = |G|`. -/
theorem conjClass_card_mul_card_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card (Subgroup.centralizer ({ConjAct.toConjAct g} : Set (ConjAct G))) =
      Nat.card G := by
  have horbit : (ConjClasses.mk g).carrier = orbit (ConjAct G) g :=
    (ConjAct.orbit_eq_carrier_conjClasses g).symm
  -- `|class(g)|` is the index of the stabilizer (orbit–stabilizer)
  have hclass : Nat.card (ConjClasses.mk g).carrier = (stabilizer (ConjAct G) g).index := by
    rw [horbit, Nat.card_coe_set_eq, ← MulAction.index_stabilizer (ConjAct G) g]
  -- the centralizer of `g` *is* the conjugation-stabilizer of `g`
  have hcent : Nat.card (Subgroup.centralizer ({ConjAct.toConjAct g} : Set (ConjAct G))) =
      Nat.card (stabilizer (ConjAct G) g) := by
    rw [ConjAct.stabilizer_eq_centralizer]
  rw [hclass, hcent, Subgroup.index_mul_card]
  exact (Nat.card_congr ConjAct.toConjAct.toEquiv).symm

/-- The conjugacy class of `g` has cardinality equal to the index of its centralizer:
`|class(g)| = [G : C_G(g)]`. -/
theorem conjClass_card_eq_index_centralizer (g : G) :
    Nat.card (ConjClasses.mk g).carrier =
      (Subgroup.centralizer ({ConjAct.toConjAct g} : Set (ConjAct G))).index := by
  have horbit : (ConjClasses.mk g).carrier = orbit (ConjAct G) g :=
    (ConjAct.orbit_eq_carrier_conjClasses g).symm
  rw [← ConjAct.stabilizer_eq_centralizer, horbit, Nat.card_coe_set_eq,
    MulAction.index_stabilizer]

/-- **The class equation, per class.** The cardinality of the conjugacy class of `g`
divides the order of the group: `|class(g)| ∣ |G|`. -/
theorem conjClass_card_dvd_card (g : G) :
    Nat.card (ConjClasses.mk g).carrier ∣ Nat.card G :=
  ⟨_, (conjClass_card_mul_card_centralizer g).symm⟩

/-- Concrete instance: in the symmetric group `S₃ = Equiv.Perm (Fin 3)` (order `6`),
every conjugacy class has cardinality dividing `6`. -/
example (g : Equiv.Perm (Fin 3)) : Nat.card (ConjClasses.mk g).carrier ∣ 6 := by
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  simpa [h6] using conjClass_card_dvd_card g

end ConjugacyClassEquationOQ01
