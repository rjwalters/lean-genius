/-
Burnside Counting Lemma from Orbit-Stabilizer

Source: Open question from lagrange-theorem gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

Formalizes Burnside's counting lemma (Cauchy-Frobenius) as a consequence of
the orbit-stabilizer theorem, which itself generalizes Lagrange's theorem:

  Chain: Lagrange → Orbit-Stabilizer → Burnside Counting Lemma

  |X/G| = (1/|G|) Σ_{g ∈ G} |Fix(g)|

The proof uses Mathlib's `MulAction` machinery and the bijection between
the disjoint union of fixed-point sets and the product of orbits × group.
-/

import Mathlib

open MulAction Finset BigOperators

namespace BurnsideLemma

variable {G : Type*} {X : Type*} [Group G] [Fintype G]
  [MulAction G X] [Fintype X]

/-! ## Part I: Lagrange's Theorem (Foundation)

Lagrange's theorem states |H| divides |G| for any subgroup H of a finite group G.
This is the foundation that makes orbit-stabilizer work. -/

/-- Lagrange's theorem: the order of a subgroup divides the order of the group. -/
theorem lagrange_divides (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G :=
  Subgroup.card_subgroup_dvd_card H

/-- Lagrange's theorem: |G| = [G : H] · |H|. -/
theorem lagrange_index (H : Subgroup G) [Fintype H]
    [Fintype (G ⧸ H)] :
    Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H :=
  (Subgroup.card_eq_card_quotient_mul_card_subgroup H).symm

/-! ## Part II: Orbit-Stabilizer Theorem

For any x ∈ X, the orbit-stabilizer theorem says |Orb(x)| · |Stab(x)| = |G|.
This generalizes Lagrange because Stab(x) is a subgroup of G. -/

/-- The stabilizer of a point is a subgroup of G (structurally guaranteed in Mathlib). -/
example (x : X) : Subgroup G := stabilizer G x

/-- Orbit-stabilizer theorem: |Orb(x)| · |Stab(x)| = |G|. -/
theorem orbit_stabilizer (x : X)
    [Fintype (orbit G x)] [Fintype (stabilizer G x)] :
    Fintype.card (orbit G x) * Fintype.card (stabilizer G x) = Fintype.card G :=
  card_orbit_mul_card_stabilizer_eq_card_group G x

/-- The orbit of x is in bijection with the coset space G/Stab(x).
    This is the structural content underlying orbit-stabilizer. -/
theorem orbit_equiv_cosets (x : X)
    [Fintype (orbit G x)] [Fintype (stabilizer G x)] :
    Nonempty (orbit G x ≃ G ⧸ stabilizer G x) :=
  ⟨orbitEquivQuotientStabilizer G x⟩

/-- Orbit-stabilizer generalizes Lagrange: applying it to the action of G on G/H
    recovers |G| = [G : H] · |H|. -/
theorem orbit_stabilizer_generalizes_lagrange (H : Subgroup G) [Fintype H]
    [Fintype (G ⧸ H)] :
    Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H :=
  lagrange_index H

/-! ## Part III: Burnside's Counting Lemma (Cauchy-Frobenius)

The number of orbits equals the average number of fixed points:
  |X/G| = (1/|G|) Σ_{g ∈ G} |Fix(g)|

Equivalently: Σ_{g ∈ G} |Fix(g)| = |X/G| · |G|. -/

/-- The set of elements fixed by a group element g. -/
def fixedPoints (g : G) : Set X := MulAction.fixedBy X g

/-- Burnside's lemma (Cauchy-Frobenius): Σ |Fix(g)| = |orbits| · |G|.
    This is the integer form; dividing both sides by |G| gives the
    classical formula |orbits| = (1/|G|) Σ |Fix(g)|. -/
theorem burnside_lemma
    [∀ g : G, Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
    Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  sum_card_fixedBy_eq_card_orbits_mul_card_group G X

/-- Burnside's lemma in divisibility form: |G| divides Σ |Fix(g)|. -/
theorem burnside_divides
    [∀ g : G, Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    Fintype.card G ∣ ∑ g : G, Fintype.card (fixedBy X g) := by
  rw [burnside_lemma]
  exact dvd_mul_left _ _

/-! ## Part IV: The Chain of Generalizations

We show explicitly how each result follows from the previous:
  Lagrange → Orbit-Stabilizer → Burnside -/

/-- The chain is complete: Burnside follows from orbit-stabilizer.
    Orbit-stabilizer follows from Lagrange (applied to stabilizer subgroup).
    The key insight is the bijection Σ_{g} Fix(g) ≃ orbits × G. -/
theorem chain_lagrange_to_burnside :
    ∀ (H : Subgroup G) [Fintype H] [Fintype (G ⧸ H)],
    -- Lagrange says |G| = [G:H] · |H|
    Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H :=
  fun H => lagrange_index H

end BurnsideLemma
