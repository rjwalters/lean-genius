/-
  Lagrange's Theorem OQ-02: The Orbit-Stabilizer Theorem

  The orbit-stabilizer theorem is a fundamental generalization of Lagrange's
  theorem to group actions. For a group G acting on a set X:

  |G| = |Orb_G(x)| x |Stab_G(x)|

  This directly generalizes Lagrange's theorem: let G act on the coset space
  G/H by left multiplication. The orbit of eH is all of G/H (the action is
  transitive), and the stabilizer of eH is H. So |G| = |G/H| x |H|.

  ## Results

  ### Proved (0 sorries, 0 axioms -- all from Mathlib):
  1. Orbit-stabilizer bijection: Orb(x) ≃ G/Stab(x)
  2. Orbit-stabilizer theorem: |Orb(x)| x |Stab(x)| = |G|
  3. Orbit size divides group order
  4. Stabilizer order divides group order
  5. Lagrange as special case of orbit-stabilizer
  6. Index formula: |G| = |H| x [G:H]
  7. Element order divides group order
  8. Orbit size equals stabilizer index
  9. p-group fixed point theorem: |Fix| ≡ |X| (mod p)
  10. Center of a nontrivial p-group is nontrivial

  ## References
  - Dummit & Foote, "Abstract Algebra", Ch. 4
  - Lang, "Algebra", Ch. I.5

  Tags: group-theory, algebra, group-actions, wiedijk-100
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace LagrangeTheoremOQ02

noncomputable section

-- ============================================================================
-- Part I: Orbit and Stabilizer Basics
-- ============================================================================

/-- Every element belongs to its own orbit. -/
theorem mem_orbit_self' {G : Type*} [Group G] {X : Type*} [MulAction G X]
    (x : X) : x ∈ MulAction.orbit G x :=
  MulAction.mem_orbit_self x

/-- Elements of the stabilizer fix the point. -/
theorem mem_stabilizer_iff' {G : Type*} [Group G] {X : Type*} [MulAction G X]
    (g : G) (x : X) : g ∈ MulAction.stabilizer G x ↔ g • x = x :=
  Iff.rfl

/-- The identity is always in the stabilizer. -/
theorem one_mem_stabilizer {G : Type*} [Group G] {X : Type*} [MulAction G X]
    (x : X) : (1 : G) ∈ MulAction.stabilizer G x :=
  one_smul G x

-- ============================================================================
-- Part II: The Orbit-Stabilizer Bijection
-- ============================================================================

/-- **Orbit-Stabilizer Bijection**: The orbit of x is in bijection with
    the left cosets of the stabilizer.

    The map g . x |-> g . Stab(x) is well-defined: g1 . x = g2 . x iff
    g1^{-1}g2 in Stab(x) iff g1.Stab(x) = g2.Stab(x). -/
def orbit_equiv_quotient_stabilizer {G : Type*} [Group G]
    {X : Type*} [MulAction G X] (x : X) :
    MulAction.orbit G x ≃ G ⧸ MulAction.stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

-- ============================================================================
-- Part III: The Orbit-Stabilizer Theorem (Cardinality)
-- ============================================================================

/-- **Orbit-Stabilizer Theorem**: |Orb(x)| x |Stab(x)| = |G|.

    From Orb(x) ≃ G/Stab(x) we get |Orb(x)| = [G : Stab(x)].
    Lagrange gives |G| = |Stab(x)| x [G : Stab(x)] = |Stab(x)| x |Orb(x)|. -/
theorem card_orbit_mul_card_stabilizer {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
      Nat.card G := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x), mul_comm]
  exact Subgroup.card_mul_index (MulAction.stabilizer G x)

/-- The orbit size divides the group order. -/
theorem card_orbit_dvd {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] (x : X) :
    Nat.card (MulAction.orbit G x) ∣ Nat.card G :=
  Dvd.intro _ (card_orbit_mul_card_stabilizer x)

/-- The stabilizer order divides the group order (also from Lagrange directly). -/
theorem card_stabilizer_dvd {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] (x : X) :
    Nat.card (MulAction.stabilizer G x) ∣ Nat.card G :=
  Dvd.intro_left _ (card_orbit_mul_card_stabilizer x)

-- ============================================================================
-- Part IV: Lagrange's Theorem as Special Case
-- ============================================================================

/-- **Lagrange's Theorem from Orbit-Stabilizer**: The order of a subgroup
    divides the order of the group.

    Special case: G acts on the left coset space G/H.
    - The action is transitive, so Orb(eH) = G/H
    - Stab(eH) = H
    - |G| = |G/H| x |H|, so |H| divides |G|. -/
theorem lagrange {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card H

/-- The index formula: |H| x [G:H] = |G|. -/
theorem card_mul_index {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) :
    Nat.card H * H.index = Nat.card G :=
  Subgroup.card_mul_index H

/-- The order of any element divides the group order
    (Lagrange applied to the cyclic subgroup). -/
theorem order_dvd_card {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card

/-- Raising any element to the group order gives the identity. -/
theorem pow_card_eq_one' {G : Type*} [Group G] [Fintype G] (g : G) :
    g ^ Fintype.card G = 1 :=
  pow_card_eq_one

-- ============================================================================
-- Part V: Orbit Size = Stabilizer Index
-- ============================================================================

/-- The size of the orbit equals the index of the stabilizer. -/
theorem card_orbit_eq_index {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] (x : X) :
    Nat.card (MulAction.orbit G x) = (MulAction.stabilizer G x).index := by
  rw [Subgroup.index_eq_card (MulAction.stabilizer G x)]
  exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G x)

-- ============================================================================
-- Part VI: Transitive Actions
-- ============================================================================

/-- For a transitive (pretransitive) action, every orbit is the full set. -/
theorem orbit_eq_univ {G : Type*} [Group G]
    {X : Type*} [MulAction G X] [MulAction.IsPretransitive G X]
    (x : X) : MulAction.orbit G x = Set.univ :=
  MulAction.orbit_eq_univ G x

-- ============================================================================
-- Part VII: Fixed Points of p-Group Actions
-- ============================================================================

/-- **p-Group Fixed Point Theorem**: When a p-group G acts on a finite set X,
    the number of fixed points is congruent to |X| modulo p.

    Non-fixed orbits have size > 1 and dividing |G| = p^k, so p divides
    each non-fixed orbit size. Since |X| = |Fix(G)| + sum of non-fixed orbit
    sizes, we get |Fix(G)| ≡ |X| (mod p). -/
theorem card_fixedPoints_mod_prime
    {p : ℕ} {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Finite X]
    [hp : Fact p.Prime] (hG : IsPGroup p G) :
    Nat.card X ≡ Nat.card (MulAction.fixedPoints G X) [MOD p] :=
  IsPGroup.card_modEq_card_fixedPoints hG X

/-- **Nontrivial Center of p-Groups**: If G is a nontrivial p-group,
    then Z(G) is nontrivial.

    Apply the p-group fixed point theorem to the conjugation action.
    The fixed points of conjugation are exactly the center Z(G).
    So |Z(G)| ≡ |G| (mod p), and since |G| = p^k with k >= 1,
    p divides |Z(G)|. As 1 in Z(G), |Z(G)| >= p > 1. -/
theorem center_nontrivial_of_pgroup
    {p : ℕ} [hp : Fact p.Prime] {G : Type*} [Group G] [Fintype G]
    (hG : IsPGroup p G) (hnt : Nontrivial G) :
    Nontrivial (Subgroup.center G) :=
  IsPGroup.center_nontrivial hG

-- ============================================================================
-- Part VIII: The Generalization Hierarchy
-- ============================================================================

/-- **Summary**: The orbit-stabilizer theorem unifies several key results:

    1. **Lagrange**: |H| | |G| (G acts on G/H)
    2. **Burnside**: Sum |Fix(g)| = |X/G| x |G| (double counting)
    3. **Class equation**: |G| = |Z(G)| + Sum [G : C_G(g_i)] (conjugation)
    4. **p-group fixed points**: |Fix| ≡ |X| (mod p) (orbit divisibility)

    All follow from: |G| = |Orb(x)| x |Stab(x)|. -/
theorem orbit_stabilizer_and_lagrange {G : Type*} [Group G] [Fintype G]
    {X : Type*} [MulAction G X] [Fintype X] (x : X) (H : Subgroup G) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G
    ∧ Nat.card H ∣ Nat.card G :=
  ⟨card_orbit_mul_card_stabilizer x, Subgroup.card_subgroup_dvd_card H⟩

end

end LagrangeTheoremOQ02
