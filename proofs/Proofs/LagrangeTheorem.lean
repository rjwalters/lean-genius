import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# Lagrange's Theorem: Order of a Subgroup

## What This Proves
For a finite group G and subgroup H ≤ G, the order of H divides the order of G.
This is Wiedijk's 100 Theorems #71.

$$|H| \text{ divides } |G|$$

Equivalently: $|G| = |H| \cdot [G : H]$ where $[G : H]$ is the index of $H$ in $G$.

This fundamental result in group theory is one of the most important theorems in
abstract algebra, providing the foundation for understanding subgroup structure.

## Approach
- **Foundation (from Mathlib):** We use `Subgroup.card_subgroup_dvd_card` which directly
  proves the divisibility result via coset partition argument.
- **Original Contributions:** Pedagogical wrapper theorems with explicit documentation
  explaining the coset-based proof strategy.
- **Proof Techniques Demonstrated:** Working with finite groups, subgroups, and
  cardinality bounds.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.GroupTheory.Coset` : Coset theory and `card_subgroup_dvd_card`
- `Mathlib.GroupTheory.Index` : Subgroup index and `card_mul_index`
- `Mathlib.GroupTheory.OrderOfElement` : Element order theory
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` : Cyclic group results

## Historical Note
Joseph-Louis Lagrange proved this theorem in 1771 while studying permutation groups
in connection with polynomial equations. The theorem was generalized to abstract groups
by later mathematicians. It represents one of the first major results in group theory.

## Why This Works
The proof relies on partitioning the group G into left (or right) cosets of H.
Each coset has the same cardinality as H (via translation bijection), and cosets
are pairwise disjoint. Therefore |G| equals the number of cosets times |H|,
meaning |H| divides |G|.

## Wiedijk's 100 Theorems: #71
-/

namespace LagrangeTheorem

/-! ## The Main Theorem -/

/-- **Lagrange's Theorem**: The order of any subgroup divides the order of the group.

    This is the fundamental divisibility result for finite groups.

    The proof relies on partitioning G into left cosets of H:
    - Each coset gH has the same cardinality as H (via the bijection h ↦ gh)
    - Cosets are either identical or disjoint
    - G is the disjoint union of its left cosets
    - Therefore |G| = (number of cosets) × |H|, so |H| divides |G| -/
theorem card_subgroup_dvd_card (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] : Fintype.card H ∣ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card H

/-- Alternative formulation using explicit cardinality names. -/
theorem lagrange {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] : Fintype.card H ∣ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card H

/-! ## The Index Formula -/

/-- **Product Formula**: |G| = |H| × [G : H]

    The order of a group equals the order of any subgroup times its index.
    This is the quantitative version of Lagrange's theorem. -/
theorem card_eq_card_mul_index (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] : Fintype.card G = Fintype.card H * H.index := by
  simp only [← Nat.card_eq_fintype_card]
  rw [mul_comm, ← Subgroup.card_mul_index H, mul_comm]

/-! ## The Coset Partition Intuition

The key insight is that left cosets form a partition of G:

For subgroup H ≤ G, the left cosets are sets of the form gH = {gh : h ∈ H}

| Property              | Why It Holds                                    |
|-----------------------|-------------------------------------------------|
| g ∈ gH                | g = g · e ∈ gH since e ∈ H                      |
| Cosets equal or disjoint | If g₁H ∩ g₂H ≠ ∅, then g₁H = g₂H             |
| |gH| = |H|            | h ↦ gh is a bijection from H to gH              |
| G = ⊔ gH              | Every element is in some coset                  |

This gives: |G| = (# of distinct cosets) × |H| = [G : H] × |H|
-/

/-! ## Corollaries -/

/-- **Order of Element Divides Group Order**: For any element g in a finite group,
    the order of g divides the order of the group.

    This follows from Lagrange's theorem applied to the cyclic subgroup ⟨g⟩. -/
theorem orderOf_dvd_card' {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card (x := g)

/-- For any element, its order divides the group order (alternative statement). -/
theorem order_divides_card {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card (x := g)

/-- **Power by Group Order**: Raising any element to the group order gives identity.

    This is an immediate consequence of order dividing group order. -/
theorem pow_card_eq_one' {G : Type*} [Group G] [Fintype G] (g : G) :
    g ^ Fintype.card G = 1 :=
  pow_card_eq_one (x := g)

/-! ## Connection to Fermat's Little Theorem

Lagrange's theorem immediately implies Fermat's little theorem when applied
to the multiplicative group (ℤ/pℤ)×.

For prime p and a coprime to p:
- (ℤ/pℤ)× has order p - 1 (= φ(p) for prime p)
- By Lagrange: order of a divides p - 1
- Therefore: a^(p-1) ≡ 1 (mod p)

This is the group-theoretic explanation of Fermat's little theorem.
-/

/-- Fermat's little theorem as a consequence of Lagrange's theorem.
    For prime p, a^(p-1) ≡ 1 (mod p) when gcd(a, p) = 1. -/
theorem fermat_little_from_lagrange {p : ℕ} [hp : Fact (Nat.Prime p)]
    (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  have h : Fintype.card (ZMod p)ˣ = p.totient := ZMod.card_units_eq_totient p
  have hp' : p.totient = p - 1 := Nat.totient_prime hp.out
  calc a ^ (p - 1)
      = a ^ p.totient := by rw [hp']
    _ = a ^ Fintype.card (ZMod p)ˣ := by rw [h]
    _ = 1 := pow_card_eq_one

/-! ## Properties of Subgroup Index -/

/-- The index of a subgroup in a finite group is the number of cosets. -/
theorem index_eq_card_quotient (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [DecidablePred (· ∈ H)] :
    H.index = Fintype.card (G ⧸ H) := by
  rw [← Nat.card_eq_fintype_card]
  exact Subgroup.index_eq_card H

/-- The index divides the group order. -/
theorem index_dvd_card (G : Type*) [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] : H.index ∣ Fintype.card G := by
  rw [card_eq_card_mul_index G H]
  exact Dvd.intro (Fintype.card H) (mul_comm _ _)

/-! ## Examples and Verification -/

/-- In a group of order n, the trivial subgroup has index n. -/
example (G : Type*) [Group G] [Fintype G] :
    (⊥ : Subgroup G).index = Fintype.card G := by
  rw [← Nat.card_eq_fintype_card]
  exact Subgroup.index_bot

/-- Every group is its own subgroup with index 1. -/
example (G : Type*) [Group G] [Fintype G] :
    (⊤ : Subgroup G).index = 1 :=
  Subgroup.index_top

/-! ## Consequences for Group Structure -/

/-- **Prime Order Implication**: If |G| = p (prime), then G has no non-trivial proper subgroups.

    This follows from Lagrange: any subgroup order must divide p,
    so it's either 1 (trivial) or p (the whole group). -/
theorem prime_order_simple {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (hp : Nat.Prime (Fintype.card G)) :
    Fintype.card H = 1 ∨ Fintype.card H = Fintype.card G := by
  have hdvd : Fintype.card H ∣ Fintype.card G := card_subgroup_dvd_card G H
  exact hp.eq_one_or_self_of_dvd (Fintype.card H) hdvd

/-- Groups of prime order are cyclic (every element except identity generates). -/
theorem prime_order_cyclic {G : Type*} [Group G] [Fintype G]
    (hp : Nat.Prime (Fintype.card G)) : IsCyclic G := by
  haveI : Fact (Nat.Prime (Fintype.card G)) := ⟨hp⟩
  exact isCyclic_of_prime_card rfl

/-! ## Why Lagrange's Theorem Matters

Lagrange's theorem is fundamental because:

1. **Structure constraints**: Limits possible subgroup orders
2. **Element orders**: Constrains orders of elements via cyclic subgroups
3. **Counting arguments**: Enables group counting and classification
4. **Number theory**: Implies Fermat's little theorem and Euler's theorem
5. **Extensions**: Generalizes to orbit-stabilizer and class equation

The converse is NOT true: n dividing |G| doesn't guarantee a subgroup of order n.
(Counter-example: A₄ has order 12 but no subgroup of order 6.)
-/

#check card_subgroup_dvd_card
#check card_eq_card_mul_index
#check orderOf_dvd_card'
#check pow_card_eq_one'
#check fermat_little_from_lagrange
#check prime_order_simple
#check prime_order_cyclic

end LagrangeTheorem
