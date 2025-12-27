import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Sylow's Theorems

## What This Proves
The Sylow theorems are fundamental structure theorems for finite groups.
For a finite group G of order n = pᵏm where p is prime and p ∤ m:

1. **Existence**: G has a subgroup of order pᵏ (called a Sylow p-subgroup)
2. **Conjugacy**: All Sylow p-subgroups are conjugate to each other
3. **Counting**: The number of Sylow p-subgroups divides m and is ≡ 1 (mod p)

This is Wiedijk's 100 Theorems #72.

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.GroupTheory.Sylow` which provides
  complete Sylow theory including the `Sylow` structure and key theorems.
- **Original Contributions:** Pedagogical wrapper theorems stating all three
  Sylow theorems in classical notation with detailed documentation.
- **Proof Techniques Demonstrated:** Working with p-groups, group actions,
  conjugacy classes, and cardinality arguments.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main results
- [x] States all three Sylow theorems
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.GroupTheory.Sylow` : The Sylow structure and main theorems
- `Mathlib.GroupTheory.Coset` : Coset theory for index calculations
- `Mathlib.GroupTheory.Index` : Subgroup index
- `Mathlib.Data.Nat.Factorization.Basic` : Prime factorization

## Historical Note
Peter Ludwig Mejdell Sylow (1832-1918) proved these theorems in 1872.
They generalize Cauchy's theorem (which guarantees an element of order p
when p divides |G|) and provide crucial structural information about finite
groups. The Sylow theorems are among the most important tools in finite group
theory, used extensively in classification problems.

## Why These Theorems Matter

The Sylow theorems are fundamental because:

1. **Existence guarantees**: Every finite group has p-subgroups of maximal order
2. **Uniqueness up to conjugacy**: All maximal p-subgroups are "the same" structurally
3. **Counting constraints**: Severely limits possible group structures
4. **Classification tool**: Essential for classifying groups of small order

For example, to show a group of order 15 is cyclic:
- By Sylow: n₃ | 5 and n₃ ≡ 1 (mod 3), so n₃ = 1 (unique Sylow 3-subgroup)
- By Sylow: n₅ | 3 and n₅ ≡ 1 (mod 5), so n₅ = 1 (unique Sylow 5-subgroup)
- Unique Sylow subgroups are normal; their intersection is trivial
- Therefore G ≅ ℤ₃ × ℤ₅ ≅ ℤ₁₅ (cyclic)

## Wiedijk's 100 Theorems: #72
-/

namespace SylowTheorems

open Subgroup

set_option linter.unusedVariables false

/-! ## Background: The Sylow Structure

In Mathlib, a Sylow p-subgroup is captured by the `Sylow p G` type.
An element `P : Sylow p G` represents a Sylow p-subgroup of G.
The underlying subgroup is accessed via coercion `↑P : Subgroup G`.
-/

/-! ## First Sylow Theorem: Existence

For any prime p dividing the order of a finite group G, there exists
a Sylow p-subgroup (a subgroup of order pᵏ where pᵏ is the largest
power of p dividing |G|).
-/

/-- **First Sylow Theorem (Existence)**: For any prime p, a finite group G
    has at least one Sylow p-subgroup.

    More precisely, if |G| = pᵏm where p ∤ m, then G has a subgroup of order pᵏ.

    The proof uses induction on |G| and analyzes the class equation. -/
theorem sylow_existence (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime] :
    Nonempty (Sylow p G) :=
  Sylow.nonempty

/-- The order of a Sylow p-subgroup equals pᵏ where pᵏ is the largest power
    of p dividing |G|.

    This is the defining property of Sylow p-subgroups. -/
theorem sylow_card (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) : Nat.card P = p ^ (Nat.card G).factorization p :=
  P.card_eq_multiplicity

/-! ## Second Sylow Theorem: Conjugacy

All Sylow p-subgroups are conjugate to each other. This means that
if P and Q are both Sylow p-subgroups of G, then there exists g ∈ G
such that Q = gPg⁻¹.
-/

/-- **Second Sylow Theorem (Conjugacy)**: Any two Sylow p-subgroups are conjugate.

    For Sylow p-subgroups P and Q, there exists g ∈ G such that g • P = Q
    (where the action is by conjugation).

    This is proved by letting P act on the cosets G/Q by multiplication
    and applying orbit-stabilizer arguments.

    Note: This requires Finite (Sylow p G), which holds for finite groups. -/
theorem sylow_conjugacy (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] (P Q : Sylow p G) : ∃ g : G, g • P = Q :=
  MulAction.exists_smul_eq G P Q

/-- Conjugacy implies all Sylow p-subgroups are isomorphic as groups. -/
theorem sylow_isomorphic (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] (P Q : Sylow p G) : Nonempty ((↑P : Subgroup G) ≃* (↑Q : Subgroup G)) :=
  ⟨Sylow.equiv P Q⟩

/-! ## Third Sylow Theorem: Counting

The number of Sylow p-subgroups divides |G|/pᵏ = m and is congruent
to 1 modulo p.
-/

/-- **Third Sylow Theorem (Counting)**: The number of Sylow p-subgroups
    satisfies n_p ≡ 1 (mod p).

    This follows from the conjugation action of G on its Sylow p-subgroups:
    the only fixed point of a Sylow p-subgroup P acting by conjugation is P itself. -/
theorem sylow_count_mod_p (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] : Nat.card (Sylow p G) ≡ 1 [MOD p] :=
  card_sylow_modEq_one p G

/-- The number of Sylow p-subgroups divides the index of any Sylow p-subgroup. -/
theorem sylow_count_dvd_index (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) : Nat.card (Sylow p G) ∣ (↑P : Subgroup G).index :=
  card_sylow_dvd_index P

/-! ## Uniqueness of Sylow Subgroups

When there is exactly one Sylow p-subgroup, it must be normal
(since it's conjugate only to itself).
-/

/-- If g • P = P for all g, then P is normal. -/
theorem sylow_normal_of_eq (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (h : ∀ g : G, g • P = P) : (↑P : Subgroup G).Normal := by
  rw [← normalizer_eq_top]
  ext g
  simp only [mem_top, iff_true]
  rw [mem_normalizer_iff]
  intro x
  have := h g
  rw [Sylow.smul_eq_iff_mem_normalizer] at this
  rw [mem_normalizer_iff] at this
  exact this x

/-- If there is exactly one Sylow p-subgroup (Subsingleton), it is normal. -/
theorem sylow_normal_of_unique (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) [Subsingleton (Sylow p G)] : (↑P : Subgroup G).Normal := by
  apply sylow_normal_of_eq
  intro g
  apply Subsingleton.elim

/-- When there are finitely many Sylow subgroups, a normal Sylow subgroup is unique. -/
noncomputable def sylow_unique_of_normal (G : Type*) [Group G] (p : ℕ) [Fact p.Prime]
    [Finite (Sylow p G)] (P : Sylow p G) (h : (↑P : Subgroup G).Normal) :
    Unique (Sylow p G) :=
  Sylow.unique_of_normal P h

/-! ## Cauchy's Theorem as a Corollary

Sylow's first theorem immediately implies Cauchy's theorem: if a prime p
divides |G|, then G has an element of order p.
-/

/-- **Cauchy's Theorem**: If prime p divides |G|, then G has an element of order p.

    This follows from Sylow's theorem: a Sylow p-subgroup has order pᵏ ≥ p,
    so it contains a non-identity element whose order is a power of p,
    and raising it to an appropriate power gives an element of order p. -/
theorem cauchy_from_sylow (G : Type*) [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (hdvd : p ∣ Fintype.card G) : ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card p hdvd

/-! ## Examples and Applications -/

/-- For a prime p, a group of order p is cyclic (immediate from Lagrange). -/
theorem group_of_prime_order_cyclic (G : Type*) [Group G] [Fintype G]
    (hp : (Fintype.card G).Prime) : IsCyclic G := by
  haveI : Fact (Fintype.card G).Prime := ⟨hp⟩
  exact isCyclic_of_prime_card rfl

/-! ## Summary of Key Results

| Theorem | Statement |
|---------|-----------|
| Sylow I (Existence) | Sylow p-subgroups exist for any prime p |
| Sylow II (Conjugacy) | All Sylow p-subgroups are conjugate |
| Sylow III (Counting) | n_p ≡ 1 (mod p) and n_p ∣ [G : P] |
| Uniqueness | If Subsingleton (Sylow p G), then P is normal |
| Cauchy | p ∣ |G| ⟹ ∃ element of order p |

These theorems, combined with Lagrange's theorem, form the foundation
for analyzing finite group structure.

## Applications in Group Classification

The Sylow theorems are indispensable for classifying finite groups:

1. **Groups of order pq** (p < q primes):
   - n_q ≡ 1 (mod q) and n_q | p
   - Since q > p, we must have n_q = 1 (unique normal Sylow q-subgroup)

2. **Groups of order p²**:
   - Must have exactly one Sylow p-subgroup (itself)
   - Such groups are abelian

3. **Simple group classification**:
   - Sylow counting arguments rule out many possible orders
   - Groups with certain orders cannot be simple
-/

#check sylow_existence
#check sylow_card
#check sylow_conjugacy
#check sylow_isomorphic
#check sylow_count_mod_p
#check sylow_count_dvd_index
#check sylow_normal_of_unique
#check sylow_unique_of_normal
#check cauchy_from_sylow
#check group_of_prime_order_cyclic

end SylowTheorems
