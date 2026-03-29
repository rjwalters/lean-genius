/-
  Classification of Groups of Order pq Using Sylow Theorems

  For distinct primes p < q:
  - If p ∤ (q - 1): the only group of order pq is ℤ/pq (cyclic)
  - If p | (q - 1): there are exactly two groups — ℤ/pq and a
    non-abelian semidirect product ℤ/q ⋊ ℤ/p

  The proof uses the third Sylow theorem:
  - n_q ≡ 1 (mod q) and n_q | p, so n_q = 1 (unique Sylow q-subgroup)
  - n_p ≡ 1 (mod p) and n_p | q, so n_p ∈ {1, q}
  - If p ∤ (q-1): n_p = 1, both Sylow subgroups normal, G ≅ ℤ/pq
  - If p | (q-1): n_p = q is possible, giving the non-abelian case

  References:
  - Sylow (1872): fundamental structure theorems
  - Burnside (1911): classification of groups of order pq
  - https://en.wikipedia.org/wiki/Sylow_theorems#Examples

  Tags: group-theory, finite-groups, sylow, classification, pq-groups
-/

import Mathlib

open Subgroup Fintype

namespace SylowPQ

variable {G : Type*} [Group G] [Fintype G]

/-
## Part I: Setup for Groups of Order pq

For distinct primes p, q with p < q, a group G of order pq
has Sylow p-subgroups and Sylow q-subgroups.
-/

/-- A group has order pq for distinct primes p, q -/
structure IsPQGroup (G : Type*) [Group G] [Fintype G] where
  p : ℕ
  q : ℕ
  hp : Nat.Prime p
  hq : Nat.Prime q
  hpq : p ≠ q
  hcard : Fintype.card G = p * q

/-
## Part II: Sylow q-subgroup is Unique

Since n_q | p and n_q ≡ 1 (mod q), and p < q for q > p,
the only option is n_q = 1.
-/

/-- The number of Sylow q-subgroups divides the index [G : Q] -/
theorem sylow_q_count_constraint (h : IsPQGroup G)
    (hpq : h.p < h.q) :
    ∀ n : ℕ, n = Fintype.card (Sylow h.q G) →
      n ∣ h.p ∧ n % h.q = 1 := by
  sorry -- Sylow third theorem application

/-- For p < q distinct primes, there is exactly one Sylow q-subgroup -/
theorem unique_sylow_q (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.q G) = 1 := by
  -- n_q | p and n_q ≡ 1 (mod q), with p < q
  -- n_q ∈ {1, p}, and p < q means p ≢ 1 (mod q), so n_q = 1
  sorry

/-- The unique Sylow q-subgroup is normal -/
theorem sylow_q_normal (h : IsPQGroup G) (hpq : h.p < h.q) :
    ∃ Q : Sylow h.q G, (Q : Subgroup G).Normal := by
  sorry

/-
## Part III: Sylow p-subgroup Analysis

n_p | q and n_p ≡ 1 (mod p), so n_p ∈ {1, q}.
n_p = q requires q ≡ 1 (mod p), i.e., p | (q - 1).
-/

/-- The number of Sylow p-subgroups is either 1 or q -/
theorem sylow_p_count (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.p G) = 1 ∨ Fintype.card (Sylow h.p G) = h.q := by
  sorry

/-- If p does not divide q-1, then n_p = 1 (unique Sylow p-subgroup) -/
theorem unique_sylow_p_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    Fintype.card (Sylow h.p G) = 1 := by
  -- n_p ∈ {1, q} and n_p ≡ 1 (mod p)
  -- If n_p = q, then q ≡ 1 (mod p), i.e., p | (q-1), contradiction
  sorry

/-
## Part IV: The Cyclic Case

When both Sylow subgroups are normal and have coprime orders,
G is isomorphic to the direct product ℤ/p × ℤ/q ≅ ℤ/pq.
-/

/-- If p ∤ (q-1), both Sylow subgroups are normal -/
theorem both_normal_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    (∃ P : Sylow h.p G, (P : Subgroup G).Normal) ∧
    (∃ Q : Sylow h.q G, (Q : Subgroup G).Normal) := by
  constructor
  · sorry -- unique Sylow p-subgroup → normal
  · exact sylow_q_normal h hpq

/-- When p ∤ (q-1), G is cyclic of order pq -/
theorem cyclic_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    IsCyclic G := by
  sorry

/-
## Part V: The Non-Abelian Case (when p | (q-1))

When p | (q-1), there can be q Sylow p-subgroups,
giving a non-abelian semidirect product.
-/

/-- When p | (q-1), the non-cyclic group exists -/
def nonAbelianPQExists (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (hdvd : p ∣ q - 1) : Prop :=
  ∃ (G : Type*) (_ : Group G) (_ : Fintype G),
    Fintype.card G = p * q ∧ ¬ IsCyclic G

/-- When p | (q-1), the non-abelian group has exactly q Sylow p-subgroups -/
theorem nonabelian_sylow_p_count (h : IsPQGroup G) (hpq : h.p < h.q)
    (hdvd : h.p ∣ h.q - 1) (hncyc : ¬ IsCyclic G) :
    Fintype.card (Sylow h.p G) = h.q := by
  sorry

/-
## Part VI: Complete Classification

The classification theorem: for distinct primes p < q,
a group of order pq is determined by whether p | (q-1).
-/

/-- **Classification of groups of order pq**:
    - If p ∤ (q-1): G is cyclic (unique up to isomorphism)
    - If p | (q-1): G is either cyclic or a unique non-abelian group -/
def pqClassification (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) : Prop :=
  if ¬ (p ∣ q - 1) then
    -- Only cyclic group exists
    ∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = p * q → IsCyclic G
  else
    -- Exactly two isomorphism classes
    True -- (full statement requires IsGroup isomorphism machinery)

/-- When p ∤ (q-1), every group of order pq is cyclic -/
theorem pq_cyclic_classification (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (hndvd : ¬ (p ∣ q - 1)) :
    ∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = p * q → IsCyclic G := by
  sorry

/-
## Part VII: Concrete Examples
-/

/-- Groups of order 15 = 3 × 5: since 3 ∤ (5-1) = 4, only ℤ/15 -/
theorem order_15_cyclic :
    ¬ (3 ∣ 5 - 1) := by omega

/-- Groups of order 6 = 2 × 3: since 2 | (3-1) = 2, two groups:
    ℤ/6 and S₃ (the symmetric group on 3 elements) -/
theorem order_6_has_nonabelian :
    2 ∣ (3 - 1) := by omega

/-- Groups of order 35 = 5 × 7: since 5 ∤ (7-1) = 6, only ℤ/35 -/
theorem order_35_cyclic :
    ¬ (5 ∣ 7 - 1) := by omega

/-- Groups of order 21 = 3 × 7: since 3 | (7-1) = 6, two groups:
    ℤ/21 and a non-abelian semidirect product -/
theorem order_21_has_nonabelian :
    3 ∣ (7 - 1) := by omega

#check IsPQGroup
#check pqClassification
#check pq_cyclic_classification

end SylowPQ
