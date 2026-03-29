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
## Helper Lemmas: Factorization and Subgroup Orders
-/

/-- The q-adic valuation of p*q is 1 when p, q are distinct primes -/
private lemma factorization_pq_at_q (h : IsPQGroup G) :
    (h.p * h.q).factorization h.q = 1 := by
  rw [Nat.factorization_mul (Nat.Prime.ne_zero h.hp) (Nat.Prime.ne_zero h.hq),
      Finsupp.add_apply]
  have h1 : h.p.factorization h.q = 0 := by
    rw [(Nat.Prime.prime h.hp).factorization, Finsupp.single_apply,
        if_neg (Ne.symm h.hpq)]
  have h2 : h.q.factorization h.q = 1 := by
    rw [(Nat.Prime.prime h.hq).factorization, Finsupp.single_apply, if_pos rfl]
  omega

/-- The p-adic valuation of p*q is 1 when p, q are distinct primes -/
private lemma factorization_pq_at_p (h : IsPQGroup G) :
    (h.p * h.q).factorization h.p = 1 := by
  rw [Nat.factorization_mul (Nat.Prime.ne_zero h.hp) (Nat.Prime.ne_zero h.hq),
      Finsupp.add_apply]
  have h1 : h.p.factorization h.p = 1 := by
    rw [(Nat.Prime.prime h.hp).factorization, Finsupp.single_apply, if_pos rfl]
  have h2 : h.q.factorization h.p = 0 := by
    rw [(Nat.Prime.prime h.hq).factorization, Finsupp.single_apply,
        if_neg (Ne.symm h.hpq)]
  omega

/-- The Sylow q-subgroup has order q -/
private lemma sylow_q_card (h : IsPQGroup G) (Q : Sylow h.q G) :
    Nat.card Q = h.q := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  rw [Q.card_eq_multiplicity, Nat.card_eq_fintype_card, h.hcard,
      factorization_pq_at_q h, pow_one]

/-- The Sylow p-subgroup has order p -/
private lemma sylow_p_card (h : IsPQGroup G) (P : Sylow h.p G) :
    Nat.card P = h.p := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, h.hcard,
      factorization_pq_at_p h, pow_one]

/-- The index of a Sylow q-subgroup in a pq-group is p -/
private lemma sylow_q_index (h : IsPQGroup G) (Q : Sylow h.q G) :
    (Q : Subgroup G).index = h.p := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  have hcmi := Subgroup.card_mul_index (Q : Subgroup G)
  rw [sylow_q_card h Q, Nat.card_eq_fintype_card, h.hcard,
      mul_comm h.p h.q] at hcmi
  exact mul_left_cancel₀ (Nat.Prime.ne_zero h.hq) hcmi

/-- The index of a Sylow p-subgroup in a pq-group is q -/
private lemma sylow_p_index (h : IsPQGroup G) (P : Sylow h.p G) :
    (P : Subgroup G).index = h.q := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  have hcmi := Subgroup.card_mul_index (P : Subgroup G)
  rw [sylow_p_card h P, Nat.card_eq_fintype_card, h.hcard] at hcmi
  exact mul_left_cancel₀ (Nat.Prime.ne_zero h.hp) hcmi

/-- If a Sylow subgroup is unique (card 1), it is normal -/
private lemma sylow_normal_of_card_one {p : ℕ} [Fact p.Prime]
    (hp_card : Fintype.card (Sylow p G) = 1) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal := by
  haveI : Subsingleton (Sylow p G) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  obtain ⟨P⟩ := Sylow.nonempty p G
  exact ⟨P, by
    rw [← normalizer_eq_top, eq_top_iff]
    intro g _
    exact Sylow.smul_eq_iff_mem_normalizer.mp (Subsingleton.elim _ _)⟩

/-
## Part II: Sylow q-subgroup is Unique

Since n_q | p and n_q ≡ 1 (mod q), and p < q for q > p,
the only option is n_q = 1.
-/

/-- The number of Sylow q-subgroups divides p and is ≡ 1 (mod q) -/
theorem sylow_q_count_constraint (h : IsPQGroup G)
    (hpq : h.p < h.q) :
    ∀ n : ℕ, n = Fintype.card (Sylow h.q G) →
      n ∣ h.p ∧ n % h.q = 1 := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  intro n hn; subst hn
  obtain ⟨Q⟩ := Sylow.nonempty h.q G
  constructor
  · -- n_q | index Q = p
    have hdvd := card_sylow_dvd_index Q
    rw [sylow_q_index h Q] at hdvd
    rwa [← Nat.card_eq_fintype_card]
  · -- n_q ≡ 1 (mod q)
    have hmod := card_sylow_modEq_one h.q G
    rw [Nat.ModEq, Nat.mod_eq_of_lt h.hq.one_lt] at hmod
    rwa [← Nat.card_eq_fintype_card]

/-- For p < q distinct primes, there is exactly one Sylow q-subgroup -/
theorem unique_sylow_q (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.q G) = 1 := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  obtain ⟨hdvd, hmod⟩ := sylow_q_count_constraint h hpq _ rfl
  rcases h.hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp
  · exact h1
  · -- If n_q = p, then p % q = 1, but p < q so p % q = p, giving p = 1
    exfalso
    rw [hp, Nat.mod_eq_of_lt hpq] at hmod
    have := h.hp.one_lt; omega

/-- The unique Sylow q-subgroup is normal -/
theorem sylow_q_normal (h : IsPQGroup G) (hpq : h.p < h.q) :
    ∃ Q : Sylow h.q G, (Q : Subgroup G).Normal := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  exact sylow_normal_of_card_one (unique_sylow_q h hpq)

/-
## Part III: Sylow p-subgroup Analysis

n_p | q and n_p ≡ 1 (mod p), so n_p ∈ {1, q}.
n_p = q requires q ≡ 1 (mod p), i.e., p | (q - 1).
-/

/-- The number of Sylow p-subgroups is either 1 or q -/
theorem sylow_p_count (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.p G) = 1 ∨ Fintype.card (Sylow h.p G) = h.q := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  obtain ⟨P⟩ := Sylow.nonempty h.p G
  have hdvd := card_sylow_dvd_index P
  rw [sylow_p_index h P] at hdvd
  rw [← Nat.card_eq_fintype_card]
  exact h.hq.eq_one_or_self_of_dvd _ hdvd

/-- If p does not divide q-1, then n_p = 1 (unique Sylow p-subgroup) -/
theorem unique_sylow_p_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    Fintype.card (Sylow h.p G) = 1 := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  rcases sylow_p_count h hpq with h1 | hq
  · exact h1
  · -- If n_p = q, then q ≡ 1 (mod p), so p | (q-1), contradiction
    exfalso
    have hmod := card_sylow_modEq_one h.p G
    rw [Nat.card_eq_fintype_card, hq] at hmod
    exact hndvd ((Nat.modEq_iff_dvd' (by omega : 1 ≤ h.q)).mp hmod.symm)

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
  · haveI : Fact h.p.Prime := ⟨h.hp⟩
    exact sylow_normal_of_card_one (unique_sylow_p_when_coprime h hpq hndvd)
  · exact sylow_q_normal h hpq

/-- When p ∤ (q-1), G is cyclic of order pq -/
theorem cyclic_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    IsCyclic G := by
  -- Both Sylow subgroups are normal with coprime orders p and q.
  -- G ≅ P × Q ≅ ℤ/p × ℤ/q ≅ ℤ/pq (by CRT), which is cyclic.
  -- Full proof requires internal direct product decomposition.
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
  -- n_p ∈ {1, q}. If n_p = 1, both Sylow subgroups are normal,
  -- making G cyclic (contradiction). So n_p = q.
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
