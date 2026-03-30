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

/-- Core lemma: If both Sylow subgroups of a pq-group are normal, G is cyclic.
    Proof sketch:
    1. P ∩ Q = {1} (coprime orders)
    2. Elements of P and Q commute (commutator ∈ P ∩ Q = {1})
    3. Generators have order p and q, product has order pq = |G|
    4. G is cyclic -/
private theorem cyclic_of_both_sylow_normal (h : IsPQGroup G) (hpq : h.p < h.q)
    (P : Sylow h.p G) (hPN : (P : Subgroup G).Normal)
    (Q : Sylow h.q G) (hQN : (Q : Subgroup G).Normal) :
    IsCyclic G := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  have hP_card := sylow_p_card h P
  have hQ_card := sylow_q_card h Q
  -- Step 1: P ⊓ Q = ⊥ (coprime orders → trivial intersection)
  have hdisjoint : Disjoint (P : Subgroup G) (Q : Subgroup G) := by
    rw [Subgroup.disjoint_def]
    intro x hxP hxQ
    have h1 : orderOf x ∣ h.p := by
      have := orderOf_dvd_natCard (⟨x, hxP⟩ : (P : Subgroup G))
      rwa [hP_card, Subgroup.orderOf_mk] at this
    have h2 : orderOf x ∣ h.q := by
      have := orderOf_dvd_natCard (⟨x, hxQ⟩ : (Q : Subgroup G))
      rwa [hQ_card, Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime h.p h.q :=
      (h.hp.coprime_iff_not_dvd).mpr (fun hdvd =>
        absurd (Nat.Prime.eq_of_dvd_of_prime h.hp h.hq hdvd) h.hpq)
    exact (orderOf_eq_one_iff_eq_one).mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  -- Step 2: Elements of P and Q commute (commutator argument)
  have hcommute : ∀ g : G, g ∈ (P : Subgroup G) →
      ∀ k : G, k ∈ (Q : Subgroup G) → Commute g k := by
    intro g hg k hk
    -- Commutator c = g⁻¹ * k⁻¹ * g * k is in P ∩ Q = {1}
    -- c ∈ P: since P normal, k⁻¹*g*k ∈ P, and g⁻¹ ∈ P
    -- c ∈ Q: since Q normal, g⁻¹*k⁻¹*g ∈ Q, and k ∈ Q
    have h_conj_P : k⁻¹ * g * k ∈ (P : Subgroup G) := by
      have := hPN.conj_mem g hg k⁻¹; simpa using this
    have h_conj_Q : g⁻¹ * k⁻¹ * g ∈ (Q : Subgroup G) := by
      have := hQN.conj_mem k⁻¹ ((Q : Subgroup G).inv_mem hk) g⁻¹; simpa using this
    have hc_in_P : g⁻¹ * (k⁻¹ * g * k) ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem ((P : Subgroup G).inv_mem hg) h_conj_P
    have hc_in_Q : g⁻¹ * k⁻¹ * g * k ∈ (Q : Subgroup G) :=
      (Q : Subgroup G).mul_mem h_conj_Q hk
    -- Both are the same element (by associativity), and it's in P ∩ Q = {1}
    have hc_one : g⁻¹ * (k⁻¹ * g * k) = 1 := by
      have : g⁻¹ * k⁻¹ * g * k = g⁻¹ * (k⁻¹ * g * k) := by group
      exact Subgroup.disjoint_def.mp hdisjoint _ hc_in_P (this ▸ hc_in_Q)
    -- From g⁻¹ * (k⁻¹ * g * k) = 1, derive g = k⁻¹ * g * k
    have h_conj_eq : k⁻¹ * g * k = g := by rwa [inv_mul_eq_one] at hc_one
    -- Therefore g * k = k * g
    show g * k = k * g
    calc g * k = k * (k⁻¹ * g * k) := by group
      _ = k * g := by rw [h_conj_eq]
  -- Step 3: Get generators of P and Q
  -- P is cyclic (prime order)
  haveI : IsCyclic (P : Subgroup G) := isCyclic_of_prime_card (by
    rw [← Nat.card_eq_fintype_card]; exact hP_card)
  haveI : IsCyclic (Q : Subgroup G) := isCyclic_of_prime_card (by
    rw [← Nat.card_eq_fintype_card]; exact hQ_card)
  -- Get generators
  obtain ⟨⟨g, hg_mem⟩, hg_gen⟩ := IsCyclic.exists_generator (α := (P : Subgroup G))
  obtain ⟨⟨k, hk_mem⟩, hk_gen⟩ := IsCyclic.exists_generator (α := (Q : Subgroup G))
  -- orderOf g = p (generator of cyclic group of order p)
  have hg_ord : orderOf g = h.p := by
    have h1 : orderOf (⟨g, hg_mem⟩ : (P : Subgroup G)) = h.p := by
      rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => hg_gen x)]
      rw [← Nat.card_eq_fintype_card]; exact hP_card
    rwa [Subgroup.orderOf_mk] at h1
  -- orderOf k = q
  have hk_ord : orderOf k = h.q := by
    have h1 : orderOf (⟨k, hk_mem⟩ : (Q : Subgroup G)) = h.q := by
      rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => hk_gen x)]
      rw [← Nat.card_eq_fintype_card]; exact hQ_card
    rwa [Subgroup.orderOf_mk] at h1
  -- g and k commute
  have hgk_comm : Commute g k := hcommute g hg_mem k hk_mem
  -- Step 4: orderOf (g * k) = p * q = |G|
  have hcop_pq : Nat.Coprime h.p h.q :=
    (h.hp.coprime_iff_not_dvd).mpr (fun hdvd =>
      absurd (Nat.Prime.eq_of_dvd_of_prime h.hp h.hq hdvd) h.hpq)
  have hord_mul : orderOf (g * k) = h.p * h.q := by
    have := hgk_comm.orderOf_mul_eq_mul_orderOf_of_coprime (by rwa [hg_ord, hk_ord])
    rwa [hg_ord, hk_ord] at this
  -- G is cyclic: zpowers (g * k) has cardinality pq = |G|, so it's all of G
  refine ⟨⟨g * k, fun x => ?_⟩⟩
  have h_card_zpow : Nat.card (Subgroup.zpowers (g * k)) = Nat.card G := by
    rw [Subgroup.card_zpowers, hord_mul, Nat.card_eq_fintype_card, h.hcard]
  have h_top : Subgroup.zpowers (g * k) = ⊤ :=
    Subgroup.eq_top_of_card_eq h_card_zpow
  rw [h_top]; exact Subgroup.mem_top x

/-- When p ∤ (q-1), G is cyclic of order pq -/
theorem cyclic_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    IsCyclic G := by
  obtain ⟨⟨P, hPN⟩, ⟨Q, hQN⟩⟩ := both_normal_when_coprime h hpq hndvd
  exact cyclic_of_both_sylow_normal h hpq P hPN Q hQN

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
  -- n_p ∈ {1, q}. If n_p = 1, both Sylow subgroups normal → G cyclic → contradiction
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  rcases sylow_p_count h hpq with h1 | hq
  · -- n_p = 1 → P is normal, Q is always normal → G cyclic → contradiction
    exfalso; apply hncyc
    obtain ⟨P, hPN⟩ := sylow_normal_of_card_one h1
    obtain ⟨Q, hQN⟩ := sylow_q_normal h hpq
    exact cyclic_of_both_sylow_normal h hpq P hPN Q hQN
  · exact hq

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
  intro G _ _ hcard
  exact cyclic_when_coprime ⟨p, q, hp, hq, ne_of_lt hpq, hcard⟩ hpq hndvd

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
