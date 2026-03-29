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
-/

/-- A group has order pq for distinct primes p, q -/
structure IsPQGroup (G : Type*) [Group G] [Fintype G] where
  p : ℕ
  q : ℕ
  hp : Nat.Prime p
  hq : Nat.Prime q
  hpq : p ≠ q
  hcard : Fintype.card G = p * q

-- ══════════════════════════════════════════════════════════════════
-- § Infrastructure
-- ══════════════════════════════════════════════════════════════════

/-- For distinct primes, the factorization of the second in the product. -/
private lemma factorization_mul_prime_right {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p * q).factorization q = 1 := by
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero,
      Finsupp.coe_add, Pi.add_apply, hq.factorization_self]
  suffices p.factorization q = 0 by omega
  simp [Nat.Prime.factorization, hp.factorization, Finsupp.single_apply, hne]

/-- For distinct primes, the factorization of the first in the product. -/
private lemma factorization_mul_prime_left {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p * q).factorization p = 1 := by
  rw [mul_comm]; exact factorization_mul_prime_right hq hp hne.symm

/-- A Sylow subgroup is normal when it is the unique one. -/
private theorem Sylow.normal_of_subsingleton' {p : ℕ} [Fact p.Prime]
    [Subsingleton (Sylow p G)] (P : Sylow p G) :
    (↑P : Subgroup G).Normal :=
  Subgroup.normalizer_eq_top.mp (by
    ext g; simp only [mem_top, iff_true]
    exact Sylow.smul_eq_iff_mem_normalizer.mp (Subsingleton.elim _ _))

/-- An element of prime order p belongs to the unique normal Sylow p-subgroup. -/
private theorem mem_unique_sylow {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [Unique (Sylow p G)]
    {a : G} (ha : orderOf a = p) :
    a ∈ (↑P : Subgroup G) := by
  have h_pgrp : IsPGroup p (zpowers a) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, ha]⟩
  obtain ⟨R, hR⟩ := h_pgrp.exists_le_sylow
  exact congr_arg Sylow.toSubgroup (Subsingleton.elim R P) ▸ hR (mem_zpowers a)

/-- Elements from disjoint normal subgroups commute. -/
private theorem commute_of_disjoint_normal {H K : Subgroup G}
    [hHn : H.Normal] [hKn : K.Normal] (hdisj : H ⊓ K = ⊥)
    {a b : G} (ha : a ∈ H) (hb : b ∈ K) : Commute a b := by
  suffices h : a * b * a⁻¹ * b⁻¹ = 1 by
    rw [Commute, SemiconjBy]
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = 1 * (b * a) := by rw [h]
      _ = b * a := one_mul _
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ H ⊓ K := by
    constructor
    · have h1 : b * a⁻¹ * b⁻¹ ∈ H := hHn.conj_mem a⁻¹ (H.inv_mem ha) b
      have h2 : a * (b * a⁻¹ * b⁻¹) ∈ H := H.mul_mem ha h1
      convert h2 using 1; group
    · exact K.mul_mem (hKn.conj_mem b hb a) (K.inv_mem hb)
  rw [hdisj, mem_bot] at hmem
  exact hmem

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Sylow q-subgroup is Unique
-- ══════════════════════════════════════════════════════════════════

/-- For p < q distinct primes, there is exactly one Sylow q-subgroup -/
theorem unique_sylow_q (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.q G) = 1 := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  rw [← Nat.card_eq_fintype_card]
  have hmod : Nat.card (Sylow h.q G) ≡ 1 [MOD h.q] := card_sylow_modEq_one h.q G
  obtain ⟨P⟩ := Sylow.nonempty (p := h.q) (G := G)
  have hdvd : Nat.card (Sylow h.q G) ∣ (↑P : Subgroup G).index :=
    card_sylow_dvd_index P
  have hP_card : Nat.card (↑P : Subgroup G) = h.q := by
    have h1 := P.card_eq_multiplicity
    rw [Nat.card_eq_fintype_card (α := G), h.hcard,
        factorization_mul_prime_right h.hp h.hq h.hpq, pow_one] at h1
    exact h1
  have hidx : (↑P : Subgroup G).index = h.p := by
    have hlag := (↑P : Subgroup G).index_mul_card
    rw [Nat.card_eq_fintype_card (α := G), h.hcard, hP_card] at hlag
    have := h.hq.pos; omega
  rw [hidx] at hdvd
  rcases h.hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hmod
    have : h.p % h.q = 1 % h.q := hmod
    rw [Nat.mod_eq_of_lt (by omega : h.p < h.q),
        Nat.mod_eq_of_lt (by omega : 1 < h.q)] at this
    linarith [h.hp.two_le]

/-- The unique Sylow q-subgroup is normal -/
theorem sylow_q_normal (h : IsPQGroup G) (hpq : h.p < h.q) :
    ∃ Q : Sylow h.q G, (Q : Subgroup G).Normal := by
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  haveI : Subsingleton (Sylow h.q G) := by
    rw [← Fintype.card_le_one_iff_subsingleton]; exact le_of_eq (unique_sylow_q h hpq)
  obtain ⟨Q⟩ := Sylow.nonempty (p := h.q) (G := G)
  exact ⟨Q, Sylow.normal_of_subsingleton' Q⟩

-- ══════════════════════════════════════════════════════════════════
-- § Part III: Sylow p-subgroup Analysis
-- ══════════════════════════════════════════════════════════════════

/-- The number of Sylow p-subgroups is either 1 or q -/
theorem sylow_p_count (h : IsPQGroup G) (hpq : h.p < h.q) :
    Fintype.card (Sylow h.p G) = 1 ∨ Fintype.card (Sylow h.p G) = h.q := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  obtain ⟨P⟩ := Sylow.nonempty (p := h.p) (G := G)
  have hdvd : Nat.card (Sylow h.p G) ∣ (↑P : Subgroup G).index :=
    card_sylow_dvd_index P
  have hP_card : Nat.card (↑P : Subgroup G) = h.p := by
    have h1 := P.card_eq_multiplicity
    rw [Nat.card_eq_fintype_card (α := G), h.hcard,
        factorization_mul_prime_left h.hp h.hq h.hpq, pow_one] at h1
    exact h1
  have hidx : (↑P : Subgroup G).index = h.q := by
    have hlag := (↑P : Subgroup G).index_mul_card
    rw [Nat.card_eq_fintype_card (α := G), h.hcard, hP_card] at hlag
    have := h.hp.pos; omega
  rw [hidx] at hdvd
  exact h.hq.eq_one_or_self_of_dvd _ hdvd

/-- If p does not divide q-1, then n_p = 1 (unique Sylow p-subgroup) -/
theorem unique_sylow_p_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    Fintype.card (Sylow h.p G) = 1 := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  rcases sylow_p_count h hpq with h1 | h1
  · exact h1
  · exfalso
    have hmod : Nat.card (Sylow h.p G) ≡ 1 [MOD h.p] := card_sylow_modEq_one h.p G
    rw [← Nat.card_eq_fintype_card, h1] at hmod
    exact hndvd ((Nat.modEq_iff_dvd' (by omega : 1 ≤ h.q)).mp hmod)

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: The Cyclic Case
-- ══════════════════════════════════════════════════════════════════

/-- If p ∤ (q-1), both Sylow subgroups are normal -/
theorem both_normal_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    (∃ P : Sylow h.p G, (P : Subgroup G).Normal) ∧
    (∃ Q : Sylow h.q G, (Q : Subgroup G).Normal) := by
  constructor
  · haveI : Fact h.p.Prime := ⟨h.hp⟩
    haveI : Subsingleton (Sylow h.p G) := by
      rw [← Fintype.card_le_one_iff_subsingleton]
      exact le_of_eq (unique_sylow_p_when_coprime h hpq hndvd)
    obtain ⟨P⟩ := Sylow.nonempty (p := h.p) (G := G)
    exact ⟨P, Sylow.normal_of_subsingleton' P⟩
  · exact sylow_q_normal h hpq

/-- Core: if both Sylow subgroups of a pq-group are normal, G is cyclic. -/
private theorem cyclic_of_both_sylow_normal (h : IsPQGroup G) (hpq : h.p < h.q)
    (P : Sylow h.p G) (Q : Sylow h.q G)
    (hPn : (↑P : Subgroup G).Normal) (hQn : (↑Q : Subgroup G).Normal) :
    IsCyclic G := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  haveI := hPn; haveI := hQn
  -- P and Q are disjoint (coprime prime orders)
  have hdisj : (↑P : Subgroup G) ⊓ (↑Q : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    obtain ⟨hxP, hxQ⟩ := mem_inf.mp hx
    obtain ⟨j, hj⟩ := P.isPGroup' ⟨x, hxP⟩
    obtain ⟨l, hl⟩ := Q.isPGroup' ⟨x, hxQ⟩
    have hj' : x ^ h.p ^ j = 1 := by exact_mod_cast hj
    have hl' : x ^ h.q ^ l = 1 := by exact_mod_cast hl
    have h_ord_p := orderOf_dvd_of_pow_eq_one hj'
    have h_ord_q := orderOf_dvd_of_pow_eq_one hl'
    have hcop : Nat.Coprime (h.p ^ j) (h.q ^ l) :=
      ((Nat.coprime_primes h.hp h.hq).mpr h.hpq).pow_pow
    have h_dvd_one : orderOf x ∣ 1 := by
      calc orderOf x ∣ Nat.gcd (h.p ^ j) (h.q ^ l) := Nat.dvd_gcd h_ord_p h_ord_q
        _ = 1 := hcop
    rwa [Nat.dvd_one.mp h_dvd_one, orderOf_eq_one_iff] at h_dvd_one
  -- Get elements of order p and q
  have hp_dvd : h.p ∣ Fintype.card G := h.hcard ▸ dvd_mul_right h.p h.q
  have hq_dvd : h.q ∣ Fintype.card G := h.hcard ▸ dvd_mul_left h.q h.p
  obtain ⟨a, ha_ord⟩ := exists_prime_orderOf_dvd_card h.p hp_dvd
  obtain ⟨b, hb_ord⟩ := exists_prime_orderOf_dvd_card h.q hq_dvd
  -- Elements are in their respective Sylow subgroups
  haveI : Unique (Sylow h.p G) := Sylow.unique_of_normal P hPn
  haveI : Unique (Sylow h.q G) := Sylow.unique_of_normal Q hQn
  have ha_mem : a ∈ (↑P : Subgroup G) := mem_unique_sylow P ha_ord
  have hb_mem : b ∈ (↑Q : Subgroup G) := mem_unique_sylow Q hb_ord
  -- They commute (disjoint normal subgroups)
  have hab : Commute a b := commute_of_disjoint_normal hdisj ha_mem hb_mem
  -- Product has order pq = |G|
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [ha_ord, hb_ord]; exact (Nat.coprime_primes h.hp h.hq).mpr h.hpq
  have hord : orderOf (a * b) = h.p * h.q := by
    rw [hab.orderOf_mul_eq_mul_orderOf_of_coprime hcop, ha_ord, hb_ord]
  -- zpowers (a * b) = ⊤, hence IsCyclic
  have htop : zpowers (a * b) = ⊤ := by
    apply eq_top_of_card_eq
    simp only [Fintype.card_zpowers, hord, h.hcard]
  exact ⟨⟨a * b, fun g => by rw [htop]; exact mem_top g⟩⟩

/-- When p ∤ (q-1), G is cyclic of order pq -/
theorem cyclic_when_coprime (h : IsPQGroup G) (hpq : h.p < h.q)
    (hndvd : ¬ (h.p ∣ h.q - 1)) :
    IsCyclic G := by
  obtain ⟨⟨P, hPn⟩, ⟨Q, hQn⟩⟩ := both_normal_when_coprime h hpq hndvd
  exact cyclic_of_both_sylow_normal h hpq P Q hPn hQn

/-
## Part V: The Non-Abelian Case (when p | (q-1))
-/

/-- When p | (q-1), the non-cyclic group exists -/
def nonAbelianPQExists (p q : ℕ) (_ : Nat.Prime p) (_ : Nat.Prime q)
    (_ : p < q) (_ : p ∣ q - 1) : Prop :=
  ∃ (G : Type*) (_ : Group G) (_ : Fintype G),
    Fintype.card G = p * q ∧ ¬ IsCyclic G

/-- When not cyclic and p | (q-1), n_p = q -/
theorem nonabelian_sylow_p_count (h : IsPQGroup G) (hpq : h.p < h.q)
    (_ : h.p ∣ h.q - 1) (hncyc : ¬ IsCyclic G) :
    Fintype.card (Sylow h.p G) = h.q := by
  haveI : Fact h.p.Prime := ⟨h.hp⟩
  haveI : Fact h.q.Prime := ⟨h.hq⟩
  rcases sylow_p_count h hpq with h1 | h1
  · exfalso
    haveI : Subsingleton (Sylow h.p G) := by
      rw [← Fintype.card_le_one_iff_subsingleton]; exact le_of_eq h1
    obtain ⟨P⟩ := Sylow.nonempty (p := h.p) (G := G)
    have hPn := Sylow.normal_of_subsingleton' P
    obtain ⟨Q, hQn⟩ := sylow_q_normal h hpq
    exact hncyc (cyclic_of_both_sylow_normal h hpq P Q hPn hQn)
  · exact h1

/-
## Part VI: Complete Classification
-/

/-- **Classification of groups of order pq**:
    - If p ∤ (q-1): G is cyclic (unique up to isomorphism)
    - If p | (q-1): G is either cyclic or a unique non-abelian group -/
def pqClassification (p q : ℕ) (_ : Nat.Prime p) (_ : Nat.Prime q)
    (_ : p < q) : Prop :=
  if ¬ (p ∣ q - 1) then
    ∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = p * q → IsCyclic G
  else
    True

/-- When p ∤ (q-1), every group of order pq is cyclic -/
theorem pq_cyclic_classification (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p < q) (hndvd : ¬ (p ∣ q - 1)) :
    ∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = p * q → IsCyclic G := by
  intro G _ _ hcard
  exact cyclic_when_coprime ⟨p, q, hp, hq, Nat.ne_of_lt hpq, hcard⟩ hpq hndvd

/-
## Part VII: Concrete Examples
-/

/-- Groups of order 15 = 3 × 5: since 3 ∤ (5-1) = 4, only ℤ/15 -/
theorem order_15_cyclic : ¬ (3 ∣ 5 - 1) := by omega

/-- Groups of order 6 = 2 × 3: since 2 | (3-1) = 2, two groups -/
theorem order_6_has_nonabelian : 2 ∣ (3 - 1) := by omega

/-- Groups of order 35 = 5 × 7: since 5 ∤ (7-1) = 6, only ℤ/35 -/
theorem order_35_cyclic : ¬ (5 ∣ 7 - 1) := by omega

/-- Groups of order 21 = 3 × 7: since 3 | (7-1) = 6, two groups -/
theorem order_21_has_nonabelian : 3 ∣ (7 - 1) := by omega

#check IsPQGroup
#check pqClassification
#check pq_cyclic_classification

end SylowPQ
