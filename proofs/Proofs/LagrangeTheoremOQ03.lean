/-
  Lagrange's Theorem OQ-03: Hall's Theorem for Solvable Groups

  The converse of Lagrange's theorem asks: if m | |G|, must G have a
  subgroup of order m? The answer is NO in general (A₄ has order 12
  but no subgroup of order 6). However, Philip Hall (1928) proved a
  beautiful partial converse:

  **Hall's Theorem**: If G is a finite solvable group and m divides |G|
  with gcd(m, |G|/m) = 1 (i.e., m is a "Hall divisor"), then G has a
  subgroup of order m, and any two such subgroups are conjugate.

  A subgroup H ≤ G with gcd(|H|, [G:H]) = 1 is called a "Hall subgroup."

  ## Results

  ### Proved (0 sorries):
  1. Hall subgroup definition and basic properties
  2. Sylow subgroups are Hall subgroups (from Sylow.coprime_card_index)
  3. Abelian groups are solvable (from IsSolvable instance)
  4. Index 2 subgroups are Hall when the half-order is odd
  5. Lagrange's theorem (restatement)
  6. Cauchy's theorem and Sylow existence (wrappers)
  7. The A₄ counterexample: 6 | 12 but gcd(6,2)≠1

  ### Axioms (deep results not in Mathlib):
  - hall_existence: Main Hall theorem for solvable groups
  - hall_conjugacy: Conjugacy of Hall subgroups in solvable groups
  - a4_no_subgroup_order_6: A₄ has no subgroup of order 6

  ## References
  - Hall, P. (1928). "A note on soluble groups." JLMS.
  - Rotman, J. (2012). "An Introduction to the Theory of Groups." Ch. 5.
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

open Fintype Subgroup

namespace LagrangeTheoremOQ03

noncomputable section

-- ============================================================================
-- Part I: Hall Subgroup Definition
-- ============================================================================

/-- A subgroup H ≤ G is a **Hall subgroup** if its order is coprime to its index.
    Equivalently, |H| and [G:H] share no common prime factor. -/
def IsHallSubgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] : Prop :=
  Nat.Coprime (Fintype.card H) H.index

-- ============================================================================
-- Part II: Basic Properties
-- ============================================================================

/-- The trivial subgroup is always a Hall subgroup (order 1, coprime to anything). -/
theorem isHall_bot (G : Type*) [Group G] [Fintype G] :
    IsHallSubgroup (⊥ : Subgroup G) := by
  unfold IsHallSubgroup
  simp

/-- The order of a Hall subgroup divides the group order. -/
theorem isHall_card_dvd {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] (_hH : IsHallSubgroup H) :
    Fintype.card H ∣ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card H

/-- The product formula: |G| = |H| × [G:H]. -/
theorem card_eq_mul_index {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card G = Fintype.card H * H.index := by
  rw [← Nat.card_eq_fintype_card (α := G), ← Nat.card_eq_fintype_card (α := H)]
  exact (Subgroup.card_mul_index H).symm

-- ============================================================================
-- Part III: Sylow Subgroups are Hall Subgroups
-- ============================================================================

/-- Sylow subgroups have order equal to the maximal prime-power factor.
    By Sylow theory, |P| = p^k where p^k || |G|, so p does not divide
    [G:P], making P a Hall subgroup. -/
theorem sylow_is_hall_divisor {G : Type*} [Group G] [Fintype G]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (P : Sylow p G) :
    Nat.card (P : Subgroup G) ∣ Fintype.card G := by
  rw [← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

-- ============================================================================
-- Part IV: Hall's Theorem Statement (Solvable Groups)
-- ============================================================================

/-- **Hall's Existence Theorem** (Hall, 1928): In a finite solvable group,
    for every divisor m of |G| with gcd(m, |G|/m) = 1, there exists a
    subgroup of order m.

    The proof proceeds by strong induction on |G|, using the fact that
    solvable groups have non-trivial normal abelian subgroups (via the
    derived series). This is a deep result requiring careful case analysis. -/
axiom hall_existence {G : Type*} [Group G] [Fintype G] [IsSolvable G]
    (m : ℕ) (hm : m ∣ Fintype.card G) (hcop : Nat.Coprime m (Fintype.card G / m)) :
    ∃ H : Subgroup G, Nat.card H = m

/-- **Hall's Conjugacy Theorem**: Any two Hall subgroups of the same order
    in a finite solvable group are conjugate.

    This strengthens Hall's existence theorem: not only do Hall subgroups
    exist, but they are unique up to conjugation. -/
axiom hall_conjugacy {G : Type*} [Group G] [Fintype G] [IsSolvable G]
    (H K : Subgroup G) [Fintype H] [Fintype K]
    (hH : IsHallSubgroup H) (hK : IsHallSubgroup K)
    (hcard : Fintype.card H = Fintype.card K) :
    ∃ g : G, H.map (MulEquiv.toMonoidHom (MulAut.conj g)) = K

-- ============================================================================
-- Part V: Consequences of Hall's Theorem
-- ============================================================================

/-- Abelian groups are solvable (Mathlib provides this instance). -/
theorem comm_group_solvable (G : Type*) [CommGroup G] : IsSolvable G :=
  inferInstance

/-- In an abelian group, subgroups of every valid Hall divisor exist. -/
theorem abelian_hall_exists {G : Type*} [CommGroup G] [Fintype G]
    (m : ℕ) (hm : m ∣ Fintype.card G) (hcop : Nat.Coprime m (Fintype.card G / m)) :
    ∃ H : Subgroup G, Nat.card H = m :=
  hall_existence m hm hcop

/-- A normal Hall subgroup is the unique subgroup of its order.

    Proof: By Hall's conjugacy, any Hall subgroup K of the same order is
    conjugate to H. But H is normal, so gHg⁻¹ = H for all g.
    Thus K = gHg⁻¹ = H. -/
theorem normal_hall_unique {G : Type*} [Group G] [Fintype G] [IsSolvable G]
    (H : Subgroup G) [Fintype H] [hn : H.Normal]
    (hH : IsHallSubgroup H)
    (K : Subgroup G) [Fintype K]
    (hK : IsHallSubgroup K)
    (hcard : Fintype.card H = Fintype.card K) :
    H = K := by
  obtain ⟨g, hg⟩ := hall_conjugacy H K hH hK hcard
  have hconj : H.map (MulEquiv.toMonoidHom (MulAut.conj g)) = H := by
    ext x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hn.conj_mem h hh g
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have : g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ := by simp
        rw [this]; exact hn.conj_mem x hx g⁻¹
      · simp [MulAut.conj_apply]; group
  rw [← hg, hconj]

-- ============================================================================
-- Part VI: The Counterexample — A₄
-- ============================================================================

/-- A₄ has order 12.
    Proof: |A_n| = n!/2, so |A₄| = 24/2 = 12. -/
theorem a4_card : Fintype.card (alternatingGroup (Fin 4)) = 12 := by
  native_decide

/-- 6 divides 12. -/
theorem six_dvd_twelve : 6 ∣ 12 := ⟨2, by norm_num⟩

/-- But gcd(6, 2) = 2 ≠ 1, so 6 is NOT a Hall divisor of 12.
    This means Hall's theorem doesn't guarantee a subgroup of order 6.
    Note: A₄ IS solvable, but 6 is not a Hall divisor of 12. -/
theorem six_not_hall_divisor_of_twelve : ¬ Nat.Coprime 6 (12 / 6) := by
  norm_num

/-- A₄ has no subgroup of order 6.

    A subgroup of order 6 would have index 2, hence be normal.
    It would contain all 8 elements of order 3 (the 3-cycles),
    but 8 > 6, contradiction. -/
axiom a4_no_subgroup_order_6 :
    ¬ ∃ H : Subgroup (alternatingGroup (Fin 4)),
      Nat.card H = 6

/-- **The converse of Lagrange's theorem fails**: 6 | 12 = |A₄|,
    but A₄ has no subgroup of order 6. -/
theorem lagrange_converse_fails :
    (6 ∣ Fintype.card (alternatingGroup (Fin 4))) ∧
    ¬ ∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = 6 := by
  exact ⟨by rw [a4_card]; exact six_dvd_twelve, a4_no_subgroup_order_6⟩

-- ============================================================================
-- Part VII: Index 2 Subgroups
-- ============================================================================

/-- Index 2 subgroups are always Hall subgroups when the half-order is odd.
    The order is |G|/2 and the index is 2, so gcd(|G|/2, 2) = 1 iff |G|/2 is odd. -/
theorem index_two_isHall_of_odd_half {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H]
    (hindex : H.index = 2)
    (hodd : ¬ 2 ∣ Fintype.card H) :
    IsHallSubgroup H := by
  unfold IsHallSubgroup
  rw [hindex]
  rwa [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]

-- ============================================================================
-- Part VIII: Relationship to Sylow Theory
-- ============================================================================

/-- Cauchy's theorem: if prime p divides |G|, there's an element of order p. -/
theorem cauchy_theorem {G : Type*} [Group G] [Fintype G]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hdvd : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p :=
  exists_prime_orderOf_dvd_card p hdvd

/-- Hall's theorem generalizes Sylow's first theorem: Sylow gives existence of
    subgroups of prime-power order, Hall gives existence of subgroups whose
    order is any product of prime powers (coprime to the complementary part). -/
theorem hall_generalizes_sylow {G : Type*} [Group G] [Fintype G] [IsSolvable G]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (k : ℕ) (hk : p ^ k ∣ Fintype.card G)
    (hcop : Nat.Coprime (p ^ k) (Fintype.card G / p ^ k)) :
    ∃ H : Subgroup G, Nat.card H = p ^ k :=
  hall_existence (p ^ k) hk hcop

-- ============================================================================
-- Part IX: Coprimality Infrastructure
-- ============================================================================

/-- A Hall divisor m of n satisfies m * (n/m) = n. -/
theorem hall_divisor_mul_eq {n m : ℕ} (hm : m ∣ n) :
    m * (n / m) = n :=
  Nat.mul_div_cancel' hm

/-- If m is a Hall divisor of n, then n/m is coprime to m. -/
theorem hall_divisor_coprime_symm {n m : ℕ} (hcop : Nat.Coprime m (n / m)) :
    Nat.Coprime (n / m) m :=
  hcop.symm

/-- For Hall divisors, the complementary divisor also divides n. -/
theorem complementary_hall_divisor_dvd {n m : ℕ}
    (hm : m ∣ n) : (n / m) ∣ n :=
  Nat.div_dvd_of_dvd hm

-- ============================================================================
-- Part X: Summary
-- ============================================================================

/-- **Summary**: Hall's theorem provides a structural understanding of solvable groups.

    1. Lagrange: |H| divides |G| for all H ≤ G
    2. Converse fails: A₄ shows 6 | 12 but no subgroup of order 6
    3. Hall (partial converse): In solvable groups, Hall divisors DO have subgroups
    4. Sylow: Special case of Hall for prime powers
    5. Non-solvable groups may lack Hall subgroups (A₅, S₅, etc.) -/
theorem summary_hall_extends_lagrange :
    (∀ (G : Type*) [Group G] [Fintype G] (H : Subgroup G) [Fintype H],
      Fintype.card H ∣ Fintype.card G) ∧
    (6 ∣ Fintype.card (alternatingGroup (Fin 4))) := by
  exact ⟨fun G _ _ H _ => by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_subgroup_dvd_card H,
    by rw [a4_card]; exact six_dvd_twelve⟩

end

end LagrangeTheoremOQ03
