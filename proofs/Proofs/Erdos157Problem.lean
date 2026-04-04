/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 2c0deff5-83dc-45bd-a8dc-7d900c102ea5

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem example_is_sidon : IsSidon (↑exampleSidonSet : Set ℕ)
-/

/-
  Erdős Problem #157: Infinite Sidon Set as Asymptotic Basis

  Source: https://erdosproblems.com/157
  Status: SOLVED (Pilatte 2023)

  Statement:
  Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

  Answer: YES.

  Definition Recap:
  - A Sidon set (B₂ sequence) has all pairwise sums distinct: a+b = c+d implies {a,b} = {c,d}
  - An asymptotic basis of order k: every sufficiently large integer is a sum of at most k elements

  Key Results:
  - Pilatte (2023): Constructed an infinite Sidon set that is an asymptotic basis of order 3

  This file formalizes the definitions and main result.
-/

import Mathlib


open Set Finset BigOperators

namespace Erdos157

/- ## Sidon Sets -/

/-- A set A is a **Sidon set** (B₂ sequence) if all pairwise sums are distinct.
    Equivalently: a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/-- Alternative characterization: the sumset A + A has no repeated elements. -/
def IsSidonAlt (A : Set ℕ) : Prop :=
  ∀ s : ℕ, (Set.ncard { (a, b) : ℕ × ℕ | a ∈ A ∧ b ∈ A ∧ a ≤ b ∧ a + b = s }) ≤ 1

/-- The two definitions are equivalent. -/
theorem sidon_iff_sidon_alt (A : Set ℕ) : IsSidon A ↔ IsSidonAlt A := by
  constructor <;> intro h
  · intro s; by_contra! H
    obtain ⟨ x, hx ⟩ := Set.nonempty_of_ncard_ne_zero ( ne_bot_of_gt H )
    obtain ⟨ y, hy ⟩ := Set.exists_ne_of_one_lt_ncard H x
    simp_all +decide
    have := h x.1 x.2 y.1 y.2 ; aesop
  · intro a b c d ha hb hc hd hab hcd hsum
    have := h ( a + b )
    contrapose! this
    have h_two_elements : { (a, b), (c, d) } ⊆ { x : ℕ × ℕ | x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 ≤ x.2 ∧ x.1 + x.2 = a + b } := by
      aesop_cat
    have h_two_elements : Set.ncard { (a, b), (c, d) } ≤ Set.ncard { x : ℕ × ℕ | x.1 ∈ A ∧ x.2 ∈ A ∧ x.1 ≤ x.2 ∧ x.1 + x.2 = a + b } := by
      apply_rules [ Set.ncard_le_ncard ]
      exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ a + b, a + b ⟩, by rintro ⟨ x, y ⟩ ⟨ hx, hy, hxy, h ⟩ ; exact ⟨ by linarith, by linarith ⟩ ⟩
    rw [ Set.ncard_pair ] at h_two_elements <;> aesop

/- ## Asymptotic Bases -/

/-- The k-fold sumset: sums of at most k elements from A. -/
def SumsetK (A : Set ℕ) (k : ℕ) : Set ℕ :=
  { n | ∃ (S : Finset ℕ), S.card ≤ k ∧ ↑S ⊆ A ∧ n = S.sum id }

/-- A set A is an **asymptotic basis of order k** if every sufficiently large
    integer can be represented as a sum of at most k elements of A. -/
def IsAsymptoticBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ SumsetK A k

/-- A set is an **exact basis of order k** if every positive integer is
    representable (no asymptotic qualification). -/
def IsExactBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → n ∈ SumsetK A k

/- ## The Main Question -/

/--
**Erdős Problem #157 (SOLVED)**:
Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

Pilatte (2023) answered YES.
-/
def Erdos157Conjecture : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ IsSidon A ∧ IsAsymptoticBasis A 3

/- ## Pilatte's Theorem -/

/- Aristotle failed to find a proof. -/
/--
**Pilatte's Theorem (2023)**:
There exists an infinite Sidon set that is an asymptotic basis of order 3.
-/
theorem pilatte_existence : Erdos157Conjecture := by
  sorry

/- ## Counting Axioms -/

/-- Sidon sets have counting function at most √N + O(N^{1/4}). -/
axiom sidon_counting_bound (A : Set ℕ) (hSidon : IsSidon A) :
    ∃ C : ℝ, ∀ N : ℕ, (Set.ncard (A ∩ Set.Icc 1 N) : ℝ) ≤ Real.sqrt N + C * N^(1/4 : ℝ)

/-- Asymptotic bases of order k have counting function at least N^{1/k}. -/
axiom basis_counting_lower (A : Set ℕ) (k : ℕ) (hk : k ≥ 1) (hBasis : IsAsymptoticBasis A k) :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ (N : ℕ) in Filter.atTop,
      c * (N : ℝ)^(1/k : ℝ) ≤ Set.ncard (A ∩ Set.Icc 1 N)

/- ## Related Results -/

/- Aristotle failed to find a proof. -/
/-- No Sidon set can be an asymptotic basis of order 2.

**Proof strategy** (not yet formalized):
1. Assume A is Sidon and IsAsymptoticBasis A 2. Let N₀ from basis, C from sidon_counting_bound.
2. For N large, let M = |A ∩ [1,2N]| ≤ √(2N) + C*(2N)^(1/4) ≈ √2·√N.
3. ALL 2-element sums a+b (a < b, a,b ∈ A) are DISTINCT by IsSidonAlt (proved below as
   `sidon_iff_sidon_alt`), so representable integers in SumsetK A 2 that are ≤ 2N is at most
   |A ∩ [1,2N]| + C(M,2) = M·(M+1)/2.
4. M·(M+1)/2 ≤ (√(2N) + C·(2N)^(1/4))²/2 + lower order ≈ N + O(N^{3/4}).
5. But [N₀, 2N] has 2N - N₀ + 1 ≈ 2N elements that ALL must be in SumsetK A 2.
6. For large N: 2N - N₀ ≤ M·(M+1)/2 ≤ N + O(N^{3/4}), so N - O(N^{3/4}) ≤ N₀. Contradiction.

NOTE: `basis_counting_lower` is NOT sufficient for this proof because it only gives c > 0
(and c ≤ 1 is consistent with the Sidon bound). The correct proof uses direct counting
via IsSidonAlt distinctness, not via basis_counting_lower.
-/
-- Key helper: the 2-element sums in a Sidon set are distinct.
-- The map (a,b) ↦ a+b is injective on pairs with a < b in A.
private lemma sidon_pair_sum_injective (A : Set ℕ) (hSidon : IsSidon A) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2)
      {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2} := by
  intro ⟨a, b⟩ ⟨ha, hb, hab⟩ ⟨c, d⟩ ⟨hc, hd, hcd⟩ h
  simp only at h
  have := hSidon a b c d ha hb hc hd (le_of_lt hab) (le_of_lt hcd) h
  exact Prod.ext this.1 this.2

-- Key counting lemma: integers in SumsetK A 2 with value ≤ 2N
-- can be injected into A ∪ {pairs from A × A}.
-- Total target size ≤ M*(M+1)/2 where M = |A ∩ [1,2N]|.
-- Requires N₀ ≥ 1 to ensure all covered elements are positive (avoiding the n=0 edge case).
private lemma sumsetK2_ncard_le (A : Set ℕ) (_hSidon : IsSidon A) (N₀ N : ℕ)
    (hN₀_pos : 1 ≤ N₀) (hN : N₀ ≤ N)
    (hcov : ∀ n, N₀ ≤ n → n ≤ 2*N → n ∈ SumsetK A 2) :
    (2 * N - N₀ + 1 : ℝ) ≤
    (Set.ncard (A ∩ Set.Icc 1 (2*N)) : ℝ) *
    ((Set.ncard (A ∩ Set.Icc 1 (2*N)) : ℝ) + 1) / 2 := by
  -- Setup: FA = A ∩ [1,2N] as a Finset, M = FA.card
  have hfin : Set.Finite (A ∩ Set.Icc 1 (2*N)) :=
    (Set.finite_Icc 1 (2*N)).subset Set.inter_subset_right
  set FA := hfin.toFinset with hFA_def
  have hM_eq : Set.ncard (A ∩ Set.Icc 1 (2*N)) = FA.card := by
    have h : (FA : Set ℕ) = A ∩ Set.Icc 1 (2*N) := hFA_def ▸ hfin.coe_toFinset
    rw [← h, Set.ncard_coe_finset]
  rw [hM_eq]
  -- Key helper: each n in [N₀, 2N] covered by SumsetK A 2 lies in FA or is a strict Sidon pair sum
  have helem : ∀ n, N₀ ≤ n → n ≤ 2*N → n ∈ SumsetK A 2 →
      (n ∈ FA) ∨ (∃ a b : ℕ, a ∈ FA ∧ b ∈ FA ∧ a < b ∧ a + b = n) := by
    intro n hn1 hn2 ⟨S, hSc, hSsub, hSsum⟩
    -- Case on S.card
    have hSc2 : S.card ≤ 2 := hSc
    interval_cases h : S.card
    · -- S = ∅, sum = 0, contradicts n ≥ N₀ ≥ 1
      have hSempty : S = ∅ := Finset.card_eq_zero.mp h
      simp only [hSempty, Finset.sum_empty] at hSsum
      omega
    · -- S = {a}, sum = a = n
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
      simp [Finset.sum_singleton] at hSsum
      left
      rw [hFA_def, hfin.mem_toFinset]
      exact ⟨hSsum ▸ hSsub (Finset.mem_singleton_self a),
             ⟨by linarith [hN₀_pos], hn2⟩⟩
    · -- S = {a, b}, sum = a + b = n
      obtain ⟨a, b, hab_ne, rfl⟩ := Finset.card_eq_two.mp h
      simp [Finset.sum_pair hab_ne] at hSsum
      have ha_A : a ∈ A := hSsub (Finset.mem_insert_self a {b})
      have hb_A : b ∈ A := hSsub (by simp)
      -- Order a and b
      rcases Nat.lt_or_ge a b with hab | hba
      · -- a < b case
        rcases Nat.eq_zero_or_pos a with rfl | ha_pos
        · -- a = 0: n = b, treat as singleton
          simp at hSsum; left
          rw [hFA_def, hfin.mem_toFinset]
          exact ⟨hSsum ▸ hb_A, ⟨by linarith [hN₀_pos], by linarith⟩⟩
        · right
          rw [hFA_def]
          refine ⟨a, b, hfin.mem_toFinset.mpr ⟨ha_A, ⟨ha_pos, by linarith⟩⟩,
                        hfin.mem_toFinset.mpr ⟨hb_A, ⟨by linarith, by linarith⟩⟩,
                        hab, hSsum.symm⟩
      · -- b ≤ a case: swap
        rcases Nat.eq_zero_or_pos b with rfl | hb_pos
        · simp at hSsum; left
          rw [hFA_def, hfin.mem_toFinset]
          exact ⟨hSsum ▸ ha_A, ⟨by linarith [hN₀_pos], by linarith⟩⟩
        · right
          have hba_lt : b < a := Nat.lt_of_le_of_ne hba (Ne.symm hab_ne)
          rw [hFA_def]
          refine ⟨b, a, hfin.mem_toFinset.mpr ⟨hb_A, ⟨hb_pos, by linarith⟩⟩,
                        hfin.mem_toFinset.mpr ⟨ha_A, ⟨by linarith, by linarith⟩⟩,
                        hba_lt, by linarith⟩
  -- Define the representable finset
  set pairs2 := (FA ×ˢ FA).filter (fun p => p.1 < p.2) with hpairs_def
  set sums2 := pairs2.image (fun p => p.1 + p.2) with hsums_def
  set repSet := FA ∪ sums2 with hrep_def
  -- Step 1: [N₀, 2N] ⊆ repSet
  have h_sub : Finset.Icc N₀ (2*N) ⊆ repSet := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    rcases helem n hn.1 hn.2 (hcov n hn.1 hn.2) with h | ⟨a, b, ha, hb, hab, hsum⟩
    · exact Finset.mem_union_left _ h
    · apply Finset.mem_union_right
      rw [hsums_def, hpairs_def]
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩, hsum⟩
  -- Step 2: |[N₀, 2N]| ≤ |repSet|
  have h_card_le : (Finset.Icc N₀ (2*N)).card ≤ repSet.card :=
    Finset.card_le_card h_sub
  -- Step 3: |[N₀, 2N]| = 2N - N₀ + 1
  have h_icc_card : (Finset.Icc N₀ (2*N)).card = 2*N - N₀ + 1 := by
    simp; omega
  -- Step 4: |repSet| ≤ M*(M+1)/2
  have h_rep_card : 2 * repSet.card ≤ FA.card * (FA.card + 1) := by
    calc 2 * repSet.card
        ≤ 2 * (FA.card + sums2.card) := by
          apply Nat.mul_le_mul_left
          exact (Finset.card_union_le FA sums2)
      _ = 2 * FA.card + 2 * sums2.card := by ring
      _ ≤ 2 * FA.card + 2 * pairs2.card := by
          apply Nat.add_le_add_left
          apply Nat.mul_le_mul_left
          exact Finset.card_image_le
      _ ≤ 2 * FA.card + FA.card * (FA.card - 1) := by
          apply Nat.add_le_add_left
          -- |pairs2| = C(M, 2) = M*(M-1)/2, so 2*|pairs2| ≤ M*(M-1)
          have : 2 * pairs2.card ≤ FA.card * (FA.card - 1) := by
            -- pairs2 (a<b pairs) and pairs2.image Prod.swap (a>b pairs) are disjoint
            -- subsets of FA.offDiag, so 2*|pairs2| ≤ |FA.offDiag| = M*(M-1)
            have h_offDiag : FA.offDiag.card = FA.card * (FA.card - 1) := by
              have hdiag : (FA.image (fun a : ℕ => (a, a))).card = FA.card :=
                Finset.card_image_of_injective _ fun a b h => (Prod.mk.inj h).1
              have hoff_union : FA.offDiag ∪ FA.image (fun a : ℕ => (a, a)) = FA ×ˢ FA := by
                ext ⟨a, b⟩
                simp only [Finset.mem_union, Finset.mem_offDiag, Finset.mem_image,
                           Finset.mem_product]
                constructor
                · rintro (⟨ha, hb, _⟩ | ⟨c, hc, h⟩)
                  · exact ⟨ha, hb⟩
                  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨hc, hc⟩
                · intro ⟨ha, hb⟩
                  by_cases heq : a = b
                  · right; exact ⟨a, ha, Prod.ext rfl heq⟩
                  · left; exact ⟨ha, hb, heq⟩
              have hdisj : Disjoint FA.offDiag (FA.image (fun a : ℕ => (a, a))) := by
                rw [Finset.disjoint_left]
                intro ⟨a, b⟩ h1 h2
                rw [Finset.mem_offDiag] at h1
                obtain ⟨c, _, heq⟩ := Finset.mem_image.mp h2
                exact h1.2.2 ((Prod.mk.inj heq).1.symm.trans (Prod.mk.inj heq).2)
              have hsum : FA.offDiag.card + FA.card = FA.card * FA.card := by
                have h := Finset.card_union_of_disjoint hdisj
                rw [hoff_union, Finset.card_product, hdiag] at h
                linarith
              cases hm : FA.card with
              | zero =>
                have hFA_empty : FA = ∅ := Finset.card_eq_zero.mp hm
                simp [hFA_empty]
              | succ m =>
                rw [hm] at hsum
                simp only [Nat.succ_sub_one]
                have hkey : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
                  have : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
                  omega
                omega
            have h_sub : pairs2 ⊆ FA.offDiag := by
              intro ⟨a, b⟩ hmem
              simp only [hpairs_def, Finset.mem_filter, Finset.mem_product] at hmem
              simp only [Finset.mem_offDiag]
              exact ⟨hmem.1.1, hmem.1.2, Nat.ne_of_lt hmem.2⟩
            have h_swap_sub : pairs2.image Prod.swap ⊆ FA.offDiag := by
              intro ⟨a, b⟩ hmem
              rcases Finset.mem_image.mp hmem with ⟨⟨c, d⟩, hcd_mem, heq⟩
              simp only [hpairs_def, Finset.mem_filter, Finset.mem_product] at hcd_mem
              have hda : d = a := (Prod.mk.inj heq).1
              have hcb : c = b := (Prod.mk.inj heq).2
              simp only [Finset.mem_offDiag]
              exact ⟨hda ▸ hcd_mem.1.2, hcb ▸ hcd_mem.1.1, by omega⟩
            have h_disj : Disjoint pairs2 (pairs2.image Prod.swap) := by
              rw [Finset.disjoint_left]
              intro ⟨a, b⟩ h1 h2
              have hab : a < b := by
                simp only [hpairs_def, Finset.mem_filter, Finset.mem_product] at h1
                exact h1.2
              rcases Finset.mem_image.mp h2 with ⟨⟨c, d⟩, hcd_mem, heq⟩
              have hcd : c < d := by
                simp only [hpairs_def, Finset.mem_filter, Finset.mem_product] at hcd_mem
                exact hcd_mem.2
              have hda : d = a := (Prod.mk.inj heq).1
              have hcb : c = b := (Prod.mk.inj heq).2
              omega
            have h_inj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) :=
              fun ⟨a, b⟩ ⟨c, d⟩ h => by
                simp only [Prod.swap] at h
                exact Prod.ext (Prod.mk.inj h).2 (Prod.mk.inj h).1
            have h_card_eq : (pairs2.image Prod.swap).card = pairs2.card :=
              Finset.card_image_of_injective _ h_inj
            calc 2 * pairs2.card
                = pairs2.card + (pairs2.image Prod.swap).card := by linarith
              _ = (pairs2 ∪ pairs2.image Prod.swap).card :=
                    (Finset.card_union_of_disjoint h_disj).symm
              _ ≤ FA.offDiag.card :=
                    Finset.card_le_card (Finset.union_subset h_sub h_swap_sub)
              _ = FA.card * (FA.card - 1) := h_offDiag
          exact this
      _ = FA.card * (FA.card + 1) := by
          cases hm : FA.card with
          | zero => simp
          | succ m => simp only [Nat.succ_sub_one]; ring
  -- Step 5: Combine and cast to ℝ
  have hNN₀ : N₀ ≤ 2 * N := by omega
  have h_ineq : 2 * (2 * N - N₀ + 1) ≤ FA.card * (FA.card + 1) :=
    calc 2 * (2 * N - N₀ + 1)
        = 2 * (Finset.Icc N₀ (2*N)).card := by rw [h_icc_card]
      _ ≤ 2 * repSet.card := by linarith [h_card_le]
      _ ≤ FA.card * (FA.card + 1) := h_rep_card
  have h_ℝ : (2 : ℝ) * (2 * (N : ℝ) - N₀ + 1) ≤ (FA.card : ℝ) * ((FA.card : ℝ) + 1) := by
    have h := Nat.cast_le (α := ℝ).mpr h_ineq
    push_cast [Nat.cast_sub hNN₀] at h
    linarith
  linarith

-- Polynomial bound: for u ≥ 4K with |C| ≤ K-1 and K ≥ 1 and u⁴ ≥ 16*N₀,
-- we have 2Cu³ + (C²+1)u² + Cu + 2N₀ < u⁴.
private lemma poly_counting_bound (C u : ℝ) (N₀ : ℕ) (K : ℝ)
    (hK : K ≥ 1) (hC_abs : |C| ≤ K - 1) (hu : u ≥ 4 * K)
    (hu4_N0 : u ^ 4 ≥ 16 * (N₀ : ℝ)) :
    2 * C * u ^ 3 + (C ^ 2 + 1) * u ^ 2 + C * u + 2 * (N₀ : ℝ) < u ^ 4 := by
  have hK_pos : K > 0 := by linarith
  have hu_ge4 : u ≥ 4 := by nlinarith
  have hu_nn : (0 : ℝ) ≤ u := by linarith
  have hC_abs_u4 : |C| ≤ u / 4 := by
    calc |C| ≤ K - 1 := hC_abs
      _ ≤ K := by linarith
      _ ≤ u / 4 := by linarith
  obtain ⟨hC_lb, hC_ub⟩ := abs_le.mp hC_abs_u4
  nlinarith [
    mul_nonneg (show (0:ℝ) ≤ u / 4 - C from by linarith)
              (show (0:ℝ) ≤ u ^ 3 from by positivity),
    mul_nonneg (show (0:ℝ) ≤ u / 4 - C from by linarith)
              (show (0:ℝ) ≤ u / 4 + C from by linarith),
    mul_nonneg (show (0:ℝ) ≤ u ^ 2 - 16 from by nlinarith)
              (sq_nonneg u),
    mul_nonneg hu_nn (show (0:ℝ) ≤ u / 4 - C from by linarith),
    show (0:ℝ) ≤ (N₀:ℝ) from Nat.cast_nonneg _,
    sq_nonneg u
  ]

-- Real analysis: for large N, the Sidon bound M ≤ √(2N) + C*(2N)^(1/4)
-- implies M*(M+1)/2 < 2N - N₀.
-- Strategy: set u = (2N)^(1/4). Then √(2N) = u² and u⁴ = 2N.
private lemma sidon_counting_contradiction (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N ≥ N₀ ∧
    (Real.sqrt (2 * N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4)) *
    ((Real.sqrt (2 * N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4)) + 1) / 2 <
    2 * (N : ℝ) - N₀ := by
  set K := |C| + 1 with hK_def
  have hK_ge1 : K ≥ 1 := by simp only [hK_def]; linarith [abs_nonneg C]
  have hC_abs : |C| ≤ K - 1 := by simp [hK_def]
  set N_val := Nat.ceil ((4 * K) ^ 4 / 2) + 8 * N₀ + 1 with hNv_def
  use N_val
  constructor
  · have : Nat.ceil ((4 * K) ^ 4 / 2) ≥ 0 := Nat.zero_le _; omega
  · set u := (2 * (N_val : ℝ)) ^ ((1 : ℝ) / 4) with hu_def
    have hNN_nn : (0 : ℝ) ≤ 2 * N_val := by positivity
    have h_sqrt_eq : Real.sqrt (2 * (N_val : ℝ)) = u ^ 2 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast u 2, hu_def,
          ← Real.rpow_mul hNN_nn]
      norm_num
    have h_u4 : u ^ 4 = 2 * (N_val : ℝ) := by
      rw [← Real.rpow_natCast u 4, hu_def, ← Real.rpow_mul hNN_nn]
      norm_num [Real.rpow_one]
    have h2N_lb : (4 * K) ^ 4 ≤ 2 * (N_val : ℝ) := by
      have h_ceil : (4 * K) ^ 4 / 2 ≤ (Nat.ceil ((4 * K) ^ 4 / 2) : ℝ) := Nat.le_ceil _
      simp only [hNv_def]; push_cast; linarith
    have hu_nn : (0 : ℝ) ≤ u := Real.rpow_nonneg (by linarith) _
    have hu_lb : u ≥ 4 * K := by
      by_contra h
      push_neg at h
      have h1 : (0:ℝ) < 4 * K - u := by linarith
      have h2 : (0:ℝ) < 4 * K + u := by
        have hK_pos : (0:ℝ) < K := by linarith
        linarith
      have h3 : (0:ℝ) < (4 * K) ^ 2 - u ^ 2 := by nlinarith [mul_pos h1 h2]
      have h4 : (0:ℝ) < (4 * K) ^ 2 + u ^ 2 := by positivity
      exact absurd (by nlinarith [mul_pos h3 h4] : u ^ 4 < (4 * K) ^ 4) (by linarith [h_u4, h2N_lb])
    have hu4_N0 : u ^ 4 ≥ 16 * (N₀ : ℝ) := by
      rw [h_u4]; simp only [hNv_def]; push_cast
      linarith [show (0:ℝ) ≤ (Nat.ceil ((4 * K) ^ 4 / 2):ℝ) from Nat.cast_nonneg _]
    have h_poly := poly_counting_bound C u N₀ K hK_ge1 hC_abs hu_lb hu4_N0
    rw [h_sqrt_eq]
    have h_ring : (u ^ 2 + C * u) * (u ^ 2 + C * u + 1) / 2 =
        (u ^ 4 + 2 * C * u ^ 3 + (C ^ 2 + 1) * u ^ 2 + C * u) / 2 := by ring
    linarith [h_ring, h_u4, h_poly, show (0:ℝ) ≤ (N₀:ℝ) from Nat.cast_nonneg _]

/-- No Sidon set can be an asymptotic basis of order 2.

**Proof strategy** (not yet formalized):
1. Assume A is Sidon and IsAsymptoticBasis A 2. Let N₀ from basis, C from sidon_counting_bound.
2. For N large, let M = |A ∩ [1,2N]| ≤ √(2N) + C*(2N)^(1/4) ≈ √2·√N.
3. ALL 2-element sums a+b (a < b, a,b ∈ A) are DISTINCT by IsSidonAlt (proved below as
   `sidon_iff_sidon_alt`), so representable integers in SumsetK A 2 that are ≤ 2N is at most
   |A ∩ [1,2N]| + C(M,2) = M·(M+1)/2.
4. M·(M+1)/2 ≤ (√(2N) + C·(2N)^(1/4))²/2 + lower order ≈ N + O(N^{3/4}).
5. But [N₀, 2N] has 2N - N₀ + 1 ≈ 2N elements that ALL must be in SumsetK A 2.
6. For large N: 2N - N₀ ≤ M·(M+1)/2 ≤ N + O(N^{3/4}), so N - O(N^{3/4}) ≤ N₀. Contradiction.

NOTE: `basis_counting_lower` is NOT sufficient for this proof because it only gives c > 0
(and c ≤ 1 is consistent with the Sidon bound). The correct proof uses direct counting
via IsSidonAlt distinctness, not via basis_counting_lower.
-/
theorem sidon_not_basis_2 (A : Set ℕ) (_hA : A.Infinite) (hSidon : IsSidon A) :
    ¬IsAsymptoticBasis A 2 := by
  intro hBasis
  -- Step 1: Extract N₀ (coverage threshold) and C (Sidon counting constant)
  obtain ⟨N₀, hN₀⟩ := hBasis
  obtain ⟨C, hC⟩ := sidon_counting_bound A hSidon
  -- Use N₀' = max N₀ 1 to ensure N₀' ≥ 1 (required by sumsetK2_ncard_le)
  let N₀' : ℕ := max N₀ 1
  have hN₀'_pos : 1 ≤ N₀' := le_max_right _ _
  have hN₀'_ge : N₀ ≤ N₀' := le_max_left _ _
  -- Step 2: Find N large enough for contradiction
  obtain ⟨N, hNN₀', hcontra⟩ := sidon_counting_contradiction C N₀'
  -- Step 3: At N, all integers in [N₀', 2N] are representable (from hN₀)
  have hcov : ∀ n, N₀' ≤ n → n ≤ 2*N → n ∈ SumsetK A 2 :=
    fun n hn₁ _ => hN₀ n (Nat.le_trans hN₀'_ge hn₁)
  -- Step 4: By counting lemma, M*(M+1)/2 ≥ 2N - N₀' + 1
  have hcount := sumsetK2_ncard_le A hSidon N₀' N hN₀'_pos hNN₀' hcov
  -- Step 5: Sidon bound: M = |A ∩ [1,2N]| ≤ √(2N) + C*(2N)^(1/4)
  -- Step 6: Derive contradiction: M*(M+1)/2 < 2N - N₀' ≤ M*(M+1)/2
  have hMbound : (Set.ncard (A ∩ Set.Icc 1 (2 * N)) : ℝ) ≤
      Real.sqrt (2 * ↑N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4) := by
    have h := hC (2 * N); push_cast at h; linarith
  have hprod : (Set.ncard (A ∩ Set.Icc 1 (2 * N)) : ℝ) *
      ((Set.ncard (A ∩ Set.Icc 1 (2 * N)) : ℝ) + 1) / 2 ≤
      (Real.sqrt (2 * N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4)) *
      ((Real.sqrt (2 * N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4)) + 1) / 2 := by
    -- Use: M ≤ A → M*(M+1)/2 ≤ A*(A+1)/2, which follows since A*(A+1) - M*(M+1) = (A-M)*(A+M+1) ≥ 0
    have hM_nn : (0 : ℝ) ≤ (Set.ncard (A ∩ Set.Icc 1 (2 * N)) : ℝ) := Nat.cast_nonneg _
    have hD := hMbound  -- M ≤ bound
    nlinarith [hM_nn, hD, sq_nonneg (Real.sqrt (2 * N) + C * (2 * ↑N : ℝ) ^ ((1 : ℝ) / 4) -
                                     (Set.ncard (A ∩ Set.Icc 1 (2 * N)) : ℝ))]
  linarith

/- ## Construction Outline

Pilatte's construction uses a probabilistic method combined with careful
analysis of the Sidon condition and sumset structure.

The key insight is that while Sidon sets are sparse (∼ √N elements up to N),
they are dense enough to form an asymptotic basis of order 3 because
3√N > N^{1/3} for large N.

References:
- Pilatte (2023): "An infinite Sidon set which is an asymptotic basis of order 3"
- Erdős-Turán (1941): Original bounds on Sidon sets
-/

/- ## Small Examples -/

/-- The set {1, 2, 4, 8, ...} (powers of 2) is a Sidon set. -/
theorem powers_of_two_sidon : IsSidon { n | ∃ k : ℕ, n = 2^k } := by
  intro a b c d
  rintro ⟨k, rfl⟩ ⟨l, rfl⟩ ⟨m, rfl⟩ ⟨n, rfl⟩ hab hcd hsum
  have h_factor : 2 ^ k * (1 + 2 ^ (l - k)) = 2 ^ m * (1 + 2 ^ (n - m)) := by
    simp +decide [ mul_add, ← pow_add,
      add_tsub_cancel_of_le ( show k ≤ l from le_of_not_gt fun h => by linarith [ pow_lt_pow_right₀ ( show 1 < 2 by decide ) h ] ),
      add_tsub_cancel_of_le ( show m ≤ n from le_of_not_gt fun h => by linarith [ pow_lt_pow_right₀ ( show 1 < 2 by decide ) h ] ) ]
    exact_mod_cast hsum
  have := congr_arg ( ·.factorization 2 ) h_factor ; norm_num at this
  rcases x : l - k with ( _ | _ | l' ) <;> rcases y : n - m with ( _ | _ | n' ) <;>
    simp_all +decide [ Nat.factorization_eq_zero_of_not_dvd, ← even_iff_two_dvd, parity_simps ]
  · subst_vars; ring_nf at h_factor; norm_num at h_factor
  · subst this; ring_nf at *; aesop
  · ring_nf at * ; aesop
  · simp_all +decide [ pow_succ, mul_assoc ]

/-- A valid Sidon set (no repeated sums). -/
def exampleSidonSet : Finset ℕ := {1, 2, 5, 11}

/-- The example set is Sidon.
    Note: The original set {1, 2, 5, 10, 11, 13} was NOT Sidon since 1+11 = 2+10 = 12.
    Aristotle proof search discovered this bug. -/
theorem example_is_sidon : IsSidon (↑exampleSidonSet : Set ℕ) := by
  simp_all +arith +decide [ Erdos157.exampleSidonSet ];
  rintro a b c d ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) ( rfl | rfl | rfl | rfl ) <;> trivial

end Erdos157