/-
Erdős Problem #476, Open Question 5: Vosper's Theorem (1956)

Source: Follow-up to erdos-476 (Erdős-Heilbronn conjecture)
Status: PARTIAL — ap_of_near_periodic proved (orbit-cardinality argument);
                   vosper_base proved; vosper_ap_sdiff_card proved (hpos: linear_combination);
                   isAP_sdiff_card proved; vosper_case1_exists sorryed (1 sorry remains)

Statement (Vosper 1956):
Let p be prime, A, B ⊆ Z/pZ with |A|, |B| ≥ 2.
If |A + B| = |A| + |B| - 1 (Cauchy-Davenport equality) and |A + B| < p,
then A and B are arithmetic progressions with the same common difference d.

Proof of ap_of_near_periodic (orbit-cardinality argument):
  b₀ = unique element of B \ B.image(·+d) (no predecessor in B).
  By strong induction: suppose b₀,...,b₀+k*d ∈ B but b₀+(k+1)*d ∉ B.
  S = B \ {b₀,...,b₀+k*d} is nonempty (since k+1 < |B|) and closed under b ↦ b-d.
  Any x₀ ∈ S generates {x₀ - n*d : n=0,...,p-1} ⊆ S of size p > |B|. Contradiction.

References:
  - Vosper, A.G. (1956)
  - Nathanson (1996): Additive Number Theory §2.4
  - Mathlib: ZMod.cauchy_davenport
-/

import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.NAry
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Arithmetic Progressions in ZMod p -/

/-- An arithmetic progression in ZMod p starting at `a` with difference `d` -/
def IsArithmeticProgression (A : Finset (ZMod p)) (a d : ZMod p) : Prop :=
  A = (Finset.range A.card).image (fun (i : ℕ) => a + (i : ZMod p) * d)

/-! ### Basic AP Infrastructure -/

lemma shift_card_eq (B : Finset (ZMod p)) (d : ZMod p) :
    (B.image (· + d)).card = B.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  have h := congrArg (· - d) hxy
  simp only [add_sub_cancel_right] at h
  exact h

lemma isAP_singleton (a d : ZMod p) :
    IsArithmeticProgression ({a} : Finset (ZMod p)) a d := by
  simp [IsArithmeticProgression]

lemma isAP_pair (a b : ZMod p) (hab : a ≠ b) :
    IsArithmeticProgression ({a, b} : Finset (ZMod p)) a (b - a) := by
  unfold IsArithmeticProgression
  rw [Finset.card_pair hab]
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, by push_cast; ring⟩
    · exact ⟨1, by omega, by push_cast; ring⟩
  · rintro ⟨i, hi, rfl⟩
    have h_cases : i = 0 ∨ i = 1 := by omega
    rcases h_cases with rfl | rfl
    · left; push_cast; ring
    · right; push_cast; ring

lemma isAP_shift (A : Finset (ZMod p)) (a d c : ZMod p)
    (h : IsArithmeticProgression A a d) :
    IsArithmeticProgression (A.image (· + c)) (a + c) d := by
  unfold IsArithmeticProgression at h ⊢
  rw [shift_card_eq A c]
  conv_lhs => rw [h]
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_apply]; ring

/-! ### AP Sum Infrastructure -/

/-- If A is an AP with diff d and has ≥ 2 elements, then d ≠ 0. -/
private lemma d_ne_zero_of_isAP {A : Finset (ZMod p)} {a d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hcard : 2 ≤ A.card) : d ≠ 0 := by
  intro hd
  have hAcard : A.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [IsArithmeticProgression, hd] at hA
    simp only [mul_zero, add_zero] at hA
    rw [hA] at hx hy
    simp only [Finset.mem_image, Finset.mem_range] at hx hy
    obtain ⟨_, _, rfl⟩ := hx
    obtain ⟨_, _, rfl⟩ := hy
    rfl
  omega

/-- The pointwise sum of two AP-sets equals the expected range image. -/
private lemma add_isAP_eq {A B : Finset (ZMod p)} {a b d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hB : IsArithmeticProgression B b d)
    (hApos : 0 < A.card) (hBpos : 0 < B.card) :
    A + B = (Finset.range (A.card + B.card - 1)).image (fun (k : ℕ) => (a + b) + (k : ZMod p) * d) := by
  apply Finset.Subset.antisymm
  · -- Forward: A + B ⊆ range.image
    intro x hx
    simp only [Finset.mem_add] at hx
    obtain ⟨xa, hxaA, xb, hxbB, rfl⟩ := hx
    rw [hA] at hxaA; rw [hB] at hxbB
    simp only [Finset.mem_image, Finset.mem_range] at hxaA hxbB
    obtain ⟨i, hi, rfl⟩ := hxaA
    obtain ⟨j, hj, rfl⟩ := hxbB
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨i + j, by omega, ?_⟩
    simp only [Nat.cast_add]; ring
  · -- Reverse: range.image ⊆ A + B
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    let i := min k (A.card - 1)
    let j := k - i
    have hi : i < A.card := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hApos Nat.one_pos)
    have hj : j < B.card := by
      simp only [i, j]
      rcases le_or_gt k (A.card - 1) with h | h
      · simp [Nat.min_eq_left h]; exact Finset.card_pos.mp hBpos
      · have : min k (A.card - 1) = A.card - 1 := Nat.min_eq_right (by omega)
        simp [this]; omega
    have h_ij : i + j = k := Nat.add_sub_cancel' (Nat.min_le_left k _)
    simp only [Finset.mem_add]
    refine ⟨a + (i : ZMod p) * d, ?_, b + (j : ZMod p) * d, ?_, ?_⟩
    · rw [hA]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨i, hi, rfl⟩
    · rw [hB]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨j, hj, rfl⟩
    · have hk : (k : ZMod p) = (i : ZMod p) + j := by
        have h := congrArg (Nat.cast (R := ZMod p)) h_ij.symm
        rwa [Nat.cast_add] at h
      rw [hk]; ring

/-- Sum of two APs with same diff is an AP, given CD equality. -/
private lemma isAP_sum {A B : Finset (ZMod p)} {a b d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hB : IsArithmeticProgression B b d)
    (hApos : 0 < A.card) (hBpos : 0 < B.card)
    (hABcard : (A + B).card = A.card + B.card - 1) :
    IsArithmeticProgression (A + B) (a + b) d := by
  unfold IsArithmeticProgression
  rw [hABcard]
  exact add_isAP_eq hA hB hApos hBpos

/-- For AP(a,d) with d≠0 and |A|<p, the unique predecessor-free element is the start a. -/
private lemma isAP_sdiff_card {A : Finset (ZMod p)} {a d : ZMod p}
    (hA : IsArithmeticProgression A a d) (hd : d ≠ 0) (hApos : 0 < A.card)
    (hlt : A.card < p) :
    A \ A.image (· + d) = {a} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨hxA, hxnimg⟩
    rw [hA] at hxA
    simp only [Finset.mem_image, Finset.mem_range] at hxA
    obtain ⟨i, hi, rfl⟩ := hxA
    rcases Nat.eq_zero_or_pos i with rfl | hi_pos
    · simp
    · exfalso; apply hxnimg
      refine ⟨a + ((i - 1 : ℕ) : ZMod p) * d, ?_, ?_⟩
      · rw [hA]; simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨i - 1, by omega, rfl⟩
      · have hcast : ((i - 1 : ℕ) : ZMod p) + 1 = (i : ZMod p) := by
          have h := Nat.sub_add_cancel hi_pos
          have := congrArg (Nat.cast (R := ZMod p)) h
          rwa [Nat.cast_add, Nat.cast_one] at this
        calc a + ((i - 1 : ℕ) : ZMod p) * d + d
            = a + (((i - 1 : ℕ) : ZMod p) + 1) * d := by rw [add_mul]; ring
          _ = a + (i : ZMod p) * d := by rw [hcast]
  · intro hxa
    rw [hxa]
    refine ⟨?_, ?_⟩
    · rw [hA]; simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨0, hApos, by simp⟩
    · rintro ⟨y, hyA, hyd⟩
      rw [hA] at hyA
      simp only [Finset.mem_image, Finset.mem_range] at hyA
      obtain ⟨j, hj, rfl⟩ := hyA
      have h_eq : ((j : ZMod p) + 1) * d = 0 := by
        have h : a + ((j : ZMod p) + 1) * d = a + 0 := by
          simp only [add_zero, add_mul, one_mul, ← add_assoc]; exact hyd
        exact add_left_cancel h
      have hzero : (j : ZMod p) + 1 = 0 := by
        have hc : ((j : ZMod p) + 1) * d * d⁻¹ = 0 * d⁻¹ := by rw [h_eq]
        rwa [mul_assoc, mul_inv_cancel₀ hd, mul_one, zero_mul] at hc
      have h_dvd : p ∣ j + 1 := by
        have hcast : ((j + 1 : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, Nat.cast_one]; exact hzero
        rwa [ZMod.natCast_zmod_eq_zero_iff_dvd] at hcast
      exact absurd (Nat.le_of_dvd (by omega) h_dvd) (by omega)

/-- **AP Sdiff Card**: Given IH gives A' = A.erase a₀ and B are APs with same diff d,
    the set A has exactly 1 element with no d-predecessor in A. -/
private lemma vosper_ap_sdiff_card
    (A : Finset (ZMod p)) (a₀ a₁ b₀ d : ZMod p) (B : Finset (ZMod p))
    (ha₀A : a₀ ∈ A)
    (hA3 : 2 < A.card)
    (hB : 2 ≤ B.card)
    (hlt : A.card + B.card - 1 < p)
    (hAB : (A + B).card = A.card + B.card - 1)
    (hcase1 : ((A.erase a₀) + B).card = A.card + B.card - 2)
    (hAP_A' : IsArithmeticProgression (A.erase a₀) a₁ d)
    (hAP_B : IsArithmeticProgression B b₀ d) :
    (A \ A.image (· + d)).card = 1 := by
  have hA'card : (A.erase a₀).card = A.card - 1 := Finset.card_erase_of_mem ha₀A
  have hA'pos : 0 < (A.erase a₀).card := by omega
  have hBpos : 0 < B.card := by omega
  have hd : d ≠ 0 := d_ne_zero_of_isAP hAP_A' (by omega)
  have hA_lt_p : A.card < p := by omega
  -- A'+B is AP(a₁+b₀, d, |A|+|B|-2) via isAP_sum
  have hcase1' : ((A.erase a₀) + B).card = (A.erase a₀).card + B.card - 1 := by omega
  have hAP_A'B : IsArithmeticProgression ((A.erase a₀) + B) (a₁ + b₀) d :=
    isAP_sum hAP_A' hAP_B hA'pos hBpos hcase1'
  -- {a₀}+B is AP(a₀+b₀, d, |B|) via isAP_sum with singleton
  have hcard_a₀B : ({a₀} + B : Finset (ZMod p)).card = B.card :=
    Finset.card_singleton_add a₀ B
  have hcard_sing_eq : ({a₀} : Finset (ZMod p)).card + B.card - 1 = B.card := by simp
  have hAP_a₀B : IsArithmeticProgression ({a₀} + B : Finset (ZMod p)) (a₀ + b₀) d :=
    isAP_sum (isAP_singleton a₀ d) hAP_B (by simp) hBpos (by rw [hcard_a₀B]; simp)
  -- |{a₀}+B \ (A'+B)| = 1: follows from |A+B| = |A'+B| + 1
  have h_sdiff_one : ((({a₀} + B) \ ((A.erase a₀) + B)) : Finset (ZMod p)).card = 1 := by
    have hunion : A + B = (A.erase a₀ + B) ∪ ({a₀} + B) := by
      ext x
      simp only [Finset.mem_add, Finset.mem_union]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        by_cases h : a = a₀
        · right; rw [h]; exact ⟨a₀, Finset.mem_singleton_self a₀, b, hb, rfl⟩
        · left; exact ⟨a, Finset.mem_erase.mpr ⟨h, ha⟩, b, hb, rfl⟩
      · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
        · exact ⟨a, Finset.mem_of_mem_erase ha, b, hb, rfl⟩
        · simp only [Finset.mem_singleton] at ha
          exact ⟨a₀, ha₀A, b, hb, by rw [ha]⟩
    have hIE := Finset.card_union_add_card_inter (A.erase a₀ + B) ({a₀} + B)
    have hsd := Finset.card_inter_add_card_sdiff ({a₀} + B) (A.erase a₀ + B)
    rw [Finset.inter_comm] at hsd
    rw [← hunion, hAB, hcase1, hcard_a₀B] at hIE
    rw [hcard_a₀B] at hsd
    omega
  -- Position analysis: a₀ is a₁-d (predecessor) or a₁+|A'|*d (successor)
  have hpos : a₀ = a₁ - d ∨ a₀ = a₁ + ((A.erase a₀).card : ZMod p) * d := by
    -- Injectivity of k ↦ a₀+b₀+k*d on {0,...,|B|-1} (size < p)
    have hBlt : B.card < p := by omega
    have hinj_a₀B : Set.InjOn (fun k : ℕ => a₀ + b₀ + (k : ZMod p) * d)
        (Finset.range B.card : Set ℕ) := by
      intro k₁ hk₁ k₂ hk₂ heq
      simp only [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
      have hmul : (k₁ : ZMod p) * d = (k₂ : ZMod p) * d := add_left_cancel heq
      have h_eq : (k₁ : ZMod p) = (k₂ : ZMod p) := by
        have hc : (k₁ : ZMod p) * d * d⁻¹ = (k₂ : ZMod p) * d * d⁻¹ := by rw [hmul]
        rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc
      have hk₁p : k₁ < p := lt_trans hk₁ hBlt
      have hk₂p : k₂ < p := lt_trans hk₂ hBlt
      have := congrArg ZMod.val h_eq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hk₁p, Nat.mod_eq_of_lt hk₂p] at this
      omega
    -- Injectivity of j ↦ a₁+b₀+j*d on {0,...,|A'|+|B|-2}
    have hA'Blt : (A.erase a₀).card + B.card - 1 < p := by omega
    have hinj_A'B : Set.InjOn (fun j : ℕ => a₁ + b₀ + (j : ZMod p) * d)
        (Finset.range ((A.erase a₀).card + B.card - 1) : Set ℕ) := by
      intro j₁ hj₁ j₂ hj₂ heq
      simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
      have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d := add_left_cancel heq
      have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := by
        have hc : (j₁ : ZMod p) * d * d⁻¹ = (j₂ : ZMod p) * d * d⁻¹ := by rw [hmul]
        rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc
      have hj₁p : j₁ < p := lt_trans hj₁ hA'Blt
      have hj₂p : j₂ < p := lt_trans hj₂ hA'Blt
      have := congrArg ZMod.val h_eq
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁p, Nat.mod_eq_of_lt hj₂p] at this
      omega
    -- Extract the unique sdiff element
    obtain ⟨elem, helem_eq⟩ := Finset.card_eq_one.mp h_sdiff_one
    have helem_mem : elem ∈ (({a₀} + B) \ ((A.erase a₀) + B) : Finset (ZMod p)) := by
      rw [helem_eq]; exact Finset.mem_singleton_self elem
    have helem_a₀B : elem ∈ ({a₀} + B : Finset (ZMod p)) :=
      (Finset.mem_sdiff.mp helem_mem).1
    have helem_notA'B : elem ∉ (A.erase a₀) + B := (Finset.mem_sdiff.mp helem_mem).2
    -- elem = a₀+b₀+k₀*d for some k₀ < |B|
    rw [hAP_a₀B] at helem_a₀B
    simp only [Finset.mem_image, Finset.mem_range] at helem_a₀B
    obtain ⟨k₀, hk₀B, hk₀_eq⟩ := helem_a₀B
    -- All elements a₀+b₀+k*d for k ≠ k₀ are in A'+B (since sdiff = {elem})
    have hall_in : ∀ k < B.card, k ≠ k₀ → a₀ + b₀ + (k : ZMod p) * d ∈ (A.erase a₀) + B := by
      intro k hkB hkk₀
      have hmem_a₀B : a₀ + b₀ + (k : ZMod p) * d ∈ ({a₀} + B : Finset (ZMod p)) := by
        rw [hAP_a₀B]; simp only [Finset.mem_image, Finset.mem_range]; exact ⟨k, hkB, rfl⟩
      by_contra hnotA'B
      have hsd : a₀ + b₀ + (k : ZMod p) * d ∈ (({a₀} + B) \ ((A.erase a₀) + B) : Finset (ZMod p)) :=
        Finset.mem_sdiff.mpr ⟨hmem_a₀B, hnotA'B⟩
      rw [helem_eq] at hsd
      simp only [Finset.mem_singleton] at hsd
      exact hkk₀ (hinj_a₀B
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hkB))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr hk₀B))
        (by rw [hsd, hk₀_eq]))
    -- Helper: convert "in A'+B" to position j in range
    have hmem_to_pos : ∀ x, x ∈ (A.erase a₀) + B →
        ∃ j < (A.erase a₀).card + B.card - 1, x = a₁ + b₀ + (j : ZMod p) * d := by
      intro x hx
      rw [hAP_A'B] at hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      exact hx
    -- Case split: k₀ = 0 (predecessor case) or k₀ = |B|-1 (successor case)
    rcases Nat.eq_zero_or_pos k₀ with rfl | hk₀pos
    · -- k₀ = 0: elem = a₀+b₀, which is NOT in A'+B
      -- a₀+b₀+1*d IS in A'+B (since k=1 ≠ 0, |B|≥2)
      left
      have h1_in : a₀ + b₀ + (1 : ZMod p) * d ∈ (A.erase a₀) + B :=
        hall_in 1 (by omega) (by omega)
      obtain ⟨j₁, hj₁lt, hj₁_eq⟩ := hmem_to_pos _ h1_in
      -- hj₁_eq: a₀+b₀+d = a₁+b₀+j₁*d  → a₀+d = a₁+j₁*d
      -- Claim: j₁ = 0 (otherwise a₀+b₀ = a₁+b₀+(j₁-1)*d ∈ A'+B, contradicting helem_notA'B)
      have hj₁_zero : j₁ = 0 := by
        by_contra hj₁ne
        have hj₁_pos : 0 < j₁ := Nat.pos_of_ne_zero hj₁ne
        -- a₀+b₀ = a₁+b₀+(j₁-1)*d
        have hpred_eq : a₀ + b₀ = a₁ + b₀ + ((j₁ - 1 : ℕ) : ZMod p) * d := by
          have hcast : ((j₁ - 1 : ℕ) : ZMod p) + 1 = (j₁ : ZMod p) := by
            have h := Nat.sub_add_cancel hj₁_pos
            have := congrArg (Nat.cast (R := ZMod p)) h
            rwa [Nat.cast_add, Nat.cast_one] at this
          simp only [one_mul] at hj₁_eq
          linear_combination hj₁_eq - d * hcast
        -- a₀+b₀ ∈ A'+B (since j₁-1 < |A'|+|B|-1)
        have hpred_in : a₀ + b₀ ∈ (A.erase a₀) + B := by
          rw [hAP_A'B]; simp only [Finset.mem_image, Finset.mem_range]
          exact ⟨j₁ - 1, by omega, hpred_eq⟩
        -- But a₀+b₀ = elem (since k₀=0, hk₀_eq says elem = a₀+b₀+0*d = a₀+b₀)
        have helem_eq' : elem = a₀ + b₀ := by rw [hk₀_eq]; simp
        exact helem_notA'B (helem_eq' ▸ hpred_in)
      -- j₁ = 0: a₀+b₀+d = a₁+b₀ → a₀ = a₁-d
      rw [hj₁_zero] at hj₁_eq
      simp only [Nat.cast_zero, zero_mul, add_zero] at hj₁_eq
      -- hj₁_eq: a₀+b₀+1*d = a₁+b₀
      have h1d : (1 : ZMod p) * d = d := one_mul d
      rw [h1d] at hj₁_eq
      linear_combination hj₁_eq
    · -- k₀ > 0. Check if k₀ = |B|-1 or k₀ is in the middle.
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hk₀B) with rfl | hk₀mid
      · -- k₀ = |B|-1 (successor case)
        right
        -- elem = a₀+b₀+(|B|-1)*d ∉ A'+B
        -- All of a₀+b₀, ..., a₀+b₀+(|B|-2)*d ARE in A'+B
        -- In particular a₀+b₀+(|B|-2)*d ∈ A'+B (since |B|≥2, |B|-2 ≠ |B|-1)
        have hlast_in : a₀ + b₀ + ((B.card - 2 : ℕ) : ZMod p) * d ∈ (A.erase a₀) + B :=
          hall_in (B.card - 2) (by omega) (by omega)
        obtain ⟨jl, hjllt, hjl_eq⟩ := hmem_to_pos _ hlast_in
        -- Also a₀+b₀ ∈ A'+B (since k=0 ≠ k₀=|B|-1, |B|≥2)
        have hfirst_in : a₀ + b₀ + (0 : ZMod p) * d ∈ (A.erase a₀) + B :=
          hall_in 0 (by omega) (by omega)
        obtain ⟨jf, hjflt, hjf_eq⟩ := hmem_to_pos _ hfirst_in
        simp only [Nat.cast_zero, zero_mul, add_zero] at hjf_eq
        -- From hjf_eq: a₀+b₀ = a₁+b₀+jf*d → a₀ = a₁+jf*d
        -- a₀+b₀+(|B|-1)*d ∉ A'+B (this is elem)
        -- a₀+b₀+(|B|-1)*d = a₁+b₀+(jf+|B|-1)*d (from hjf_eq)
        -- (jf+|B|-1) ∉ {0,...,|A'|+|B|-2} means jf+|B|-1 ≥ |A'|+|B|-1 → jf ≥ |A'|
        -- Also jf ≤ |A'|+|B|-2 - (|B|-1) = |A'|-1 ... hmm that would force jf = |A'| contradicting jf ≤ |A'|-1
        -- Actually: we need to show the last element is outside AND use this to pin jf = |A'|
        -- elem = a₀+b₀+(|B|-1)*d ∉ A'+B
        have hlast_notA'B : a₀ + b₀ + ((B.card - 1 : ℕ) : ZMod p) * d ∉ (A.erase a₀) + B := by
          intro hmem
          obtain ⟨jx, hjxlt, hjx_eq⟩ := hmem_to_pos _ hmem
          -- a₀+b₀+(|B|-1)*d = a₁+b₀+jx*d
          -- But this element = elem (since k₀=|B|-1)
          have helem_eq' : a₀ + b₀ + ((B.card - 1 : ℕ) : ZMod p) * d = elem := by
            rw [← hk₀_eq]; congr 1; simp
          exact helem_notA'B (helem_eq' ▸ hmem)
        -- From hjf_eq: a₀+b₀ = a₁+b₀+jf*d
        -- The last element: a₀+b₀+(|B|-1)*d = a₁+b₀+(jf+|B|-1)*d
        -- But (jf+|B|-1) must be ≥ |A'|+|B|-1 (outside range)
        -- And jf ≤ |A'|+|B|-2-(|B|-1) = |A'|-1... hmm, contradiction unless I'm wrong about jf bound
        -- Actually: jf < |A'|+|B|-1 from hjflt
        -- jf+|B|-1: need this ≥ |A'|+|B|-1 (outside range means ≥ |A'|+|B|-1)
        -- And jf+|B|-1 ≥ |A'|+|B|-1 ↔ jf ≥ |A'|. So jf ≥ |A'|.
        -- Combined with jf < |A'|+|B|-1: jf ∈ {|A'|,...,|A'|+|B|-2}.
        -- But the only valid value: a₀+b₀+(|B|-2)*d = a₁+b₀+jl*d, and jl = jf+|B|-2.
        -- If jf = |A'|: jl = |A'|+|B|-2 ∈ {0,...,|A'|+|B|-2}. ✓
        -- If jf > |A'|: jl = jf+|B|-2 ≥ |A'|+|B|-1 which is outside range... but jl < |A'|+|B|-1. Contradiction!
        -- So jf = |A'|.
        have hjf_val : jf = (A.erase a₀).card := by
          -- From hjf_eq and hlast_notA'B:
          -- a₀+b₀+(|B|-1)*d = a₁+b₀+(jf+|B|-1:ZMod p)*d is outside A'+B
          -- meaning (jf+|B|-1:ℕ) ≥ |A'|+|B|-1 (in ℕ sense, since sizes < p)
          by_contra hjfne
          -- If jf < |A'|: then jf+|B|-1 < |A'|+|B|-1, so a₀+b₀+(|B|-1)*d ∈ A'+B. Contradiction.
          have hjflt' : jf < (A.erase a₀).card := Nat.lt_of_le_of_ne (by omega) hjfne
          apply hlast_notA'B
          rw [hAP_A'B]; simp only [Finset.mem_image, Finset.mem_range]
          refine ⟨jf + (B.card - 1), by omega, ?_⟩
          -- a₀+b₀+(|B|-1)*d = a₁+b₀+(jf+|B|-1)*d
          -- from hjf_eq: a₀+b₀ = a₁+b₀+jf*d
          have hcast : ((jf + (B.card - 1) : ℕ) : ZMod p) = (jf : ZMod p) + ((B.card - 1 : ℕ) : ZMod p) := by
            push_cast; ring
          rw [hcast, add_mul]
          -- a₁+b₀+jf*d+(|B|-1)*d = a₀+b₀+(|B|-1)*d (using hjf_eq)
          linear_combination hjf_eq
        -- jf = |A'|, so a₀ = a₁+|A'|*d
        rw [hjf_val] at hjf_eq
        simp only [Nat.cast_zero, zero_mul, add_zero] at hjf_eq
        -- hjf_eq: a₀+b₀ = a₁+b₀+|A'|*d → a₀ = a₁+|A'|*d
        linear_combination hjf_eq
      · -- k₀ is in the middle (0 < k₀ < |B|-1): derive contradiction
        exfalso
        -- Both first (k=0) and last (k=|B|-1) elements of {a₀}+B are in A'+B
        have hfirst_in : a₀ + b₀ + (0 : ZMod p) * d ∈ (A.erase a₀) + B :=
          hall_in 0 (by omega) (by omega)
        have hlast_in : a₀ + b₀ + ((B.card - 1 : ℕ) : ZMod p) * d ∈ (A.erase a₀) + B :=
          hall_in (B.card - 1) (by omega) (by omega)
        simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst_in
        obtain ⟨jf, hjflt, hjf_eq⟩ := hmem_to_pos _ hfirst_in
        obtain ⟨jl, hjllt, hjl_eq⟩ := hmem_to_pos _ hlast_in
        -- jl = jf + |B| - 1 (from injectivity and positions)
        -- Both jf and jl are < |A'|+|B|-1
        -- But also: the middle element a₀+b₀+k₀*d ∉ A'+B (it's the unique sdiff element)
        -- From positions: jf+k₀ must be outside {0,...,|A'|+|B|-2}
        -- From jf ≥ 0 and jf+|B|-1 = jl < |A'|+|B|-1: jf ≤ |A'|-1
        -- So jf+k₀ ≤ jf+|B|-2 < |A'|+|B|-1 (since jf ≤ |A'|-1 and k₀ ≤ |B|-2)
        -- contradiction: all positions jf,...,jf+|B|-1 are valid → a₀+b₀+k*d ∈ A'+B for ALL k
        -- including k=k₀ → contradiction with helem_notA'B
        have hk₀_in : a₀ + b₀ + (k₀ : ZMod p) * d ∈ (A.erase a₀) + B := by
          rw [hAP_A'B]; simp only [Finset.mem_image, Finset.mem_range]
          -- Need: jf + k₀ ∈ {0,...,|A'|+|B|-2}
          -- jl = jf + |B| - 1 (from the position of the last element)
          have hjl_eq2 : jl = jf + (B.card - 1) := by
            apply hinj_A'B
              (Finset.mem_coe.mpr (Finset.mem_range.mpr hjllt))
              (Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)))
            push_cast
            linear_combination -hjl_eq + hjf_eq
          refine ⟨jf + k₀, by omega, ?_⟩
          push_cast
          linear_combination hjf_eq
        exact helem_notA'B (by rwa [← hk₀_eq])
  -- In each case A is an AP with diff d, so |A \ A.image(·+d)| = 1 by isAP_sdiff_card
  rcases hpos with ha₀_pred | ha₀_succ
  · -- Case: a₀ = a₁ - d (predecessor of AP A'); A = AP(a₀, d, |A|)
    have hAP_A : IsArithmeticProgression A a₀ d := by
      have hA_card : A.card = (A.erase a₀).card + 1 := by omega
      unfold IsArithmeticProgression
      rw [hA_card, ← Finset.insert_erase ha₀A]
      ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | hx)
        · exact ⟨0, by omega, by simp⟩
        · rw [hAP_A'] at hx
          simp only [Finset.mem_image, Finset.mem_range] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          refine ⟨i + 1, by omega, ?_⟩
          have ha₁ : a₁ = a₀ + d := by rw [ha₀_pred]; ring
          have hcast3 : (↑(i + 1) : ZMod p) = (↑i : ZMod p) + 1 := by
            rw [Nat.cast_add, Nat.cast_one]
          rw [ha₁, hcast3]; ring
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi_pos
        · left; simp
        · right; rw [hAP_A']
          simp only [Finset.mem_image, Finset.mem_range]
          refine ⟨i - 1, by omega, ?_⟩
          have ha₁ : a₁ = a₀ + d := by rw [ha₀_pred]; ring
          have hcast : ((i - 1 : ℕ) : ZMod p) + 1 = (i : ZMod p) := by
            have h := Nat.sub_add_cancel hi_pos
            have := congrArg (Nat.cast (R := ZMod p)) h
            rwa [Nat.cast_add, Nat.cast_one] at this
          rw [ha₁]
          linear_combination d * hcast
    rw [isAP_sdiff_card hAP_A hd (by omega) hA_lt_p, Finset.card_singleton]
  · -- Case: a₀ = a₁ + |A'|*d (successor of AP A'); A = AP(a₁, d, |A|)
    have hAP_A : IsArithmeticProgression A a₁ d := by
      have hA_card : A.card = (A.erase a₀).card + 1 := by omega
      unfold IsArithmeticProgression
      rw [hA_card, ← Finset.insert_erase ha₀A]
      ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hmem
        rcases hmem with hxa | hx
        · rw [hxa]
          exact ⟨(A.erase a₀).card, by omega, ha₀_succ.symm⟩
        · rw [hAP_A'] at hx
          simp only [Finset.mem_image, Finset.mem_range] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          exact ⟨i, by omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi' | rfl
        · right; rw [hAP_A']
          simp only [Finset.mem_image, Finset.mem_range]
          exact ⟨i, hi', rfl⟩
        · left; exact ha₀_succ.symm
    rw [isAP_sdiff_card hAP_A hd (by omega) hA_lt_p, Finset.card_singleton]

/-! ### The Key "Near-Periodic" Lemma -/

/-- The map k ↦ x₀ + k * d : Fin p → ZMod p is injective when d ≠ 0 (ZMod p is a field) -/
private lemma zmod_orbit_injective {x₀ d : ZMod p} (hd : d ≠ 0) :
    Function.Injective (fun k : Fin p => x₀ + (k : ZMod p) * d) := by
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ heq
  simp only at heq
  have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d :=
    add_left_cancel heq
  have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := by
    have hc : (j₁ : ZMod p) * d * d⁻¹ = (j₂ : ZMod p) * d * d⁻¹ := by rw [hmul]
    rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc
  ext
  have hval := congrArg ZMod.val h_eq
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hval
  omega

/-- **Key Lemma**: |B \ B.image(·+d)| = 1 with d ≠ 0, |B| < p implies B is an AP. -/
lemma ap_of_near_periodic {B : Finset (ZMod p)} {d : ZMod p}
    (hd : d ≠ 0) (hlt : B.card < p)
    (h : (B \ (B.image (· + d))).card = 1) :
    ∃ b₀ : ZMod p, IsArithmeticProgression B b₀ d := by
  -- b₀: the unique element of B with no predecessor
  obtain ⟨b₀, hb₀_eq⟩ := Finset.card_eq_one.mp h
  have hb₀_sdiff : b₀ ∈ B \ B.image (· + d) := hb₀_eq ▸ Finset.mem_singleton_self b₀
  have hb₀_mem : b₀ ∈ B := (Finset.mem_sdiff.mp hb₀_sdiff).1
  have hb₀_noimg : b₀ ∉ B.image (· + d) := (Finset.mem_sdiff.mp hb₀_sdiff).2
  -- Every b ∈ B \ {b₀} has a predecessor: b - d ∈ B
  have hpred : ∀ b ∈ B, b ≠ b₀ → b - d ∈ B := by
    intro b hbB hne
    have hnotSD : b ∉ B \ B.image (· + d) := by rw [hb₀_eq]; simp [hne]
    rw [Finset.mem_sdiff, not_and_or, not_not] at hnotSD
    rcases hnotSD with hnotB | himg
    · exact absurd hbB hnotB
    · obtain ⟨c, hcB, hcd⟩ := Finset.mem_image.mp himg
      rwa [← eq_sub_of_add_eq hcd]
  -- Injectivity of j ↦ b₀ + j*d on {0,...,B.card-1}
  have hinjOn : Set.InjOn (fun j : ℕ => b₀ + (j : ZMod p) * d)
      (Finset.range B.card : Set ℕ) := by
    intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
    have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d := add_left_cancel heq
    have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := by
      have hc : (j₁ : ZMod p) * d * d⁻¹ = (j₂ : ZMod p) * d * d⁻¹ := by rw [hmul]
      rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc
    have := congrArg ZMod.val h_eq
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hj₁ hlt),
               Nat.mod_eq_of_lt (lt_trans hj₂ hlt)] at this
    omega
  -- Strong induction: b₀ + k*d ∈ B for all k < B.card
  -- Strategy: suffices h : ∀ n, ∀ k < n, k < B.card → b₀+k*d ∈ B
  have hmem : ∀ k : ℕ, k < B.card → b₀ + (k : ZMod p) * d ∈ B := by
    suffices hind : ∀ n : ℕ, ∀ k, k < n → k < B.card → b₀ + (k : ZMod p) * d ∈ B from
      fun k hk => hind (k + 1) k (Nat.lt_succ_self k) hk
    intro n
    induction n with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
      intro k hkm hkB
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hkm) with hkm' | rfl
      · exact ih k hkm' hkB
      -- k = m: b₀ + m*d ∈ B (proved by orbit-cardinality contradiction)
      · by_contra hnot
        -- T_m = {b₀, b₀+d, ..., b₀+(m-1)*d} ⊆ B
        let T : Finset (ZMod p) :=
          (Finset.range k).image (fun j => b₀ + (j : ZMod p) * d)
        have hT_sub : T ⊆ B := by
          intro x hx
          simp only [T, Finset.mem_image, Finset.mem_range] at hx
          obtain ⟨j, hj, rfl⟩ := hx
          exact ih j hj (lt_trans hj hkB)
        have hT_card : T.card = k := by
          rw [Finset.card_image_of_injOn]
          · exact Finset.card_range k
          · intro j₁ hj₁ j₂ hj₂ heq
            simp only [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂
            exact hinjOn (Finset.mem_coe.mpr (Finset.mem_range.mpr (lt_trans hj₁ hkB)))
                         (Finset.mem_coe.mpr (Finset.mem_range.mpr (lt_trans hj₂ hkB)))
                         heq
        -- S = B \ T is nonempty (|B| > m = |T|)
        have hS_pos : 0 < (B \ T).card := by
          rw [Finset.card_sdiff hT_sub, hT_card]; omega
        obtain ⟨x₀, hx₀_S⟩ := Finset.card_pos.mp hS_pos
        -- S is closed under b ↦ b - d
        have hσ : ∀ b ∈ B \ T, b - d ∈ B \ T := by
          intro b hb
          simp only [Finset.mem_sdiff] at hb ⊢
          obtain ⟨hbB, hbT⟩ := hb
          refine ⟨hpred b hbB ?_, ?_⟩
          · -- b ≠ b₀: since b₀ ∈ T ⊆ B and b ∉ T
            intro hbb₀
            apply hbT
            simp [T, hbb₀]
          · -- b - d ∉ T: if b-d = b₀+j*d for j < m, then b = b₀+(j+1)*d
            intro hbdT
            simp only [T, Finset.mem_image, Finset.mem_range] at hbdT
            obtain ⟨j, hjm, hjd⟩ := hbdT
            -- b = b-d + d = (b₀+j*d) + d = b₀+(j+1)*d
            have hb_eq : b = b₀ + ((j + 1 : ℕ) : ZMod p) * d := by
              have heq : b - d = b₀ + (j : ZMod p) * d := hjd.symm
              have : b = b - d + d := by ring
              rw [this, heq]; push_cast; ring
            rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hjm) with hj1 | hj1
            · -- j+1 < m: b ∈ T, contradiction
              exact hbT (by
                simp only [T, Finset.mem_image, Finset.mem_range]
                exact ⟨j + 1, hj1, hb_eq⟩)
            · -- j+1 = k: b = b₀+k*d, contradicts hnot (b₀+k*d ∉ B)
              apply hnot
              rw [← hj1]
              exact hb_eq ▸ hbB
        -- The orbit {x₀ - n*d : n < p} ⊆ S
        have horbit : ∀ n : ℕ, n < p → x₀ - (n : ZMod p) * d ∈ B \ T := by
          intro n hn
          induction n with
          | zero => simpa using hx₀_S
          | succ k ihk =>
            have hk : k < p := Nat.lt_of_succ_lt hn
            have hSk := ihk hk
            have heq : x₀ - ((k : ZMod p) + 1) * d = (x₀ - (k : ZMod p) * d) - d := by ring
            rw [show (↑(k + 1) : ZMod p) = (↑k : ZMod p) + 1 from by push_cast; ring]
            rw [heq]
            exact hσ _ hSk
        -- The orbit has p distinct elements (injective map)
        have horbit_inj : Function.Injective (fun n : Fin p => x₀ - (n : ZMod p) * d) := by
          intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ heq
          simp only at heq
          -- From x₀ - j₁*d = x₀ - j₂*d, derive j₁*d = j₂*d
          have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d := by
            linear_combination -heq
          have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := by
            have hc : (j₁ : ZMod p) * d * d⁻¹ = (j₂ : ZMod p) * d * d⁻¹ := by rw [hmul]
            rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc
          ext
          have := congrArg ZMod.val h_eq
          simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at this
          omega
        -- The orbit image has p elements, all in B \ T ⊆ B
        have himg_card : (Finset.univ.image (fun n : Fin p => x₀ - (n : ZMod p) * d)).card = p :=
          by rw [Finset.card_image_of_injective _ horbit_inj, Finset.card_fin]
        have himg_sub : Finset.univ.image (fun n : Fin p => x₀ - (n : ZMod p) * d) ⊆ B := by
          intro x hx
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
          exact (Finset.mem_sdiff.mp (horbit j.val j.isLt)).1
        -- p ≤ |B| < p: contradiction
        have hle := Finset.card_le_card himg_sub
        rw [himg_card] at hle
        omega
  -- Conclude B = (range B.card).image (j ↦ b₀ + j*d)
  refine ⟨b₀, ?_⟩
  unfold IsArithmeticProgression
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact hmem j hj
  · rw [Finset.card_image_of_injOn hinjOn, Finset.card_range]

/-! ### Vosper's Theorem -/

/-- **Vosper Base Case**: |A| = 2 forces B to be an AP when CD equality holds. -/
lemma vosper_base (A B : Finset (ZMod p)) (hA : A.card = 2) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1) (hlt : A.card + B.card - 1 < p) :
    ∃ (d a₀ b₀ : ZMod p),
      IsArithmeticProgression A a₀ d ∧ IsArithmeticProgression B b₀ d := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hA
  have hd : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hB_lt_p : B.card < p := by
    have : ({a, b} : Finset (ZMod p)).card = 2 := Finset.card_pair hab
    omega
  have hB_near_periodic : (B \ (B.image (· + (b - a)))).card = 1 := by
    have hunion : ({a, b} : Finset (ZMod p)) + B = {a} + B ∪ ({b} + B) := by
      rw [Finset.insert_eq, Finset.union_add]
    have hcardA : ({a} + B : Finset (ZMod p)).card = B.card := Finset.card_singleton_add a B
    have hcardBb : ({b} + B : Finset (ZMod p)).card = B.card := Finset.card_singleton_add b B
    have hAB_card : ({a, b} + B : Finset (ZMod p)).card = B.card + 1 := by
      have : ({a, b} : Finset (ZMod p)).card = 2 := Finset.card_pair hab; omega
    have hIE := Finset.card_union_add_card_inter ({a} + B) ({b} + B)
    have hint_card : (({a} + B) ∩ ({b} + B)).card = B.card - 1 := by
      have : (({a} + B) ∪ ({b} + B)).card = B.card + 1 := by rw [← hunion]; exact hAB_card
      omega
    have hinter_card_eq : (({a} + B) ∩ ({b} + B)).card = (B ∩ B.image (· + (b - a))).card := by
      have hset : ({a} + B) ∩ ({b} + B) = (B ∩ B.image (· + (b - a))).image (· + a) := by
        apply le_antisymm
        · intro x hx
          rw [Finset.mem_inter] at hx
          obtain ⟨hxA, hxBb⟩ := hx
          rw [Finset.mem_add] at hxA hxBb
          obtain ⟨y₁, hy₁, z₁, hz₁, h₁⟩ := hxA
          obtain ⟨y₂, hy₂, z₂, hz₂, h₂⟩ := hxBb
          rw [Finset.mem_singleton] at hy₁ hy₂; subst hy₁; subst hy₂
          rw [Finset.mem_image]
          refine ⟨z₁, ?_, by rw [add_comm]; exact h₁⟩
          rw [Finset.mem_inter, Finset.mem_image]
          exact ⟨hz₁, z₂, hz₂, by
            calc z₂ + (b - a) = b + z₂ - a := by ring
              _ = x - a := by rw [← h₂]; ring
              _ = a + z₁ - a := by rw [← h₁]; ring
              _ = z₁ := by ring⟩
        · intro x hx
          rw [Finset.mem_image] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          rw [Finset.mem_inter] at hz
          obtain ⟨hzB, hzimg⟩ := hz
          rw [Finset.mem_image] at hzimg
          obtain ⟨w, hwB, hwz⟩ := hzimg
          rw [Finset.mem_inter, Finset.mem_add, Finset.mem_add]
          refine ⟨?_, ?_⟩
          · exact ⟨a, Finset.mem_singleton_self a, z, hzB, by ring⟩
          · exact ⟨b, Finset.mem_singleton_self b, w, hwB, by
              calc b + w = w + (b - a) + a := by ring
                _ = z + a := by rw [hwz]⟩
      rw [hset]
      exact shift_card_eq (B ∩ B.image (· + (b - a))) a
    have hpart := Finset.card_inter_add_card_sdiff B (B.image (· + (b - a)))
    -- hpart : (B ∩ B.image ...).card + (B \ B.image ...).card = B.card
    -- hinter_card_eq : (({a}+B) ∩ ({b}+B)).card = (B ∩ B.image ...).card
    -- hint_card : (({a}+B) ∩ ({b}+B)).card = B.card - 1
    -- omega can chain these to get (B \ B.image ...).card = 1
    omega
  obtain ⟨b₀, hB_ap⟩ := ap_of_near_periodic hd hB_lt_p hB_near_periodic
  exact ⟨b - a, a, b₀, isAP_pair a b hab, hB_ap⟩

/-- **Vosper's Theorem** (1956): equality case of Cauchy-Davenport.
    Proof by strong induction on |A| (via recursive call + termination_by).

    Inductive step strategy:
    1. Find non-redundant a₀ ∈ A (Case 1): |(A\{a₀})+B| = |A|+|B|-2.
       Existence: if every a ∈ A were "redundant" (Case 2), the Cauchy-Davenport
       lower bound Σ |(A\{a})+B| ≥ |A|·(|A|+|B|-2) combined with the equality
       Σ |(A\{a})+B| = |A|·(|A+B|) gives |A|·|B| ≥ 2(|A|+|B|-1), which fails
       for |A|·|B| < 2(|A|+|B|-1) (e.g., |A|=3,|B|=2 gives 6 ≥ 8, contradiction).
    2. Apply IH (recursive): A' = A\{a₀} and B are APs with common diff d.
    3. Extend (AP extension sorry): a₀ is predecessor/successor of A' in the AP.
       Proof sketch: Both A'+B and {a₀}+B are APs with diff d. Since |A+B| = |A'+B|+1,
       exactly 1 element of {a₀}+B is outside A'+B, which must be an endpoint.
       This forces a₀ = a₁-d or a₀ = a₁+|A'|·d, making A an AP with diff d. -/
theorem vosper (A B : Finset (ZMod p)) (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (h : (A + B).card = A.card + B.card - 1) (hlt : A.card + B.card - 1 < p) :
    ∃ (d a₀ b₀ : ZMod p),
      IsArithmeticProgression A a₀ d ∧ IsArithmeticProgression B b₀ d := by
  rcases Nat.lt_or_eq_of_le hA with hA3 | hA2
  · -- |A| ≥ 3: inductive step
    -- Step 1: Find non-redundant a₀ ∈ A.
    -- For each a ∈ A: CD gives |(A.erase a)+B| ≥ |A|+|B|-2.
    --                 Inclusion gives |(A.erase a)+B| ≤ |A+B| = |A|+|B|-1.
    -- If ALL a are redundant (Case 2 for all), a counting argument fails. So ∃ Case 1.
    obtain ⟨a₀, ha₀A, hcase1⟩ : ∃ a₀ ∈ A, ((A.erase a₀) + B).card = A.card + B.card - 2 := by
      -- Proof by contradiction: assume all a ∈ A give Case 2 (|(A.erase a)+B| = |A|+|B|-1).
      -- Then |A|·|B| ≥ 2(|A|+|B|-1), which fails for small |A|,|B| and small p values.
      -- For the general case, the iterative removal argument gives the contradiction.
      sorry -- [SORRY 1/2] Case 1 existence: counting argument or iterative removal
    -- Step 2: Apply IH recursively to A' = A.erase a₀ and B.
    have hA'card : (A.erase a₀).card = A.card - 1 := Finset.card_erase_of_mem ha₀A
    have hA'2 : 2 ≤ (A.erase a₀).card := by omega
    -- Restate hcase1 using A'.card instead of A.card
    have hcase1' : ((A.erase a₀) + B).card = (A.erase a₀).card + B.card - 1 := by
      rw [hA'card]; omega
    have hcase1_lt_p : (A.erase a₀).card + B.card - 1 < p := by omega
    obtain ⟨d, a₁, b₀, hAP_A', hAP_B⟩ :=
      vosper (A.erase a₀) B hA'2 hB hcase1' hcase1_lt_p
    -- Step 3: Extend the AP from A' to A.
    -- We have: IsAP(A', a₁, d) and IsAP(B, b₀, d).
    -- Claim: A is also AP with diff d (a₀ is adjacent to A' in the AP order).
    -- Proof: A'+B is AP with diff d of length |A'|+|B|-1. {a₀}+B is AP with diff d.
    --        |{a₀}+B \ A'+B| = 1 forces the missing element to be an endpoint.
    --        Endpoint missing ↔ a₀ = a₁-d (predecessor) or a₀ = a₁+|A'|·d (successor).
    have hAP_A : ∃ start : ZMod p, IsArithmeticProgression A start d := by
      have hd : d ≠ 0 := d_ne_zero_of_isAP hAP_A' hA'2
      have hA_lt_p : A.card < p := by omega
      have hsdiff : (A \ A.image (· + d)).card = 1 :=
        vosper_ap_sdiff_card A a₀ a₁ b₀ d B ha₀A hA3 hB hlt h hcase1 hAP_A' hAP_B
      exact ap_of_near_periodic hd hA_lt_p hsdiff
    obtain ⟨start_A, hAP_A_start⟩ := hAP_A
    exact ⟨d, start_A, b₀, hAP_A_start, hAP_B⟩
  · -- |A| = 2: base case
    exact vosper_base A B hA2.symm hB h hlt
termination_by A.card
decreasing_by
  simp only [Finset.card_erase_of_mem ha₀A]; omega

end Erdos476OQ05
