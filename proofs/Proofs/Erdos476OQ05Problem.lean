/-
Erdős Problem #476, Open Question 5: Vosper's Theorem (1956)

Source: Follow-up to erdos-476 (Erdős-Heilbronn conjecture)
Status: PARTIAL — ap_of_near_periodic proved (orbit-cardinality argument);
                   vosper_base proved; vosper_ap_sdiff_card proved (hpos proved, Session 20);
                   isAP_sdiff_card proved; vosper_case1_exists sorryed [1 sorry remains];
                   counting argument proves |A|=|B|=3 sub-case; Kneser needed for |A|≥4 or |B|≥4

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
    have h_ij : i + j = k := Nat.min_add_sub_cancel' (by omega)
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
  · rintro rfl
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
      have hzero : (j : ZMod p) + 1 = 0 := (mul_eq_zero.mp h_eq).resolve_right hd
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
  have h_sdiff_one : ({a₀} + B \ ((A.erase a₀) + B) : Finset (ZMod p)).card = 1 := by
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
    -- Unfold AP definitions to use index-set representation
    unfold IsArithmeticProgression at hAP_a₀B hAP_A'B
    rw [hcard_a₀B] at hAP_a₀B
    -- Bounds needed for injectivity of nat-cast
    have hBlt : B.card < p := by omega
    have hn₂lt : (A.erase a₀).card + B.card - 1 < p := by rw [hA'card]; omega
    -- The AP₁ map i ↦ a₀+b₀+i*d is injective on range(B.card)
    have hAP₁_inj : ∀ i j : ℕ, i < B.card → j < B.card →
        a₀ + b₀ + (i : ZMod p) * d = a₀ + b₀ + (j : ZMod p) * d → i = j := by
      intro i j hi hj heq
      have h1 : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd (add_left_cancel heq)
      have h2 := congrArg ZMod.val h1
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_trans hi hBlt),
                 Nat.mod_eq_of_lt (Nat.lt_trans hj hBlt)] at h2
      omega
    -- The AP₂ map j ↦ a₁+b₀+j*d is injective on range(n₂)
    have hAP₂_inj : ∀ i j : ℕ, i < (A.erase a₀).card + B.card - 1 →
        j < (A.erase a₀).card + B.card - 1 →
        a₁ + b₀ + (i : ZMod p) * d = a₁ + b₀ + (j : ZMod p) * d → i = j := by
      intro i j hi hj heq
      have h1 : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd (add_left_cancel heq)
      have h2 := congrArg ZMod.val h1
      simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_trans hi hn₂lt),
                 Nat.mod_eq_of_lt (Nat.lt_trans hj hn₂lt)] at h2
      omega
    -- Extract the unique missing element y
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h_sdiff_one
    have hy_AP₁ : y ∈ ({a₀} + B : Finset _) :=
      Finset.mem_of_mem_sdiff (hy ▸ Finset.mem_singleton_self y)
    have hy_notAP₂ : y ∉ (A.erase a₀) + B :=
      (Finset.mem_sdiff.mp (hy ▸ Finset.mem_singleton_self y)).2
    -- All other elements of AP₁ are in AP₂
    have hothers : ∀ z ∈ ({a₀} + B : Finset _), z ≠ y → z ∈ (A.erase a₀) + B := by
      intro z hz hne
      by_contra hznot
      exact hne (Finset.mem_singleton.mp (hy ▸ Finset.mem_sdiff.mpr ⟨hz, hznot⟩))
    -- y = a₀+b₀+m*d for some m < B.card
    rw [hAP_a₀B] at hy_AP₁
    obtain ⟨m, hm_range, hm_eq⟩ := Finset.mem_image.mp hy_AP₁
    rw [Finset.mem_range] at hm_range
    -- Helper: AP₂ membership gives explicit index
    have inAP₂ : ∀ z ∈ (A.erase a₀) + B, ∃ j < (A.erase a₀).card + B.card - 1,
        z = a₁ + b₀ + (j : ZMod p) * d := by
      intro z hz
      rw [hAP_A'B] at hz
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hz
      exact ⟨j, Finset.mem_range.mp hj, hje.symm⟩
    -- Helper: y ∉ AP₂ means a₁+b₀+j*d ≠ a₀+b₀+m*d for all j < n₂
    have hy_notAP₂_idx : ∀ j < (A.erase a₀).card + B.card - 1,
        a₁ + b₀ + (j : ZMod p) * d ≠ y := by
      intro j hj heq
      exact hy_notAP₂ (by rw [hAP_A'B]; exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, heq.symm⟩)
    -- Case split: m = 0, m = B.card-1, or interior
    rcases Nat.lt_or_eq_of_le (Nat.zero_le m) with hm_pos | rfl
    · -- m ≥ 1 case
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hm_range) with hm_int | rfl
      · -- 0 < m < B.card-1: INTERIOR CASE → contradiction
        -- (proof: both (m-1) and (m+1) are non-missing indices, giving j=n₂-1 and k=0,
        --  then linear combination yields (|A'|+|B|)*d = 0, contradicting n₂+1 < p and d≠0)
        exfalso
        -- index m-1 not missing → a₀+b₀+(m-1)*d ∈ AP₂ at some j with j = n₂-1
        have hpred_ne : a₀ + b₀ + ((m - 1 : ℕ) : ZMod p) * d ≠ y := by
          intro heq
          exact absurd (hAP₁_inj _ _ (by omega) hm_range heq.symm) (by omega)
        have hpred_AP₁ : a₀ + b₀ + ((m - 1 : ℕ) : ZMod p) * d ∈ ({a₀} + B : Finset _) := by
          rw [hAP_a₀B]; exact Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), rfl⟩
        obtain ⟨j, hj_lt, hj_eq⟩ := inAP₂ _ (hothers _ hpred_AP₁ hpred_ne)
        -- j must be n₂-1 (otherwise a₀+b₀+m*d would be in AP₂ via index j+1)
        have hj_max : j = (A.erase a₀).card + B.card - 2 := by
          by_contra hj_ne
          have hj_lt' : j + 1 < (A.erase a₀).card + B.card - 1 := by omega
          have hym_eq : a₁ + b₀ + ((j + 1 : ℕ) : ZMod p) * d = y := by
            rw [← hm_eq]
            have hcast : ((j + 1 : ℕ) : ZMod p) = (j : ZMod p) + 1 := by push_cast; ring
            have hm_cast : (m : ZMod p) = ((m - 1 : ℕ) : ZMod p) + 1 := by
              push_cast [Nat.sub_add_cancel hm_pos]; ring
            linear_combination hj_eq + hm_cast * d - hcast * d
          exact hy_notAP₂_idx _ hj_lt' hym_eq
        -- index m+1 not missing → a₀+b₀+(m+1)*d ∈ AP₂ at some k with k = 0
        have hsucc_ne : a₀ + b₀ + ((m + 1 : ℕ) : ZMod p) * d ≠ y := by
          intro heq
          exact absurd (hAP₁_inj _ _ (by omega) hm_range heq.symm) (by omega)
        have hsucc_AP₁ : a₀ + b₀ + ((m + 1 : ℕ) : ZMod p) * d ∈ ({a₀} + B : Finset _) := by
          rw [hAP_a₀B]; exact Finset.mem_image.mpr ⟨m + 1, Finset.mem_range.mpr (by omega), by push_cast; ring⟩
        obtain ⟨k, hk_lt, hk_eq⟩ := inAP₂ _ (hothers _ hsucc_AP₁ hsucc_ne)
        -- k must be 0 (otherwise a₀+b₀+m*d would be in AP₂ via index k-1)
        have hk_zero : k = 0 := by
          by_contra hk_ne
          have hym_eq2 : a₁ + b₀ + ((k - 1 : ℕ) : ZMod p) * d = y := by
            rw [← hm_eq]
            have hcast : ((k - 1 : ℕ) : ZMod p) = (k : ZMod p) - 1 := by
              push_cast [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk_ne)]; ring
            have hm_cast : (m : ZMod p) = ((m + 1 : ℕ) : ZMod p) - 1 := by push_cast; ring
            linear_combination hk_eq + hm_cast * d - hcast * d
          exact hy_notAP₂_idx _ (by omega) hym_eq2
        -- From j = n₂-1 and k = 0: derive (|A'|+|B|)*d = 0
        rw [hj_max] at hj_eq; rw [hk_zero] at hk_eq
        -- hj_eq : a₁+b₀+((n₂-1):ZMod p)*d = a₀+b₀+((m-1):ℕ)*d
        -- hk_eq : a₁+b₀+(0:ZMod p)*d = a₀+b₀+((m+1):ℕ)*d
        have hderiv : ((A.erase a₀).card + B.card : ZMod p) * d = 0 := by
          have hcast_n₂ : ((A.erase a₀).card + B.card - 2 : ℕ) + 2 = (A.erase a₀).card + B.card := by
            rw [hA'card]; omega
          have : ((A.erase a₀).card + B.card - 2 + 2 : ℕ) = (A.erase a₀).card + B.card := hcast_n₂
          have hcast_sum : ((A.erase a₀).card + B.card : ZMod p) =
              ((A.erase a₀).card + B.card - 2 : ℕ) + (2 : ZMod p) := by
            push_cast [← hcast_n₂]; ring
          rw [hcast_sum]
          linear_combination hj_eq - hk_eq
        -- (|A'|+|B|)*d = 0 with d≠0 implies p ∣ (|A'|+|B|), but |A'|+|B| < p
        have hlt' : (A.erase a₀).card + B.card < p := by rw [hA'card]; omega
        have hne : ((A.erase a₀).card + B.card : ZMod p) ≠ 0 := by
          rw [ZMod.natCast_zmod_eq_zero_iff_dvd]
          intro hdvd
          have := Nat.le_of_dvd (by omega) hdvd
          omega
        exact hne (mul_right_cancel₀ hd (by rw [hderiv, zero_mul]))
      · -- m = B.card-1: LAST ELEMENT missing → a₀ = a₁+|A'|*d
        right
        -- index m-1 = B.card-2 not missing (since m = B.card-1 and B.card ≥ 2)
        have hpred_ne : a₀ + b₀ + ((B.card - 2 : ℕ) : ZMod p) * d ≠ y := by
          intro heq
          exact absurd (hAP₁_inj _ _ (by omega) hm_range heq.symm) (by omega)
        have hpred_AP₁ : a₀ + b₀ + ((B.card - 2 : ℕ) : ZMod p) * d ∈ ({a₀} + B : Finset _) := by
          rw [hAP_a₀B]
          exact Finset.mem_image.mpr ⟨B.card - 2, Finset.mem_range.mpr (by omega), rfl⟩
        obtain ⟨j, hj_lt, hj_eq⟩ := inAP₂ _ (hothers _ hpred_AP₁ hpred_ne)
        -- j = n₂-1 (otherwise a₀+b₀+(B.card-1)*d = y would be in AP₂ via index j+1)
        have hj_max : j = (A.erase a₀).card + B.card - 2 := by
          by_contra hj_ne
          have hj_lt' : j + 1 < (A.erase a₀).card + B.card - 1 := by omega
          have hym_eq : a₁ + b₀ + ((j + 1 : ℕ) : ZMod p) * d = y := by
            rw [← hm_eq]
            have hcast_j : ((j + 1 : ℕ) : ZMod p) = (j : ZMod p) + 1 := by push_cast; ring
            have hcast_m : (B.card - 1 : ZMod p) = ((B.card - 2 : ℕ) : ZMod p) + 1 := by
              push_cast [Nat.sub_add_cancel (by omega : 2 ≤ B.card)]; ring
            linear_combination hj_eq + hcast_m * d - hcast_j * d
          exact hy_notAP₂_idx _ hj_lt' hym_eq
        -- From hj_eq with j = n₂-1: a₀+b₀+(B.card-2)*d = a₁+b₀+(|A'|+|B|-2)*d
        rw [hj_max] at hj_eq
        -- Conclusion: a₀ = a₁+|A'|*d
        have hcast_n : (A.erase a₀).card + B.card - 2 = (A.erase a₀).card + (B.card - 2) := by omega
        linear_combination hj_eq
    · -- m = 0: FIRST ELEMENT missing → a₀ = a₁-d
      left
      -- index 1 is not missing (B.card ≥ 2)
      have h1_ne : a₀ + b₀ + (1 : ZMod p) * d ≠ y := by
        rw [← hm_eq]
        simp only [Nat.cast_zero, zero_mul, add_zero, one_mul]
        intro h; exact hd (add_left_cancel h)
      have h1_AP₁ : a₀ + b₀ + (1 : ZMod p) * d ∈ ({a₀} + B : Finset _) := by
        rw [hAP_a₀B]
        exact Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega), by push_cast; ring⟩
      obtain ⟨j, hj_lt, hj_eq⟩ := inAP₂ _ (hothers _ h1_AP₁ h1_ne)
      rcases Nat.eq_zero_or_pos j with rfl | hj_pos
      · -- j = 0: a₁+b₀ = a₀+b₀+d → a₀ = a₁-d
        simp only [Nat.cast_zero, zero_mul, add_zero] at hj_eq
        linear_combination -hj_eq
      · -- j ≥ 1: a₁+b₀+(j-1)*d = a₀+b₀ ∈ AP₂, contradicting a₀+b₀ ∉ AP₂
        exfalso
        -- a₀+b₀ = y (since m = 0, y = a₀+b₀+0*d = a₀+b₀)
        have hy_val : y = a₀ + b₀ := by rw [← hm_eq]; simp
        -- a₁+b₀+(j-1)*d = a₀+b₀ = y
        have hpred_eq_y : a₁ + b₀ + ((j - 1 : ℕ) : ZMod p) * d = y := by
          rw [hy_val]
          have hcast_j : ((j - 1 : ℕ) : ZMod p) = (j : ZMod p) - 1 := by
            push_cast [Nat.sub_add_cancel hj_pos]; ring
          linear_combination hj_eq - hcast_j * d
        exact hy_notAP₂_idx _ (by omega) hpred_eq_y
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
          calc a₀ + (↑i : ZMod p) * d
              = a₀ + ((↑(i - 1 : ℕ) : ZMod p) + 1) * d := by rw [hcast]
            _ = a₀ + d + (↑(i - 1 : ℕ) : ZMod p) * d := by ring
    rw [isAP_sdiff_card hAP_A hd (by omega) hA_lt_p, Finset.card_singleton]
  · -- Case: a₀ = a₁ + |A'|*d (successor of AP A'); A = AP(a₁, d, |A|)
    have hAP_A : IsArithmeticProgression A a₁ d := by
      have hA_card : A.card = (A.erase a₀).card + 1 := by omega
      unfold IsArithmeticProgression
      rw [hA_card, ← Finset.insert_erase ha₀A]
      ext x
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro (rfl | hx)
        · exact ⟨(A.erase a₀).card, by omega, by rw [← ha₀_succ]⟩
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
  have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := mul_right_cancel₀ hd hmul
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
    have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := mul_right_cancel₀ hd hmul
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
          have h_neg : -(j₁ : ZMod p) * d = -(j₂ : ZMod p) * d :=
            add_left_cancel (show x₀ + -(j₁ : ZMod p) * d = x₀ + -(j₂ : ZMod p) * d by
              rwa [← sub_eq_add_neg, ← sub_eq_add_neg])
          have hmul : (j₁ : ZMod p) * d = (j₂ : ZMod p) * d := by
            rwa [neg_mul, neg_mul, neg_inj] at h_neg
          have h_eq : (j₁ : ZMod p) = (j₂ : ZMod p) := mul_right_cancel₀ hd hmul
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
        linarith [Finset.card_le_card himg_sub, himg_card]
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
      by_contra hall
      push_neg at hall
      -- Every a ∈ A is redundant: cardinality is pinched between CD lower bound and inclusion upper bound
      have hredA_card : ∀ a ∈ A, (A.erase a + B).card = A.card + B.card - 1 := by
        intro a haA
        have hlo : A.card + B.card - 2 ≤ (A.erase a + B).card := by
          have hCD : p ⊓ ((A.erase a).card + B.card - 1) ≤ (A.erase a + B).card :=
            ZMod.cauchy_davenport hp.1
              (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem haA]; omega))
              (Finset.card_pos.mp (by omega))
          simp only [Finset.card_erase_of_mem haA, Nat.inf_eq_min] at hCD
          omega
        have hhi : (A.erase a + B).card ≤ A.card + B.card - 1 :=
          (Finset.card_le_card (Finset.add_subset_add_right (Finset.erase_subset _ _))).trans_eq h
        have hne := hall a haA
        omega
      -- Cardinality equality + inclusion → set equality
      have hredA : ∀ a ∈ A, A.erase a + B = A + B := fun a haA =>
        Finset.eq_of_subset_of_card_le
          (Finset.add_subset_add_right (Finset.erase_subset _ _))
          (h.trans (hredA_card a haA).symm).le
      -- Case split on |B|
      by_cases hB2 : B.card = 2
      · -- |B| = 2: orbit argument — A closed under +d forces |A| ≥ p, contradicting |A| < p
        have hA_lt_p : A.card < p := by omega
        obtain ⟨b₁, b₂, hne_b, hB_eq⟩ := Finset.card_eq_two.mp hB2
        have hb₁B : b₁ ∈ B := by rw [hB_eq]; exact Finset.mem_insert_self b₁ _
        have hd : b₁ - b₂ ≠ 0 := sub_ne_zero.mpr hne_b
        -- A is closed under translation by d = b₁ - b₂
        have hclosed : ∀ a ∈ A, a + (b₁ - b₂) ∈ A := by
          intro a haA
          have hmem : a + b₁ ∈ A.erase a + B := by
            rw [hredA a haA]; exact Finset.mem_add.mpr ⟨a, haA, b₁, hb₁B, rfl⟩
          obtain ⟨a', ha'er, b', hb'B, heq⟩ := Finset.mem_add.mp hmem
          rw [Finset.mem_erase] at ha'er
          rw [hB_eq, Finset.mem_insert, Finset.mem_singleton] at hb'B
          rcases hb'B with rfl | rfl
          · exact absurd (add_right_cancel heq) ha'er.1
          · have ha'_val : a' = a + (b₁ - b₂) := by linear_combination heq
            rw [← ha'_val]; exact ha'er.2
        -- The d-orbit of any a₀ ∈ A has p distinct elements all in A → |A| ≥ p
        obtain ⟨a₀, ha₀A⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
        have horbit_nat : ∀ k : ℕ, a₀ + (k : ZMod p) * (b₁ - b₂) ∈ A := by
          intro k
          induction k with
          | zero => simpa using ha₀A
          | succ n ih =>
            have := hclosed _ ih
            convert this using 1
            push_cast; ring
        have horbit : ∀ k : Fin p, a₀ + (k : ZMod p) * (b₁ - b₂) ∈ A :=
          fun k => horbit_nat k.val
        have himg_card : (Finset.univ.image (fun k : Fin p =>
            a₀ + (k : ZMod p) * (b₁ - b₂))).card = p := by
          rw [Finset.card_image_of_injective _ (zmod_orbit_injective hd),
              Finset.card_univ, Fintype.card_fin]
        have himg_sub : (Finset.univ.image (fun k : Fin p =>
            a₀ + (k : ZMod p) * (b₁ - b₂))) ⊆ A :=
          fun _ hx => by obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx; exact horbit j
        linarith [Finset.card_le_card himg_sub]
      · -- |B| ≥ 3: counting argument handles |A|=|B|=3; general case needs Kneser
        have hB3 : 3 ≤ B.card := by omega
        -- If all of A is redundant, every x ∈ A+B has ≥ 2 A-representations.
        -- Proof: if r(x) = 1 with unique a₁, then x ∉ (A.erase a₁)+B, contradicting hredA a₁.
        have hrep2 : ∀ x ∈ A + B, 2 ≤ (A.filter (fun a => x - a ∈ B)).card := by
          intro x hx
          by_contra hlt2
          push_neg at hlt2
          have hpos : 0 < (A.filter (fun a => x - a ∈ B)).card := by
            obtain ⟨a, haA, b, hbB, hxab⟩ := Finset.mem_add.mp hx
            apply Finset.card_pos.mpr
            exact ⟨a, Finset.mem_filter.mpr ⟨haA, show x - a ∈ B by
              have : x - a = b := (eq_sub_of_add_eq hxab).symm
              rw [this]; exact hbB⟩⟩
          have hcard1 : (A.filter (fun a => x - a ∈ B)).card = 1 := by omega
          obtain ⟨a₁, ha₁⟩ := Finset.card_eq_one.mp hcard1
          have ha₁A : a₁ ∈ A :=
            (Finset.mem_filter.mp (ha₁ ▸ Finset.mem_singleton_self a₁)).1
          have hxnotin : x ∉ A.erase a₁ + B := by
            intro hcontra
            obtain ⟨a', ha'er, b', hb'B, hsum'⟩ := Finset.mem_add.mp hcontra
            rw [Finset.mem_erase] at ha'er
            have ha'filt : a' ∈ A.filter (fun a => x - a ∈ B) :=
              Finset.mem_filter.mpr ⟨ha'er.2, (eq_sub_of_add_eq hsum') ▸ hb'B⟩
            rw [ha₁] at ha'filt
            exact ha'er.1 (Finset.mem_singleton.mp ha'filt)
          exact hxnotin (hredA a₁ ha₁A ▸ hx)
        -- Double counting: ∑_{x ∈ A+B} r(x) = |A| · |B|
        -- Because the map (x, a) ↦ (a, x-a) bijects the sigma with A×B.
        have hsum_eq : ∑ x ∈ A + B, (A.filter (fun a => x - a ∈ B)).card = A.card * B.card := by
          rw [← Finset.card_sigma, ← Finset.card_product]
          apply Finset.card_bij (fun xa _ => (xa.2, xa.1 - xa.2))
          · intro ⟨x, a⟩ hmem
            simp only [Finset.mem_sigma, Finset.mem_filter] at hmem
            exact Finset.mem_product.mpr ⟨hmem.2.1, hmem.2.2⟩
          · intro ⟨x₁, a₁⟩ _ ⟨x₂, a₂⟩ _ heq
            simp only [Prod.mk.injEq] at heq
            obtain ⟨ha, hd⟩ := heq
            obtain rfl := ha  -- unify a₁ = a₂
            -- hd : x₁ - a₁ = x₂ - a₁; need ⟨x₁, a₁⟩ = ⟨x₂, a₁⟩
            have h1 : x₁ = x₂ := by
              have := congr_arg (· + a₁) hd
              simp only [sub_add_cancel] at this
              exact this
            simp [h1]
          · intro (a, b) hmem
            rw [Finset.mem_product] at hmem
            obtain ⟨haA, hbB⟩ := hmem
            exact ⟨⟨a + b, a⟩,
              Finset.mem_sigma.mpr ⟨Finset.mem_add.mpr ⟨a, haA, b, hbB, rfl⟩,
                Finset.mem_filter.mpr ⟨haA, show a + b - a ∈ B by
                  convert hbB using 1; ring⟩⟩,
              Prod.ext rfl (show a + b - a = b by ring)⟩
        -- From hrep2: ∑_x r(x) ≥ 2 · |A+B| = 2 · (|A| + |B| - 1)
        have hlb : 2 * (A + B).card ≤ ∑ x ∈ A + B, (A.filter (fun a => x - a ∈ B)).card :=
          calc 2 * (A + B).card = ∑ _ ∈ A + B, 2 := by simp [Finset.sum_const, mul_comm]
            _ ≤ _ := Finset.sum_le_sum hrep2
        -- Combining: |A| · |B| ≥ 2 · (|A| + |B| - 1), i.e., (|A|-2)(|B|-2) ≥ 2
        have hineq : 2 * (A.card + B.card - 1) ≤ A.card * B.card := by
          have := hsum_eq ▸ h ▸ hlb; omega
        -- For |A|=3, |B|=3: 2*(3+3-1)=10 ≤ 3*3=9 is false → contradiction
        by_cases hAB3 : A.card = 3 ∧ B.card = 3
        · obtain ⟨hA3eq, hB3eq⟩ := hAB3
          rw [hA3eq, hB3eq] at hineq; norm_num at hineq
        · -- |A| ≥ 4 or |B| ≥ 4: (|A|-2)(|B|-2) ≥ 2 holds, but Kneser's theorem is needed
          -- to derive that A and B must be APs (not available in Mathlib)
          sorry -- [HARD] Requires Kneser's theorem (not in Mathlib) for |A|≥4 or |B|≥4
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
