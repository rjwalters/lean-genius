/-
Erdős Problem #476, Open Question 5: Vosper's Theorem (1956)

Source: Follow-up to erdos-476 (Erdős-Heilbronn conjecture)
Status: PARTIAL — ap_of_near_periodic proved (orbit-cardinality argument);
                   vosper_base proved; vosper inductive step sorryed

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
          refine ⟨z₁, ?_, by linear_combination h₁⟩
          rw [Finset.mem_inter, Finset.mem_image]
          exact ⟨hz₁, z₂, hz₂, by linear_combination h₂ - h₁⟩
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
          · exact ⟨b, Finset.mem_singleton_self b, w, hwB, by linear_combination hwz⟩
      rw [hset]
      exact shift_card_eq (B ∩ B.image (· + (b - a))) a
    have hBinter : (B ∩ B.image (· + (b - a))).card = B.card - 1 :=
      hinter_card_eq.symm.trans hint_card
    have hpart : (B ∩ B.image (· + (b - a))).card + (B \ B.image (· + (b - a))).card = B.card :=
      Finset.card_inter_add_card_sdiff B _
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
      sorry -- [SORRY 2/2] AP extension: a₀ adjacent to A' → A is AP with diff d
    obtain ⟨start_A, hAP_A_start⟩ := hAP_A
    exact ⟨d, start_A, b₀, hAP_A_start, hAP_B⟩
  · -- |A| = 2: base case
    exact vosper_base A B hA2.symm hB h hlt
termination_by A.card
decreasing_by
  simp only [Finset.card_erase_of_mem ha₀A]; omega

end Erdos476OQ05
