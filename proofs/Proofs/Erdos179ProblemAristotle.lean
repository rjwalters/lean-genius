/-
  Aristotle targets for Erdős Problem #179: Arithmetic Progression Supersaturation
  Routine supporting lemmas for automated proof search.
  See Erdos179Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main deep results (Fox-Pohoata, Leng-Sah-Sawhney, Szemerédi)
  - Routine combinatorics about arithmetic progressions
  - Card computations for `arithmeticProgression`
  - Membership and containment lemmas
  - Supporting infrastructure for AP_free_has_2APs and F_2_well_defined
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos179Aristotle

open Finset Nat

/-
## Section 1: Arithmetic Progression Definitions (local copies)

Local definitions matching Erdos179Problem.lean.
-/

/-- An arithmetic progression of length k with first term a and common difference d. -/
def arithmeticProgression (a d : ℕ) (k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/-- A set contains a k-term AP. -/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d k ⊆ A

/-
## Section 2: Membership in Arithmetic Progressions
-/

/-- x is in arithmeticProgression a d k iff x = a + i*d for some i < k. -/
theorem mem_ap_iff (a d k x : ℕ) :
    x ∈ arithmeticProgression a d k ↔ ∃ i, i < k ∧ x = a + i * d := by
  unfold arithmeticProgression
  simp [Finset.mem_image, Finset.mem_range]

/-- The first element a is in arithmeticProgression a d k for k ≥ 1. -/
theorem ap_mem_first (a d k : ℕ) (hk : k ≥ 1) :
    a ∈ arithmeticProgression a d k := by
  rw [mem_ap_iff]
  exact ⟨0, by omega, by ring⟩

/-- The second element a + d is in arithmeticProgression a d k for k ≥ 2. -/
theorem ap_mem_second (a d k : ℕ) (hk : k ≥ 2) :
    a + d ∈ arithmeticProgression a d k := by
  rw [mem_ap_iff]
  exact ⟨1, by omega, by ring⟩

/-- The third element a + 2d is in arithmeticProgression a d k for k ≥ 3. -/
theorem ap_mem_third (a d k : ℕ) (hk : k ≥ 3) :
    a + 2 * d ∈ arithmeticProgression a d k := by
  rw [mem_ap_iff]
  exact ⟨2, by omega, by ring⟩

/-
## Section 3: Cardinality of Arithmetic Progressions
-/

/-- The map i ↦ a + i*d is injective when d > 0. -/
theorem ap_map_injective (a d : ℕ) (hd : 0 < d) :
    Function.Injective (fun i => a + i * d) := by
  intro i j h
  have : i * d = j * d := by omega
  exact Nat.eq_of_mul_eq_mul_right hd this

/-- An AP with positive common difference has exactly k elements. -/
theorem ap_card_of_pos (a d k : ℕ) (hd : 0 < d) :
    (arithmeticProgression a d k).card = k := by
  unfold arithmeticProgression
  rw [Finset.card_image_of_injective _ (ap_map_injective a d hd)]
  exact Finset.card_range k

/-- An AP with d = 0 is a singleton (if k ≥ 1). -/
theorem ap_card_zero_diff (a k : ℕ) (hk : k ≥ 1) :
    (arithmeticProgression a 0 k).card = 1 := by
  unfold arithmeticProgression
  have : Finset.image (fun i => a + i * 0) (Finset.range k) = {a} := by
    ext x
    simp [Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; simp
    · rintro rfl; exact ⟨0, hk, by simp⟩
  rw [this]
  simp

/-- AP of length 0 is empty. -/
theorem ap_empty (a d : ℕ) : arithmeticProgression a d 0 = ∅ := by
  unfold arithmeticProgression
  simp

/-- AP of length 1 is a singleton. -/
theorem ap_singleton (a d : ℕ) : arithmeticProgression a d 1 = {a} := by
  unfold arithmeticProgression
  simp [Finset.range_one]

/-
## Section 4: Specific AP Examples
-/

/-- {0, 1, 2} is an AP starting at 0 with difference 1. -/
example : arithmeticProgression 0 1 3 = {0, 1, 2} := by decide

/-- {1, 3, 5, 7} is an AP starting at 1 with difference 2. -/
example : arithmeticProgression 1 2 4 = {1, 3, 5, 7} := by decide

/-- {2, 5, 8} is an AP with difference 3. -/
example : arithmeticProgression 2 3 3 = {2, 5, 8} := by decide

/-- {0, 10, 20, 30} is an AP with difference 10. -/
example : arithmeticProgression 0 10 4 = {0, 10, 20, 30} := by decide

/-
## Section 5: Pair Formation Lemma
-/

/-- Any two distinct naturals form a 2-AP. -/
theorem pair_forms_ap (a b : ℕ) (hab : a < b) :
    arithmeticProgression a (b - a) 2 = {a, b} := by
  unfold arithmeticProgression
  ext x
  simp [Finset.mem_image, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · left; ring
    · right; omega
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by ring⟩
    · exact ⟨1, by norm_num, by omega⟩

/-- Any pair {a, b} with a < b satisfies ContainsAP {a,b} 2. -/
theorem pair_contains_2ap (a b : ℕ) (hab : a < b) :
    ContainsAP {a, b} 2 := by
  unfold ContainsAP
  refine ⟨a, b - a, by omega, ?_⟩
  rw [pair_forms_ap a b hab]

/-
## Section 6: AP Containment Properties
-/

/-- If A ⊆ B and A contains a k-AP, so does B. -/
theorem ContainsAP_mono {A B : Finset ℕ} (h : A ⊆ B) (k : ℕ) :
    ContainsAP A k → ContainsAP B k := by
  intro ⟨a, d, hd, hAP⟩
  exact ⟨a, d, hd, hAP.trans h⟩

/-- A set containing {0, 1, 2} as a subset contains a 3-AP. -/
theorem contains_012_has_3ap (A : Finset ℕ) (h : {0, 1, 2} ⊆ A) :
    ContainsAP A 3 := by
  exact ⟨0, 1, by norm_num, by
    have : arithmeticProgression 0 1 3 = {0, 1, 2} := by decide
    rw [this]; exact h⟩

/-- Consecutive integers starting at n form a k-AP with difference 1. -/
theorem consecutive_form_ap (n k : ℕ) :
    arithmeticProgression n 1 k = Finset.image (fun i => n + i) (Finset.range k) := by
  unfold arithmeticProgression
  congr 1
  ext i
  simp [mul_one]

/-- The set {n, n+1, ..., n+k-1} contains a k-AP. -/
theorem consecutive_contains_ap (n k : ℕ) (hk : k ≥ 1) :
    ContainsAP (Finset.image (fun i => n + i) (Finset.range k)) k := by
  refine ⟨n, 1, by norm_num, ?_⟩
  rw [← consecutive_form_ap]

end Erdos179Aristotle
