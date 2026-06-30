/-
  Erdős Problem #179: Elementary Arithmetic-Progression Combinatorics
  Companion to Erdos179Problem.lean (incomplete-01)

  The parent file Erdos179Problem.lean states the deep Fox–Pohoata /
  Leng–Sah–Sawhney supersaturation results (F_k(N,ℓ) = N^{2-o(1)}) and
  leaves several `sorry`s, including the elementary combinatorial facts
  about counting arithmetic progressions. Those deep analytic theorems
  are far beyond elementary formalization, but the *combinatorial
  scaffolding* around them is fully provable. This self-contained file
  proves that scaffolding with 0 axioms / 0 sorries.

  Main results:
    • `arithmeticProgression_card`  : a k-term AP with positive common
        difference has exactly k elements (injectivity of i ↦ a + i·d).
    • `arithmeticProgression_subset`: k-APs sit inside ℓ-APs for k ≤ ℓ.
    • `ContainsAP_of_le`           : an ℓ-AP forces a k-AP for k ≤ ℓ
        (the trivial "supersaturation is monotone" direction).
    • `countAPs_le_choose`         : a set of size N has at most C(N,k)
        many k-APs — the trivial upper bound underlying F_k(N,ℓ) ≤ N².
    • `countAPs_two`               : a set of size N has *exactly* C(N,2)
        two-term APs. This proves the parent's `AP_free_has_2APs` and
        `F_2_well_defined` sorries — and shows the 3-AP-free hypothesis
        in the parent's statement is REDUNDANT: the identity holds for
        every finite set.

  Reference: https://erdosproblems.com/179
-/

import Mathlib

namespace Erdos179Combinatorics

open Finset
open scoped Classical

/- ## Part I: Arithmetic Progressions (matching the parent's definitions) -/

/-- An arithmetic progression of length k with first term a and common difference d. -/
def arithmeticProgression (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A set contains a k-term AP if some AP of length k (with d > 0) is a subset. -/
def ContainsAP (A : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ arithmeticProgression a d k ⊆ A

/-- The number of k-term APs contained in A. -/
noncomputable def countAPs (A : Finset ℕ) (k : ℕ) : ℕ :=
  (A.powerset.filter fun S => ∃ a d, d > 0 ∧ S = arithmeticProgression a d k).card

/- ## Part II: Structure of a single AP -/

/-- A 2-term AP is the pair of its two terms: `{a, a + d}`. -/
theorem arithmeticProgression_two (a d : ℕ) :
    arithmeticProgression a d 2 = {a, a + d} := by
  ext x
  simp only [arithmeticProgression, Finset.mem_image, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · left; ring
    · right; ring
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by ring⟩
    · exact ⟨1, by norm_num, by ring⟩

/-- **Cardinality of an AP.** A k-term AP with positive common difference has
    exactly k elements, because i ↦ a + i·d is injective when d > 0. -/
theorem arithmeticProgression_card (a d k : ℕ) (hd : 0 < d) :
    (arithmeticProgression a d k).card = k := by
  have hinj : Set.InjOn (fun i => a + i * d) ↑(Finset.range k) := by
    intro i _ j _ hij
    dsimp only at hij
    have h : i * d = j * d := by omega
    exact Nat.eq_of_mul_eq_mul_right hd h
  unfold arithmeticProgression
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- A shorter AP is contained in a longer one with the same start and step. -/
theorem arithmeticProgression_subset (a d : ℕ) {k k' : ℕ} (h : k ≤ k') :
    arithmeticProgression a d k ⊆ arithmeticProgression a d k' := by
  unfold arithmeticProgression
  apply Finset.image_subset_image
  intro x hx
  rw [Finset.mem_range] at hx ⊢
  omega

/- ## Part III: Supersaturation is monotone (the trivial direction) -/

/-- If a set contains an ℓ-AP, it contains a k-AP for every k ≤ ℓ. -/
theorem ContainsAP_of_le {A : Finset ℕ} {k ℓ : ℕ} (h : k ≤ ℓ) (hA : ContainsAP A ℓ) :
    ContainsAP A k := by
  obtain ⟨a, d, hd, hsub⟩ := hA
  exact ⟨a, d, hd, (arithmeticProgression_subset a d h).trans hsub⟩

/-- A set of size ≥ 2 contains a 2-AP (any two distinct elements form one). -/
theorem ContainsAP_two_of_two_le_card (A : Finset ℕ) (h : 2 ≤ A.card) :
    ContainsAP A 2 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨x, y - x, by omega, ?_⟩
    rw [arithmeticProgression_two, show x + (y - x) = y from by omega]
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  · refine ⟨y, x - y, by omega, ?_⟩
    rw [arithmeticProgression_two, show y + (x - y) = x from by omega]
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption

/- ## Part IV: Counting APs -/

/-- **Trivial upper bound.** A set of size N contains at most C(N, k) many
    k-APs, since each AP (with d > 0) is a k-element subset. This is the
    elementary fact underlying `F_k(N, ℓ) ≤ N²` in the parent file. -/
theorem countAPs_le_choose (A : Finset ℕ) (k : ℕ) :
    countAPs A k ≤ A.card.choose k := by
  unfold countAPs
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSA, a, d, hd, rfl⟩ := hS
  rw [Finset.mem_powersetCard]
  exact ⟨hSA, arithmeticProgression_card a d k hd⟩

/-- **Exact count of 2-APs.** Every set of size N has exactly C(N, 2) two-term
    APs: the 2-APs of A are precisely its 2-element subsets, since `{x, y}`
    with x < y equals the AP with start x and step y - x. -/
theorem countAPs_two (A : Finset ℕ) : countAPs A 2 = A.card.choose 2 := by
  unfold countAPs
  have hset : (A.powerset.filter fun S => ∃ a d, d > 0 ∧ S = arithmeticProgression a d 2)
      = A.powersetCard 2 := by
    ext S
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨hSA, a, d, hd, rfl⟩
      refine ⟨hSA, ?_⟩
      rw [arithmeticProgression_two]
      exact Finset.card_pair (by omega)
    · rintro ⟨hSA, hcard⟩
      refine ⟨hSA, ?_⟩
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
      rcases lt_or_gt_of_ne hxy with h | h
      · exact ⟨x, y - x, by omega, by
          rw [arithmeticProgression_two, show x + (y - x) = y from by omega]⟩
      · refine ⟨y, x - y, by omega, ?_⟩
        rw [arithmeticProgression_two, show y + (x - y) = x from by omega]
        exact Finset.pair_comm x y
  rw [hset, Finset.card_powersetCard]

/-- The parent's `AP_free_has_2APs`: in a 3-AP-free set, the number of 2-APs is
    C(N, 2). The 3-AP-free hypothesis is REDUNDANT — `countAPs_two` shows the
    identity holds for every finite set, regardless of any AP-freeness. -/
theorem AP_free_has_2APs (A : Finset ℕ) (_hA : ¬ContainsAP A 3) :
    countAPs A 2 = A.card.choose 2 :=
  countAPs_two A

end Erdos179Combinatorics
