/-
# Erdős #1097 OQ-01 — Common Differences in k-Term Arithmetic Progressions

Follow-up question: Generalize Erdős #1097 from 3-term APs to k-term APs.

## Question

For k ≥ 3, define D_k(A) = { d : ∃ a, {a, a+d, ..., a+(k-1)d} ⊆ A }.
How does |D_k(A)| grow as a function of n = |A| and k?

## Key Observations

- D_k(A) ⊆ D_3(A) for all k ≥ 3 (every k-AP contains 3-APs)
- D_k(A) is monotone decreasing in k: D_{k+1}(A) ⊆ D_k(A)
- For k > n, D_k(A) = {0} (only trivial AP possible)
- Translation invariance: D_k(A + c) = D_k(A)
- Symmetry: d ∈ D_k(A) ↔ -d ∈ D_k(A)

The 3-AP case (k=3) has best bounds Ω(n^{1.778}) to O(n^{11/6}).
For k ≥ 4 the bounds should be different since k-APs are rarer.

*Reference:* [erdosproblems.com/1097](https://www.erdosproblems.com/1097)
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic

open Finset

/- ## Core Definitions -/

/-- A k-term AP with base a and common difference d in set A:
    a, a+d, a+2d, ..., a+(k-1)d all belong to A. -/
def IsKAP (A : Set ℤ) (k : ℕ) (a d : ℤ) : Prop :=
  ∀ i : ℕ, i < k → a + i * d ∈ A

/-- The set of common differences of k-term APs in A. -/
def commonDiffK (A : Set ℤ) (k : ℕ) : Set ℤ :=
  { d | ∃ a, IsKAP A k a d }

/-- Finite version: common differences of k-term APs in a finite integer set. -/
noncomputable def commonDiffKFinset (A : Finset ℤ) (k : ℕ) : Finset ℤ :=
  (A - A).filter fun d => ∃ a ∈ A, ∀ i : ℕ, i < k → a + i * d ∈ A

/-- Count of distinct common differences |D_k(A)|. -/
noncomputable def numCommonDiffK (A : Finset ℤ) (k : ℕ) : ℕ :=
  (commonDiffKFinset A k).card

/- ## Infrastructure Lemmas -/

/-- Any k-AP with k ≥ 1 starts in A. -/
theorem isKAP_mem_base {A : Set ℤ} {k : ℕ} {a d : ℤ}
    (h : IsKAP A k a d) (hk : 0 < k) : a ∈ A := by
  have := h 0 hk
  simpa using this

/-- Trivial AP: for any a ∈ A, the constant sequence (d=0) is a k-AP. -/
theorem isKAP_zero_diff {A : Set ℤ} {k : ℕ} {a : ℤ}
    (ha : a ∈ A) : IsKAP A k a 0 := by
  intro i _
  simp [ha]

/-- Zero is always a common difference for nonempty sets (for any k). -/
theorem zero_mem_commonDiffK {A : Set ℤ} {k : ℕ}
    (hA : ∃ a, a ∈ A) : (0 : ℤ) ∈ commonDiffK A k := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a, isKAP_zero_diff ha⟩

/-- Monotonicity in k: a (k+1)-AP is also a k-AP. -/
theorem isKAP_of_succ {A : Set ℤ} {k : ℕ} {a d : ℤ}
    (h : IsKAP A (k + 1) a d) : IsKAP A k a d := by
  intro i hi
  exact h i (Nat.lt_succ_of_lt hi)

/-- Key containment: D_{k+1}(A) ⊆ D_k(A). More APs needed → fewer differences. -/
theorem commonDiffK_anti {A : Set ℤ} {k : ℕ} :
    commonDiffK A (k + 1) ⊆ commonDiffK A k := by
  intro d ⟨a, ha⟩
  exact ⟨a, isKAP_of_succ ha⟩

/-- General monotonicity: k ≤ m → D_m(A) ⊆ D_k(A). -/
theorem commonDiffK_mono_k {A : Set ℤ} {k m : ℕ} (hkm : k ≤ m) :
    commonDiffK A m ⊆ commonDiffK A k := by
  intro d ⟨a, ha⟩
  exact ⟨a, fun i hi => ha i (lt_of_lt_of_le hi hkm)⟩

/-- D_k(A) ⊆ D_3(A) for all k ≥ 3. -/
theorem commonDiffK_subset_diff3 {A : Set ℤ} {k : ℕ} (hk : 3 ≤ k) :
    commonDiffK A k ⊆ commonDiffK A 3 :=
  commonDiffK_mono_k hk

/-- Subset monotonicity: A ⊆ B → D_k(A) ⊆ D_k(B). -/
theorem commonDiffK_subset_mono {A B : Set ℤ} {k : ℕ} (h : A ⊆ B) :
    commonDiffK A k ⊆ commonDiffK B k := by
  intro d ⟨a, ha⟩
  exact ⟨a, fun i hi => h (ha i hi)⟩

/-- Symmetry: d ∈ D_k(A) → -d ∈ D_k(A). -/
theorem neg_mem_commonDiffK {A : Set ℤ} {k : ℕ} {d : ℤ}
    (hk : 2 ≤ k) (hd : d ∈ commonDiffK A k) : -d ∈ commonDiffK A k := by
  obtain ⟨a, ha⟩ := hd
  refine ⟨a + ((k : ���) - 1) * d, fun i hi => ?_⟩
  have hcast : (��(k - 1 - i) : ℤ) = (k : ℤ) - 1 - (i : ℤ) := by omega
  have key : a + ((k : ℤ) - 1) * d + (i : ℤ) * (-d) = a + ↑(k - 1 - i) * d := by
    rw [hcast]; ring
  rw [key]
  exact ha (k - 1 - i) (by omega)

/-- D_0(A) = ℤ for any set A (vacuous: every d is a common difference of
    a 0-term AP). -/
theorem commonDiffK_zero (A : Set ℤ) : commonDiffK A 0 = Set.univ := by
  ext d
  simp only [commonDiffK, IsKAP, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact ⟨0, fun i hi => absurd hi (by omega)⟩

/-- D_1(A) = ℤ for any nonempty set A (every d is a common difference of
    a 1-term AP, since any element alone suffices). -/
theorem commonDiffK_one {A : Set ℤ} (hA : ∃ a, a ∈ A) :
    commonDiffK A 1 = Set.univ := by
  ext d
  simp only [commonDiffK, IsKAP, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨a, ha⟩ := hA
  exact ⟨a, fun i hi => by interval_cases i; simpa using ha⟩

/-- For the finset version: D_k(A) ⊆ A - A. -/
theorem commonDiffKFinset_subset (A : Finset ℤ) (k : ℕ) :
    commonDiffKFinset A k ⊆ A - A :=
  filter_subset _ _

/-- Upper bound: |D_k(A)| ≤ |A|². -/
theorem numCommonDiffK_le_sq (A : Finset ℤ) (k : ℕ) :
    numCommonDiffK A k ≤ A.card * A.card := by
  unfold numCommonDiffK commonDiffKFinset
  calc ((A - A).filter _).card
      ≤ (A - A).card := card_filter_le _ _
    _ ≤ A.card * A.card := by
        rw [sub_def]
        exact le_trans card_image_le (le_of_eq (card_product A A))

/-- Finset version: monotonicity in k.
    For k ≤ m, D_m(A) ⊆ D_k(A) at the finset level. -/
theorem commonDiffKFinset_anti {A : Finset ℤ} {k : ℕ} :
    commonDiffKFinset A (k + 1) ⊆ commonDiffKFinset A k := by
  intro d hd
  unfold commonDiffKFinset at hd ⊢
  rw [mem_filter] at hd ⊢
  refine ⟨hd.1, ?_⟩
  obtain ⟨a, ha, hap⟩ := hd.2
  exact ⟨a, ha, fun i hi => hap i (Nat.lt_succ_of_lt hi)⟩

/-- Finset count monotonicity: |D_{k+1}(A)| ≤ |D_k(A)|. -/
theorem numCommonDiffK_anti (A : Finset ℤ) (k : ℕ) :
    numCommonDiffK A (k + 1) ≤ numCommonDiffK A k := by
  unfold numCommonDiffK
  exact card_le_card commonDiffKFinset_anti

/- ## Connection to 3-AP Case (Erdős #1097) -/

/-- IsKAP with k=3 is exactly IsThreeAP from the parent file. -/
theorem isKAP_three_iff (A : Set ℤ) (a d : ℤ) :
    IsKAP A 3 a d ↔ (a ∈ A ∧ a + d ∈ A ∧ a + 2 * d ∈ A) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h 0 (by omega); simpa using this
    · have := h 1 (by omega); simpa using this
    · have := h 2 (by omega); simpa using this
  · intro ⟨h0, h1, h2⟩ i hi
    interval_cases i <;> simpa using *

/- ## Main Open Question -/

/-- **Open Question (OQ-01).** For k ≥ 4, what is the growth rate of
    max_{|A|=n} |D_k(A)|? The 3-AP case has bounds Ω(n^{1.778}) to
    O(n^{11/6}). For larger k the answer should decrease since k-APs
    are rarer, but the precise exponent is unknown.

    Specifically: does there exist α(k) < 3/2 such that
    |D_k(A)| = O(n^{α(k)}) for all n-element sets? -/
def kAP_growth_question (k : ℕ) : Prop :=
  ∃ α : ℝ, ∃ C : ℝ, 0 < C ∧ 0 < α ∧
    ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
      (numCommonDiffK A k : ℝ) ≤ C * (n : ℝ) ^ α

/-- For k=3, the Katz-Tao bound gives α ≤ 11/6. -/
def kAP_three_bound : Prop :=
  kAP_growth_question 3

/-- Monotonicity of optimal exponent: if the k-AP growth question holds
    with exponent α, then the (k+1)-AP question holds with at most α. -/
theorem kAP_growth_mono {k : ℕ} {α C : ℝ} (hC : 0 < C) (hα : 0 < α)
    (h : ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
      (numCommonDiffK A k : ℝ) ≤ C * (n : ℝ) ^ α) :
    ∀ (n : ℕ) (A : Finset ℤ), A.card = n →
      (numCommonDiffK A (k + 1) : ℝ) ≤ C * (n : ℝ) ^ α := by
  intro n A hA
  calc (numCommonDiffK A (k + 1) : ℝ)
      ≤ (numCommonDiffK A k : ℝ) := by exact_mod_cast numCommonDiffK_anti A k
    _ ≤ C * (n : ℝ) ^ α := h n A hA

/- ## Summary -/

/-- D_k is anti-monotone in k and bounded by |A|²: for k ≥ 3,
    |D_k(A)| ≤ |D_3(A)| ≤ |A|². -/
theorem kAP_basic_bounds (A : Finset ℤ) (k : ℕ) :
    numCommonDiffK A k ≤ A.card * A.card :=
  numCommonDiffK_le_sq A k
