/-
  Aristotle targets for Erdős Problem #817
  Routine supporting lemmas for automated proof search.
  See Erdos817Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (g_3(n) ≫ 3^n)
  - NOT the Erdős-Sárközy partial result (deep sieve argument)
  - Routine combinatorics: subset sum cardinalities, AP-free small sets, Icc bounds
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace Erdos817Aristotle

open Finset Filter Nat

/-
  ## Section 1: Arithmetic Progression Freeness

  A set with fewer than 3 elements cannot contain a 3-term AP.
  These support g3_one and related small-case bounds.
-/

-- Aristotle target: set of cardinality < 3 is 3-AP-free
-- If |S| < 3, there are no 3 distinct elements, so no 3-AP exists
theorem apFree_of_card_lt_three (S : Finset ℕ) (hS : S.card < 3) :
    ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ (S : Set ℕ) := by
  intro a d hd
  -- The 3 values a, a+d, a+2d are distinct (since d > 0)
  -- S has < 3 elements, so at least one is missing
  by_contra h
  push_neg at h
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  simp only [Finset.mem_coe, zero_mul, add_zero, one_mul, Nat.reduceMul] at h0 h1 h2
  have hdistinct : ({a, a + d, a + 2 * d} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem, Finset.card_singleton]
    · simp; omega
    · simp; omega
  have hsub : ({a, a + d, a + 2 * d} : Finset ℕ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  exact absurd (Finset.card_le_card hsub) (by omega)

-- Aristotle target: {0, 1} contains no 3-term AP
-- Only 2 elements, need 3 for an AP
theorem apFree_zero_one : ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ ({0, 1} : Set ℕ) := by
  intro a d hd
  -- If a ≥ 2, then a ∉ {0,1}
  -- If a = 0, then a + 2d ≥ 2 so a + 2d ∉ {0,1}
  -- If a = 1, then a + d ≥ 2 so a + d ∉ {0,1}
  by_cases ha0 : a ≥ 2
  · exact ⟨0, by omega, by simp [Set.mem_insert_iff]; omega⟩
  · push_neg at ha0
    interval_cases a
    · exact ⟨2, by omega, by simp [Set.mem_insert_iff]; omega⟩
    · exact ⟨1, by omega, by simp [Set.mem_insert_iff]; omega⟩

-- Aristotle target: no 3-AP in a 2-element set of naturals
theorem two_element_nat_set_apFree (x y : ℕ) (hxy : x ≠ y) :
    ∀ a d, d > 0 → ∃ i < 3, a + i * d ∉ ({x, y} : Set ℕ) := by
  have hcard : ({x, y} : Finset ℕ).card < 3 := by
    rw [Finset.card_insert_of_not_mem (by simp [hxy]), Finset.card_singleton]; omega
  intro a d hd
  obtain ⟨i, hi, hmem⟩ := apFree_of_card_lt_three {x, y} hcard a d hd
  exact ⟨i, hi, by simpa using hmem⟩

/-
  ## Section 2: Subset Sum Properties

  The subset sum set of a singleton {a} is {0, a}.
  Supporting g3_one: g_3(1) = 1 since {1} has AP-free subset sums.
-/

-- Local definition matching the main file
def subsetSumsLocal (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun B => B.sum id)

-- Aristotle target: subsetSums of singleton is {0, a}
theorem subsetSums_singleton (a : ℕ) :
    subsetSumsLocal {a} = {0, a} := by
  unfold subsetSumsLocal
  ext x
  simp only [Finset.mem_image, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨B, hB, rfl⟩
    have : B = ∅ ∨ B = {a} := by
      rcases Finset.eq_empty_or_nonempty B with rfl | ⟨b, hb⟩
      · left; rfl
      · right; ext y; simp only [Finset.mem_singleton]
        exact ⟨fun hy => (Finset.mem_singleton.mp (hB hy)), fun hy => hy ▸ hb⟩
    rcases this with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨∅, Finset.empty_subset _, by simp⟩
    · exact ⟨{a}, Finset.Subset.refl _, by simp⟩

-- Aristotle target: subsetSums of singleton has cardinality 2 (when a ≠ 0)
theorem card_subsetSums_singleton (a : ℕ) (ha : a ≠ 0) :
    (subsetSumsLocal {a}).card = 2 := by
  rw [subsetSums_singleton]
  rw [Finset.card_insert_of_not_mem (by simp [ha]), Finset.card_singleton]

-- Aristotle target: subsetSums of singleton has cardinality ≤ 2
theorem card_subsetSums_singleton_le (a : ℕ) :
    (subsetSumsLocal {a}).card ≤ 2 := by
  rw [subsetSums_singleton]
  exact le_trans (Finset.card_insert_le 0 {a}) (by simp)

/-
  ## Section 3: Icc Cardinality Bounds

  Any A ⊆ Icc 1 N with |A| = n requires N ≥ n.
  This supports g_ge_n: g_k(n) ≥ n.
-/

-- Aristotle target: |Icc 1 N| = N
theorem card_Icc_one (N : ℕ) : (Finset.Icc 1 N).card = N := by
  simp [Nat.card_Icc]

-- Aristotle target: if A ⊆ Icc 1 N then |A| ≤ N
theorem subset_Icc_card_le (A : Finset ℕ) (N : ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    A.card ≤ N := by
  calc A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
    _ = N := card_Icc_one N

-- Aristotle target: N ≥ n when some A ⊆ Icc 1 N has |A| = n
theorem Icc_contains_n_elements (A : Finset ℕ) (n N : ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hn : A.card = n) :
    N ≥ n := hn ▸ subset_Icc_card_le A N hA

/-
  ## Section 4: Powers of 3 are in Icc 1 (3^n)

  Supporting g3_le_exp: g_3(n) ≤ 3^n.
  The set {3^0, 3^1, ..., 3^(n-1)} ⊆ {1,...,3^n-1} ⊆ {1,...,3^n}.
-/

-- Aristotle target: 3^i ≥ 1 for all i (so powers of 3 are in Icc 1 ...)
theorem three_pow_pos (i : ℕ) : 0 < 3^i := by positivity

-- Aristotle target: 3^i ≤ 3^n for i < n
theorem three_pow_le_pow (i n : ℕ) (hi : i < n) : 3^i ≤ 3^n :=
  Nat.pow_le_pow_right (by norm_num) hi.le

-- Aristotle target: 3^i ∈ Finset.Icc 1 (3^n) for i < n
theorem three_pow_mem_Icc (i n : ℕ) (hi : i < n) :
    3^i ∈ Finset.Icc 1 (3^n) := by
  simp only [Finset.mem_Icc]
  exact ⟨three_pow_pos i, three_pow_le_pow i n hi⟩

end Erdos817Aristotle
