/-
Erdős Problem #360: Partition Sum-Free Classes

Let f(n) be minimal such that {1,...,n-1} can be partitioned into f(n) classes
so that n cannot be expressed as a sum of distinct elements from any single class.
How fast does f(n) grow?

**Answer**: f(n) ≍ n^{1/3} / (log n)^{1/3} (log log n)^{2/3} · (n/φ(n))

Determined up to a multiplicative constant by Conlon-Fox-Pham (2021).

Reference: https://erdosproblems.com/360
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Nth

namespace Erdos360

/-
## Overview

This problem concerns the minimum number of classes needed to partition {1,...,n-1}
such that no class contains a subset summing to n. This is related to sum-free sets
and Ramsey-type problems in additive combinatorics.

### Key Definitions

A **sum-free subset** of integers avoids representing any element as a sum of
distinct elements from the same set. Here we want each partition class to be
"n-sum-free" - no subset sums to exactly n.
-/

/-- A set S ⊆ {1,...,n-1} is n-sum-free if no subset of distinct elements sums to n. -/
def IsNSumFree (n : ℕ) (S : Finset ℕ) : Prop :=
  ∀ T : Finset ℕ, T ⊆ S → T.sum id ≠ n

/-- A partition of {1,...,n-1} into classes that are all n-sum-free. -/
def IsValidPartition (n : ℕ) (parts : Finset (Finset ℕ)) : Prop :=
  -- All elements are from {1,...,n-1}
  (∀ P ∈ parts, ∀ x ∈ P, 1 ≤ x ∧ x < n) ∧
  -- Parts are disjoint
  (∀ P Q : Finset ℕ, P ∈ parts → Q ∈ parts → P ≠ Q → Disjoint P Q) ∧
  -- Union covers {1,...,n-1}
  (∀ x : ℕ, 1 ≤ x → x < n → ∃ P ∈ parts, x ∈ P) ∧
  -- Each part is n-sum-free
  (∀ P ∈ parts, IsNSumFree n P)

/-
## The Function f(n)

f(n) is the minimum number of parts in a valid partition.
-/

/-- The set of valid partition sizes for n. -/
def ValidPartitionSizes (n : ℕ) : Set ℕ :=
  {k : ℕ | ∃ parts : Finset (Finset ℕ), parts.card = k ∧ IsValidPartition n parts}

/-- f(n) is the minimum valid partition size. -/
noncomputable def f (n : ℕ) : ℕ := sInf (ValidPartitionSizes n)

/-
## Historical Results

### Alon-Erdős (1996)
Proved that f(n) = n^{1/3 + o(1)}, with explicit bounds:
  n^{1/3} / (log n)^{4/3} ≪ f(n) ≪ n^{1/3} / (log n)^{1/3} · (log log n)^{1/3}

### Vu (2007)
Improved the lower bound to:
  f(n) ≫ n^{1/3} / log n

### Conlon-Fox-Pham (2021)
Determined the exact order of growth:
  f(n) ≍ n^{1/3} · (n/φ(n)) / ((log n)^{1/3} · (log log n)^{2/3})
-/

/-- Alon-Erdős (1996): f(n) grows like n^{1/3 + o(1)}.
This establishes the basic growth rate. -/
axiom alon_erdos_1996 :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
  ∀ n : ℕ, n ≥ 2 →
    c₁ * (n : ℝ)^(1/3 : ℝ) / (Real.log n)^(4/3 : ℝ) ≤ f n ∧
    (f n : ℝ) ≤ c₂ * (n : ℝ)^(1/3 : ℝ) / (Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(1/3 : ℝ)

/-- Vu (2007): Improved lower bound f(n) ≫ n^{1/3} / log n. -/
axiom vu_2007 :
  ∃ c : ℝ, c > 0 ∧
  ∀ n : ℕ, n ≥ 3 →
    c * (n : ℝ)^(1/3 : ℝ) / Real.log n ≤ f n

/-- Conlon-Fox-Pham (2021): Determined exact order of growth.
f(n) ≍ n^{1/3} · (n/φ(n)) / ((log n)^{1/3} · (log log n)^{2/3}) -/
axiom conlon_fox_pham_2021 :
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
  ∀ n : ℕ, n ≥ 10 →
    let φn := Nat.totient n
    c₁ * (n : ℝ)^(1/3 : ℝ) * ((n : ℝ) / (φn : ℝ)) / ((Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(2/3 : ℝ)) ≤ f n ∧
    (f n : ℝ) ≤ c₂ * (n : ℝ)^(1/3 : ℝ) * ((n : ℝ) / (φn : ℝ)) / ((Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(2/3 : ℝ))

/-
## Key Observations

### Why n^{1/3}?

The greedy bound: The largest element ≤ n-1 that can be in a sum-free class is roughly
the cube root. If we include elements up to n^{1/3}, then choosing 3 such elements
can easily sum to n. This gives a rough lower bound of n^{1/3} classes.

### Role of n/φ(n)

The factor n/φ(n) captures arithmetic structure. When n has many small prime factors,
φ(n) is much smaller than n, making n/φ(n) large. This means more partitions are needed
because arithmetic progressions with common factors create more sum constraints.
-/

/-- For prime n, φ(n) = n - 1, so n/φ(n) ≈ 1. -/
theorem prime_totient_ratio (p : ℕ) (hp : Nat.Prime p) :
    (p : ℚ) / Nat.totient p = p / (p - 1) := by
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]

/-- For highly composite n, n/φ(n) can be large (like log log n for primorials). -/
axiom primorial_totient_ratio :
  ∀ k : ℕ, k ≥ 2 →
    let n : ℕ := (Finset.range k).prod (fun i => Nat.nth Nat.Prime i)
    (n : ℝ) / (Nat.totient n : ℝ) ≥ Real.log (Real.log k)

/-
## Small Cases

For small n, we can compute f(n) directly.
-/

/-- f(2) = 1: {1} is already 2-sum-free (can't sum to 2 with one element). -/
theorem f_2 : f 2 = 1 := by
  -- `1` is achievable: the single class `{1}`.
  have hmem1 : (1 : ℕ) ∈ ValidPartitionSizes 2 := by
    refine ⟨{{1}}, Finset.card_singleton _, ?_, ?_, ?_, ?_⟩
    · -- every element of every class lies in {1,...,1}
      intro P hP x hx
      rw [Finset.mem_singleton] at hP
      subst hP
      rw [Finset.mem_singleton] at hx
      subst hx
      omega
    · -- classes are pairwise disjoint (there is only one)
      intro P Q hP hQ hPQ
      rw [Finset.mem_singleton] at hP hQ
      subst hP; subst hQ
      exact absurd rfl hPQ
    · -- coverage of {1,...,1}
      intro x hx1 hx2
      interval_cases x
      exact ⟨{1}, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    · -- each class is 2-sum-free
      intro P hP
      rw [Finset.mem_singleton] at hP
      subst hP
      intro T hT
      have hb : T.sum id ≤ ({1} : Finset ℕ).sum id :=
        Finset.sum_le_sum_of_subset (f := id) hT
      have hval : ({1} : Finset ℕ).sum id = 1 := by simp
      omega
  -- `0` is not achievable: the empty partition cannot cover `1`.
  have hmem0 : (0 : ℕ) ∉ ValidPartitionSizes 2 := by
    rintro ⟨parts, hcard, _, _, hcov, _⟩
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨P, hP, _⟩ := hcov 1 (by norm_num) (by norm_num)
    exact absurd hP (Finset.notMem_empty P)
  -- The infimum of a set of naturals containing `1` but not `0` is `1`.
  have hle : sInf (ValidPartitionSizes 2) ≤ 1 := Nat.sInf_le hmem1
  have hmem : sInf (ValidPartitionSizes 2) ∈ ValidPartitionSizes 2 :=
    Nat.sInf_mem ⟨1, hmem1⟩
  have hne0 : sInf (ValidPartitionSizes 2) ≠ 0 := fun h => hmem0 (h ▸ hmem)
  show sInf (ValidPartitionSizes 2) = 1
  omega

/-- f(4) = 2: Need 2 classes because {1,3} sums to 4. -/
theorem f_4 : f 4 = 2 := by
  -- `2` is achievable: the partition `{{1,2}, {3}}`.
  -- `{1,2}` and `{3}` are distinct, so the partition has two classes.
  have hne12 : ({1, 2} : Finset ℕ) ≠ ({3} : Finset ℕ) := by
    intro h
    have h2 : (2 : ℕ) ∈ ({3} : Finset ℕ) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self 2)
    rw [Finset.mem_singleton] at h2
    exact absurd h2 (by norm_num)
  have hmem2 : (2 : ℕ) ∈ ValidPartitionSizes 4 := by
    refine ⟨{{1, 2}, {3}}, ?_, ?_, ?_, ?_, ?_⟩
    · -- the two classes are distinct, so the cardinality is 2
      rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne12),
        Finset.card_singleton]
    · -- membership bounds
      intro P hP x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · rw [Finset.mem_singleton] at hx
        subst hx
        omega
    · -- pairwise disjointness
      intro P Q hP hQ hPQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact absurd rfl hPQ
      · rw [Finset.disjoint_left]
        intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> simp
      · rw [Finset.disjoint_left]
        intro a ha
        rw [Finset.mem_singleton] at ha
        subst ha
        simp
      · exact absurd rfl hPQ
    · -- coverage of {1,2,3}
      intro x hx1 hx2
      interval_cases x
      · exact ⟨{1, 2}, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
      · exact ⟨{1, 2}, Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
      · exact ⟨{3}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          Finset.mem_singleton_self _⟩
    · -- each class is 4-sum-free (max subset sum is 3)
      intro P hP
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · intro T hT
        have hb : T.sum id ≤ ({1, 2} : Finset ℕ).sum id :=
          Finset.sum_le_sum_of_subset (f := id) hT
        have hval : ({1, 2} : Finset ℕ).sum id = 3 := by
          rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]; norm_num
        omega
      · intro T hT
        have hb : T.sum id ≤ ({3} : Finset ℕ).sum id :=
          Finset.sum_le_sum_of_subset (f := id) hT
        have hval : ({3} : Finset ℕ).sum id = 3 := by simp
        omega
  -- `0` is not achievable: the empty partition cannot cover `1`.
  have hmem0 : (0 : ℕ) ∉ ValidPartitionSizes 4 := by
    rintro ⟨parts, hcard, _, _, hcov, _⟩
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨P, hP, _⟩ := hcov 1 (by norm_num) (by norm_num)
    exact absurd hP (Finset.notMem_empty P)
  -- `1` is not achievable: a single class covering {1,2,3} contains {1,3} → 4.
  have hmem1 : (1 : ℕ) ∉ ValidPartitionSizes 4 := by
    rintro ⟨parts, hcard, _, _, hcov, hsf⟩
    rw [Finset.card_eq_one] at hcard
    obtain ⟨P, hPeq⟩ := hcard
    subst hPeq
    obtain ⟨Q1, hQ1, h1P⟩ := hcov 1 (by norm_num) (by norm_num)
    obtain ⟨Q3, hQ3, h3P⟩ := hcov 3 (by norm_num) (by norm_num)
    rw [Finset.mem_singleton] at hQ1 hQ3
    rw [hQ1] at h1P
    rw [hQ3] at h3P
    have hfree : IsNSumFree 4 P := hsf P (Finset.mem_singleton_self P)
    have hsub : ({1, 3} : Finset ℕ) ⊆ P := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1P
      · exact h3P
    have hval : ({1, 3} : Finset ℕ).sum id = 4 := by
      rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 3)]; norm_num
    exact hfree {1, 3} hsub hval
  -- The infimum of a set containing `2` but not `0` or `1` is `2`.
  have hle : sInf (ValidPartitionSizes 4) ≤ 2 := Nat.sInf_le hmem2
  have hmem : sInf (ValidPartitionSizes 4) ∈ ValidPartitionSizes 4 :=
    Nat.sInf_mem ⟨2, hmem2⟩
  have hne0 : sInf (ValidPartitionSizes 4) ≠ 0 := fun h => hmem0 (h ▸ hmem)
  have hne1 : sInf (ValidPartitionSizes 4) ≠ 1 := fun h => hmem1 (h ▸ hmem)
  show sInf (ValidPartitionSizes 4) = 2
  omega

/-- f(3) = 2: the whole ground set `{1,2}` sums to 3, so `1` and `2` must be
    separated; the partition `{{1}, {2}}` is optimal. -/
theorem f_3 : f 3 = 2 := by
  -- `2` is achievable: the partition `{{1}, {2}}`.
  have hne : ({1} : Finset ℕ) ≠ ({2} : Finset ℕ) := by
    intro h
    have h1 : (1 : ℕ) ∈ ({2} : Finset ℕ) := h ▸ Finset.mem_singleton_self 1
    rw [Finset.mem_singleton] at h1
    exact absurd h1 (by norm_num)
  have hmem2 : (2 : ℕ) ∈ ValidPartitionSizes 3 := by
    refine ⟨{{1}, {2}}, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
    · intro P hP x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;>
        (rw [Finset.mem_singleton] at hx; subst hx; omega)
    · intro P Q hP hQ hPQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact absurd rfl hPQ
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_singleton] at ha; subst ha; decide
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_singleton] at ha; subst ha; decide
      · exact absurd rfl hPQ
    · intro x hx1 hx2
      interval_cases x
      · exact ⟨{1}, Finset.mem_insert_self _ _, Finset.mem_singleton_self _⟩
      · exact ⟨{2}, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
          Finset.mem_singleton_self _⟩
    · intro P hP
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · intro T hT
        have hb : T.sum id ≤ ({1} : Finset ℕ).sum id :=
          Finset.sum_le_sum_of_subset (f := id) hT
        have hval : ({1} : Finset ℕ).sum id = 1 := by simp
        omega
      · intro T hT
        have hb : T.sum id ≤ ({2} : Finset ℕ).sum id :=
          Finset.sum_le_sum_of_subset (f := id) hT
        have hval : ({2} : Finset ℕ).sum id = 2 := by simp
        omega
  -- `0` is not achievable: the empty partition cannot cover `1`.
  have hmem0 : (0 : ℕ) ∉ ValidPartitionSizes 3 := by
    rintro ⟨parts, hcard, _, _, hcov, _⟩
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨P, hP, _⟩ := hcov 1 (by norm_num) (by norm_num)
    exact absurd hP (Finset.notMem_empty P)
  -- `1` is not achievable: a single class covering `{1,2}` contains `{1,2}` → 3.
  have hmem1 : (1 : ℕ) ∉ ValidPartitionSizes 3 := by
    rintro ⟨parts, hcard, _, _, hcov, hsf⟩
    rw [Finset.card_eq_one] at hcard
    obtain ⟨P, hPeq⟩ := hcard
    subst hPeq
    obtain ⟨Q1, hQ1, h1P⟩ := hcov 1 (by norm_num) (by norm_num)
    obtain ⟨Q2, hQ2, h2P⟩ := hcov 2 (by norm_num) (by norm_num)
    rw [Finset.mem_singleton] at hQ1 hQ2
    rw [hQ1] at h1P
    rw [hQ2] at h2P
    have hfree : IsNSumFree 3 P := hsf P (Finset.mem_singleton_self P)
    have hsub : ({1, 2} : Finset ℕ) ⊆ P := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1P
      · exact h2P
    have hval : ({1, 2} : Finset ℕ).sum id = 3 := by
      rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 2)]; norm_num
    exact hfree {1, 2} hsub hval
  have hle : sInf (ValidPartitionSizes 3) ≤ 2 := Nat.sInf_le hmem2
  have hmem : sInf (ValidPartitionSizes 3) ∈ ValidPartitionSizes 3 :=
    Nat.sInf_mem ⟨2, hmem2⟩
  have hne0 : sInf (ValidPartitionSizes 3) ≠ 0 := fun h => hmem0 (h ▸ hmem)
  have hne1 : sInf (ValidPartitionSizes 3) ≠ 1 := fun h => hmem1 (h ▸ hmem)
  show sInf (ValidPartitionSizes 3) = 2
  omega

/-- f(5) = 2: `{1,4}` and `{2,3}` each sum to 5, so no single class works; the
    partition `{{1,2}, {3,4}}` is 5-sum-free (checked by enumerating subsets). -/
theorem f_5 : f 5 = 2 := by
  have hne : ({1, 2} : Finset ℕ) ≠ ({3, 4} : Finset ℕ) := by
    intro h
    have h1 : (1 : ℕ) ∈ ({3, 4} : Finset ℕ) := h ▸ Finset.mem_insert_self 1 {2}
    rw [Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hmem2 : (2 : ℕ) ∈ ValidPartitionSizes 5 := by
    refine ⟨{{1, 2}, {3, 4}}, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
    · intro P hP x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;>
        (rw [Finset.mem_insert, Finset.mem_singleton] at hx
         rcases hx with rfl | rfl <;> omega)
    · intro P Q hP hQ hPQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact absurd rfl hPQ
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> decide
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> decide
      · exact absurd rfl hPQ
    · intro x hx1 hx2
      interval_cases x
      · exact ⟨{1, 2}, by decide, by decide⟩
      · exact ⟨{1, 2}, by decide, by decide⟩
      · exact ⟨{3, 4}, by decide, by decide⟩
      · exact ⟨{3, 4}, by decide, by decide⟩
    · intro P hP
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;>
        (intro T hT
         rw [← Finset.mem_powerset] at hT
         fin_cases hT <;> decide)
  have hmem0 : (0 : ℕ) ∉ ValidPartitionSizes 5 := by
    rintro ⟨parts, hcard, _, _, hcov, _⟩
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨P, hP, _⟩ := hcov 1 (by norm_num) (by norm_num)
    exact absurd hP (Finset.notMem_empty P)
  -- `1` is not achievable: a single class covering `{1,…,4}` contains `{1,4}` → 5.
  have hmem1 : (1 : ℕ) ∉ ValidPartitionSizes 5 := by
    rintro ⟨parts, hcard, _, _, hcov, hsf⟩
    rw [Finset.card_eq_one] at hcard
    obtain ⟨P, hPeq⟩ := hcard
    subst hPeq
    obtain ⟨Q1, hQ1, h1P⟩ := hcov 1 (by norm_num) (by norm_num)
    obtain ⟨Q4, hQ4, h4P⟩ := hcov 4 (by norm_num) (by norm_num)
    rw [Finset.mem_singleton] at hQ1 hQ4
    rw [hQ1] at h1P
    rw [hQ4] at h4P
    have hfree : IsNSumFree 5 P := hsf P (Finset.mem_singleton_self P)
    have hsub : ({1, 4} : Finset ℕ) ⊆ P := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1P
      · exact h4P
    have hval : ({1, 4} : Finset ℕ).sum id = 5 := by
      rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 4)]; norm_num
    exact hfree {1, 4} hsub hval
  have hle : sInf (ValidPartitionSizes 5) ≤ 2 := Nat.sInf_le hmem2
  have hmem : sInf (ValidPartitionSizes 5) ∈ ValidPartitionSizes 5 :=
    Nat.sInf_mem ⟨2, hmem2⟩
  have hne0 : sInf (ValidPartitionSizes 5) ≠ 0 := fun h => hmem0 (h ▸ hmem)
  have hne1 : sInf (ValidPartitionSizes 5) ≠ 1 := fun h => hmem1 (h ▸ hmem)
  show sInf (ValidPartitionSizes 5) = 2
  omega

/-- f(6) = 2: `{1,5}`, `{2,4}` and `{1,2,3}` each sum to 6, so no single class
    works; the partition `{{1,2}, {3,4,5}}` is 6-sum-free. -/
theorem f_6 : f 6 = 2 := by
  have hne : ({1, 2} : Finset ℕ) ≠ ({3, 4, 5} : Finset ℕ) := by
    intro h
    have h1 : (1 : ℕ) ∈ ({3, 4, 5} : Finset ℕ) := h ▸ Finset.mem_insert_self 1 {2}
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at h1
    omega
  have hmem2 : (2 : ℕ) ∈ ValidPartitionSizes 6 := by
    refine ⟨{{1, 2}, {3, 4, 5}}, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact hne),
        Finset.card_singleton]
    · intro P hP x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl
      · rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> omega
      · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> omega
    · intro P Q hP hQ hPQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hP hQ
      rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
      · exact absurd rfl hPQ
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> decide
      · rw [Finset.disjoint_left]; intro a ha
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl | rfl <;> decide
      · exact absurd rfl hPQ
    · intro x hx1 hx2
      interval_cases x
      · exact ⟨{1, 2}, by decide, by decide⟩
      · exact ⟨{1, 2}, by decide, by decide⟩
      · exact ⟨{3, 4, 5}, by decide, by decide⟩
      · exact ⟨{3, 4, 5}, by decide, by decide⟩
      · exact ⟨{3, 4, 5}, by decide, by decide⟩
    · intro P hP
      rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;>
        (intro T hT
         rw [← Finset.mem_powerset] at hT
         fin_cases hT <;> decide)
  have hmem0 : (0 : ℕ) ∉ ValidPartitionSizes 6 := by
    rintro ⟨parts, hcard, _, _, hcov, _⟩
    rw [Finset.card_eq_zero] at hcard
    subst hcard
    obtain ⟨P, hP, _⟩ := hcov 1 (by norm_num) (by norm_num)
    exact absurd hP (Finset.notMem_empty P)
  -- `1` is not achievable: a single class covering `{1,…,5}` contains `{1,5}` → 6.
  have hmem1 : (1 : ℕ) ∉ ValidPartitionSizes 6 := by
    rintro ⟨parts, hcard, _, _, hcov, hsf⟩
    rw [Finset.card_eq_one] at hcard
    obtain ⟨P, hPeq⟩ := hcard
    subst hPeq
    obtain ⟨Q1, hQ1, h1P⟩ := hcov 1 (by norm_num) (by norm_num)
    obtain ⟨Q5, hQ5, h5P⟩ := hcov 5 (by norm_num) (by norm_num)
    rw [Finset.mem_singleton] at hQ1 hQ5
    rw [hQ1] at h1P
    rw [hQ5] at h5P
    have hfree : IsNSumFree 6 P := hsf P (Finset.mem_singleton_self P)
    have hsub : ({1, 5} : Finset ℕ) ⊆ P := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1P
      · exact h5P
    have hval : ({1, 5} : Finset ℕ).sum id = 6 := by
      rw [Finset.sum_pair (by norm_num : (1 : ℕ) ≠ 5)]; norm_num
    exact hfree {1, 5} hsub hval
  have hle : sInf (ValidPartitionSizes 6) ≤ 2 := Nat.sInf_le hmem2
  have hmem : sInf (ValidPartitionSizes 6) ∈ ValidPartitionSizes 6 :=
    Nat.sInf_mem ⟨2, hmem2⟩
  have hne0 : sInf (ValidPartitionSizes 6) ≠ 0 := fun h => hmem0 (h ▸ hmem)
  have hne1 : sInf (ValidPartitionSizes 6) ≠ 1 := fun h => hmem1 (h ▸ hmem)
  show sInf (ValidPartitionSizes 6) = 2
  omega

/-
## Connection to Subset Sums and Ramsey Theory

This problem is closely related to:
1. **Sum-free sets**: Sets where no element is a sum of two others
2. **Schur numbers**: Minimum k such that {1,...,n} can be k-colored avoiding x + y = z
3. **Complete sequences**: Sequences where every sufficiently large n is representable

The factor (log log n)^{2/3} in the denominator reflects deep structure from
analytic number theory and probabilistic combinatorics.
-/

/-- The main result: Problem #360 is solved. Exact order: f(n) ≍ n^{1/3}·(n/φ(n)) / ((log n)^{1/3}·(log log n)^{2/3}). -/
theorem erdos_360_solved :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, n ≥ 10 →
      let φn := Nat.totient n
      c₁ * (n : ℝ)^(1/3 : ℝ) * ((n : ℝ) / (φn : ℝ)) / ((Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(2/3 : ℝ)) ≤ f n ∧
      (f n : ℝ) ≤ c₂ * (n : ℝ)^(1/3 : ℝ) * ((n : ℝ) / (φn : ℝ)) / ((Real.log n)^(1/3 : ℝ) * (Real.log (Real.log n))^(2/3 : ℝ)) :=
  conlon_fox_pham_2021

end Erdos360
