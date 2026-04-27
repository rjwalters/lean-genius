/-
  Aristotle targets for Erdős Problem #360: Partition Sum-Free Classes
  Routine supporting lemmas for automated proof search.
  See Erdos360Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main growth rate result (solved by Conlon-Fox-Pham 2021, axiomatized)
  - Concrete small cases: f(2) = 1 and f(4) = 2, which are decidable computations
  - Helper lemmas for sum-free partition witnesses
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets:
  - set1_is_2sum_free_ari: {1} is 2-sum-free (no subset sums to 2)
  - valid_partition_2_ari: {{1}} is a valid 1-partition of {1}
  - f_2_le_1_ari: f(2) ≤ 1 via the witness partition {{1}}
  - f_2_ge_1_ari: f(2) ≥ 1 (empty partition is invalid)
  - set12_is_4sum_free_ari: {1,2} is 4-sum-free
  - set3_is_4sum_free_ari: {3} is 4-sum-free
  - valid_partition_4_ari: {{1,2},{3}} is a valid 2-partition of {1,2,3}
  - f_4_le_2_ari: f(4) ≤ 2 via the witness partition
  - f_4_ge_2_ari: f(4) ≥ 2 (no single class covers {1,2,3})

  Excluded:
  - erdos_360_solved — axiomatized deep result (Conlon-Fox-Pham 2021)
  - alon_erdos_1996, vu_2007, conlon_fox_pham_2021 — all axioms
  - f(n) growth theorems — require analytic number theory
-/
import Mathlib
import Proofs.Erdos360Problem

namespace Erdos360Aristotle

open Erdos360 Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: f(2) = 1
-- ═══════════════════════════════════════════════════════════════════

/-- {1} is 2-sum-free: no subset of {1} sums to 2.
    Proof: Subsets are {} (sum 0) and {1} (sum 1), neither equals 2. -/
theorem set1_is_2sum_free_ari : IsNSumFree 2 {1} := by
  intro T hT
  fin_cases h : T using 2 <;> simp_all [IsNSumFree, Finset.subset_singleton_iff] <;> omega

/-- {{1}} is a valid 1-partition of {1,...,1} = {1}.
    Proof: {1} covers {1}, is 2-sum-free, and has 1 class. -/
theorem valid_partition_2_ari : IsValidPartition 2 {{(1 : ℕ)}} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP x hx
    simp at hP; subst hP; simp at hx; omega
  · intro P Q hP hQ hne
    simp at hP hQ; subst hP; subst hQ; exact absurd rfl hne
  · intro x hx1 hx2
    simp; omega
  · intro P hP
    simp at hP; subst hP
    exact set1_is_2sum_free_ari

/-- f(2) ≤ 1: the single-class partition {{1}} witnesses 1 class suffices. -/
theorem f_2_le_1_ari : f 2 ≤ 1 := by
  apply Nat.sInf_le
  exact ⟨{{1}}, rfl, valid_partition_2_ari⟩

/-- f(2) ≥ 1: we need at least 1 class to cover {1}.
    Proof: 0 classes can't cover {1}. -/
theorem f_2_ge_1_ari : f 2 ≥ 1 := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro h
  have := Nat.sInf_eq_zero.mp h
  rcases this with ⟨_, h⟩ | h
  · obtain ⟨parts, hcard, hval⟩ := h
    have := hval.2.2.1 1 (by omega) (by omega)
    obtain ⟨P, hP, _⟩ := this
    have := Finset.card_pos.mpr ⟨P, hP⟩
    omega
  · simp [ValidPartitionSizes] at h

-- ═══════════════════════════════════════════════════════════════════
-- PART II: f(4) = 2
-- ═══════════════════════════════════════════════════════════════════

/-- {1, 2} is 4-sum-free: no subset sums to 4.
    Subsets: {}, {1}, {2}, {1,2}. Sums: 0, 1, 2, 3. None equals 4. -/
theorem set12_is_4sum_free_ari : IsNSumFree 4 ({1, 2} : Finset ℕ) := by
  intro T hT
  have hT' : T ⊆ {1, 2} := hT
  fin_cases h : T using 4 <;> simp_all [Finset.subset_pair_iff] <;> omega

/-- {3} is 4-sum-free: no subset sums to 4.
    Subsets: {}, {3}. Sums: 0, 3. Neither equals 4. -/
theorem set3_is_4sum_free_ari : IsNSumFree 4 ({3} : Finset ℕ) := by
  intro T hT
  fin_cases h : T using 2 <;> simp_all [Finset.subset_singleton_iff] <;> omega

/-- {{1,2},{3}} is a valid 2-partition of {1,2,3}.
    Covers: 1 ∈ {1,2}, 2 ∈ {1,2}, 3 ∈ {3}. Both classes are 4-sum-free. -/
theorem valid_partition_4_ari : IsValidPartition 4 ({{(1:ℕ), 2}, {3}} : Finset (Finset ℕ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP x hx
    simp at hP; rcases hP with rfl | rfl <;> simp at hx <;> omega
  · intro P Q hP hQ hne
    simp at hP hQ
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> simp_all <;> decide
  · intro x hx1 hx2
    simp; omega
  · intro P hP
    simp at hP
    rcases hP with rfl | rfl
    · exact set12_is_4sum_free_ari
    · exact set3_is_4sum_free_ari

/-- f(4) ≤ 2: partition {{1,2},{3}} witnesses 2 classes suffice. -/
theorem f_4_le_2_ari : f 4 ≤ 2 := by
  apply Nat.sInf_le
  exact ⟨{{1, 2}, {3}}, rfl, valid_partition_4_ari⟩

/-- f(4) ≥ 2: a single class cannot cover {1,2,3} while being 4-sum-free.
    Note: {1,3} sums to 4, so any single class covering {1,3} is not 4-sum-free. -/
theorem f_4_ge_2_ari : f 4 ≥ 2 := by
  sorry

end Erdos360Aristotle
