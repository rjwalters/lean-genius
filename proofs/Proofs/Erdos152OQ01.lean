/-
  Erdős #152 OQ-01: Two Isolated Elements in Sidon Sumsets

  Strengthens gap_existence_pigeonhole (≥1 isolated element for |A|≥5)
  to ≥2 isolated elements for sufficiently large Sidon sets.

  Key insight: Sidon difference injectivity gives at most one consecutive
  pair in A. When no consecutive pair exists AND min(A) ≥ 1, both
  2·min(A) and 2·max(A) are isolated in A+A.

  Parent: Erdos152Problem.lean
-/

import Proofs.Erdos152Problem

open scoped Pointwise

/-
## The Easy Case: No Consecutive Pair, Positive Minimum

When A has no consecutive pair (no x, x+1 both in A) and min(A) ≥ 1,
both endpoints 2·min and 2·max are isolated.
-/

/-- If min(A) ≥ 1, then 2·min(A) - 1 ∉ A+A (below the minimum possible sum). -/
private theorem min_sum_left_isolated (A : Finset ℕ) (hne : A.Nonempty)
    (hm_pos : A.min' hne ≥ 1) :
    A.min' hne + A.min' hne - 1 ∉ sumsetFinset A := by
  set m := A.min' hne
  intro h
  have sum_ge : ∀ s ∈ sumsetFinset A, m + m ≤ s := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    linarith [Finset.min'_le A a ha, Finset.min'_le A b hb]
  linarith [sum_ge _ h]

/-- If min(A)+1 ∉ A, then 2·min(A)+1 ∉ A+A: the only way to sum to
    2m+1 from elements ≥ m is via m and m+1. -/
private theorem min_sum_right_isolated (A : Finset ℕ) (hne : A.Nonempty)
    (hm1 : A.min' hne + 1 ∉ A) :
    A.min' hne + A.min' hne + 1 ∉ sumsetFinset A := by
  set m := A.min' hne
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
  have ha_ge := Finset.min'_le A a ha
  have hb_ge := Finset.min'_le A b hb
  -- a + b = 2m + 1, a ≥ m, b ≥ m → one is m+1
  by_cases ha_eq : a = m
  · have : b = m + 1 := by omega
    exact hm1 (this ▸ hb)
  · have : a = m + 1 := by omega
    exact hm1 (this ▸ ha)

/-- If max(A)-1 ∉ A, then 2·max(A)-1 ∉ A+A: the only way to sum to
    2M-1 from elements ≤ M is via M and M-1. -/
private theorem max_sum_left_isolated (A : Finset ℕ) (hne : A.Nonempty)
    (hM_ge4 : A.max' hne ≥ 4)
    (hM1 : A.max' hne - 1 ∉ A) :
    A.max' hne + A.max' hne - 1 ∉ sumsetFinset A := by
  set M := A.max' hne
  intro h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
  have ha_le := Finset.le_max' A a ha
  have hb_le := Finset.le_max' A b hb
  by_cases ha_eq : a = M
  · exact hM1 (show M - 1 ∈ A by have : b = M - 1 := by omega; rwa [this] at hb)
  · exact hM1 (show M - 1 ∈ A by have : a = M - 1 := by omega; rwa [this] at ha)

/-- 2·max(A)+1 ∉ A+A (exceeds the maximum sum). -/
private theorem max_sum_right_isolated (A : Finset ℕ) (hne : A.Nonempty) :
    A.max' hne + A.max' hne + 1 ∉ sumsetFinset A := by
  set M := A.max' hne
  intro h
  have sum_le : ∀ s ∈ sumsetFinset A, s ≤ M + M := fun s hs => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hs
    linarith [Finset.le_max' A a ha, Finset.le_max' A b hb]
  linarith [sum_le _ h]

/-- **Two isolated elements (no-consecutive-pair case)**:
    If A is a Sidon set with |A| ≥ 5, min(A) ≥ 1, and A has no consecutive pair
    (max(A)-1 ∉ A and min(A)+1 ∉ A), then both 2·min(A) and 2·max(A) are isolated,
    giving isolatedCount(A) ≥ 2. -/
theorem two_isolated_no_consecutive (A : Finset ℕ) (hS : IsSidonFinset A)
    (hn : A.card ≥ 5)
    (hm_pos : A.min' (Finset.card_pos.mp (by omega)) ≥ 1)
    (hM1 : A.max' (Finset.card_pos.mp (by omega)) - 1 ∉ A)
    (hm1 : A.min' (Finset.card_pos.mp (by omega)) + 1 ∉ A) :
    isolatedCount A ≥ 2 := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set M := A.max' hne
  set m := A.min' hne
  have hM_mem : M ∈ A := Finset.max'_mem A hne
  have hm_mem : m ∈ A := Finset.min'_mem A hne
  have hM4 : M ≥ 4 := by
    have : A ⊆ Finset.range (M + 1) := fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ.mpr (Finset.le_max' A a ha))
    linarith [Finset.card_le_card this, Finset.card_range (M + 1)]
  have hm_ne_M : m ≠ M := by
    intro h; subst h
    have : A = {m} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨hne, fun x hx => le_antisymm (Finset.le_max' A x hx) (Finset.min'_le A x hx)⟩
    simp [this] at hn
  -- Both sums are in A+A
  have h2M_in : M + M ∈ sumsetFinset A := Finset.add_mem_add hM_mem hM_mem
  have h2m_in : m + m ∈ sumsetFinset A := Finset.add_mem_add hm_mem hm_mem
  -- They are different
  have h_ne : m + m ≠ M + M := by omega
  -- Both are isolated
  have h2M_iso : m + m ∈ (sumsetFinset A).filter (fun s =>
      s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A) := by
    rw [Finset.mem_filter]
    exact ⟨h2m_in,
      min_sum_left_isolated A hne hm_pos,
      min_sum_right_isolated A hne hm1⟩
  have h2m_iso : M + M ∈ (sumsetFinset A).filter (fun s =>
      s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A) := by
    rw [Finset.mem_filter]
    exact ⟨h2M_in,
      max_sum_left_isolated A hne hM4 hM1,
      max_sum_right_isolated A hne⟩
  -- Two distinct elements in the filtered set → card ≥ 2
  calc isolatedCount A
      = ((sumsetFinset A).filter (fun s =>
          s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A)).card := rfl
    _ ≥ ({m + m, M + M} : Finset ℕ).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h2M_iso
        · exact h2m_iso
    _ = 2 := Finset.card_pair h_ne

/-- **Main theorem (partial)**: For Sidon sets of size ≥ 7 with min ≥ 1,
    isolatedCount ≥ 2. Full proof would handle all cases. -/
theorem gap_existence_two (A : Finset ℕ) (hS : IsSidonFinset A)
    (hn : A.card ≥ 7) (hm_pos : A.min' (Finset.card_pos.mp (by omega)) ≥ 1) :
    isolatedCount A ≥ 2 := by
  have hne : A.Nonempty := Finset.card_pos.mp (by omega)
  set M := A.max' hne
  set m := A.min' hne
  have hM_mem : M ∈ A := Finset.max'_mem A hne
  have hm_mem : m ∈ A := Finset.min'_mem A hne
  -- Sidon sets have at most one consecutive pair
  by_cases hM1 : M - 1 ∈ A
  · by_cases hm1 : m + 1 ∈ A
    · -- Both consecutive pairs → A has ≤ 2 elements, contradiction
      exfalso
      have hdiff := sidon_diff_injective hS hM_mem hM1 hm1 hm_mem
        (by omega) (by omega) (by omega)
      have : A ⊆ ({m, m + 1} : Finset ℕ) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have := Finset.min'_le A x hx; have := Finset.le_max' A x hx; omega
      have : A.card ≤ 2 := by
        calc A.card ≤ ({m, m + 1} : Finset ℕ).card := Finset.card_le_card this
          _ ≤ 1 + 1 := Finset.card_insert_le _ _
          _ = 2 := by ring
      omega
    · -- M-1 ∈ A, m+1 ∉ A: 2m is isolated. Need second isolated element.
      -- This case requires interior analysis (harder).
      sorry
  · by_cases hm1 : m + 1 ∈ A
    · -- M-1 ∉ A, m+1 ∈ A: 2M is isolated. Need second from interior.
      sorry
    · -- Neither M-1 nor m+1 in A: both endpoints isolated
      exact two_isolated_no_consecutive A hS (by omega) hm_pos hM1 hm1
