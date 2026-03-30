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
    · -- M-1 ∈ A, m+1 ∉ A: 2m is isolated. Second isolated: m + s₂.
      -- s₂ = min(A \ {m}), the second-smallest element.
      have hA'ne : (A.erase m).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hm_mem]; omega)
      set s₂ := (A.erase m).min' hA'ne
      have hs₂_er : s₂ ∈ A.erase m := Finset.min'_mem _ hA'ne
      have hs₂_mem : s₂ ∈ A := Finset.mem_of_mem_erase hs₂_er
      have hs₂_ne_m : s₂ ≠ m := Finset.ne_of_mem_erase hs₂_er
      have hs₂_gt_m : m < s₂ := lt_of_le_of_ne (Finset.min'_le A s₂ hs₂_mem) hs₂_ne_m.symm
      have hs₂_ge_m2 : s₂ ≥ m + 2 := by
        have : m + 1 ≠ s₂ := fun h => hm1 (h ▸ hs₂_mem); omega
      have hs₂_min : ∀ x ∈ A, x ≠ m → s₂ ≤ x :=
        fun x hx hxm => Finset.min'_le _ x (Finset.mem_erase.mpr ⟨hxm, hx⟩)
      -- s₂ + 1 ∉ A: Sidon prevents second consecutive pair
      have hs₂1_not : s₂ + 1 ∉ A := by
        intro hs₂1
        -- Sidon: (s₂+1) + (M-1) = s₂ + M → {s₂+1, M-1} = {s₂, M}
        have heq : (s₂ + 1) + (M - 1) = s₂ + M := by omega
        have hpair := hS (s₂ + 1) (M - 1) s₂ M hs₂1 hM1 hs₂_mem hM_mem heq
        have : s₂ + 1 ∈ ({s₂, M} : Finset ℕ) :=
          hpair ▸ Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · omega  -- s₂ + 1 = s₂
        · -- s₂ + 1 = M → s₂ = M - 1 → A ⊆ {m, M-1, M} → |A| ≤ 3
          have hsub : A ⊆ ({m, M - 1, M} : Finset ℕ) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases hxm : x = m; · left; exact hxm
            · right; have := hs₂_min x hx hxm; have := Finset.le_max' A x hx; omega
          linarith [Finset.card_le_card hsub,
            Finset.card_insert_le m ({M - 1, M} : Finset ℕ),
            Finset.card_insert_le (M - 1) ({M} : Finset ℕ),
            Finset.card_singleton M]
      -- m + s₂ ∈ A+A, and both neighbors absent
      have hms₂_in : m + s₂ ∈ sumsetFinset A := Finset.add_mem_add hm_mem hs₂_mem
      have hms₂_left : m + s₂ - 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        by_cases ham : a = m
        · -- b = s₂ - 1, but s₂-1 is between m and s₂ exclusive → not in A
          have : s₂ - 1 ∉ A := by
            intro hmem; have := hs₂_min (s₂ - 1) hmem (by omega); omega
          exact this (by have : b = s₂ - 1 := by omega; rwa [this] at hb)
        · -- a ≥ s₂, b ≥ m → a + b ≥ m + s₂ > m + s₂ - 1
          linarith [hs₂_min a ha ham, Finset.min'_le A b hb]
      have hms₂_right : m + s₂ + 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        by_cases ham : a = m
        · exact hs₂1_not (by have : b = s₂ + 1 := by omega; rwa [this] at hb)
        · by_cases hbm : b = m
          · exact hs₂1_not (by have : a = s₂ + 1 := by omega; rwa [this] at ha)
          · -- a ≥ s₂, b ≥ s₂ → a + b ≥ 2s₂ > m + s₂ + 1 (since s₂ ≥ m + 2)
            linarith [hs₂_min a ha ham, hs₂_min b hb hbm]
      -- 2m is also isolated
      have h2m_in : m + m ∈ sumsetFinset A := Finset.add_mem_add hm_mem hm_mem
      have h2m_left : m + m - 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
        linarith [Finset.min'_le A a ha, Finset.min'_le A b hb]
      have h2m_right : m + m + 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        have ha_ge := Finset.min'_le A a ha; have hb_ge := Finset.min'_le A b hb
        by_cases ha_eq : a = m
        · exact hm1 (by have : b = m + 1 := by omega; rwa [this] at hb)
        · exact hm1 (by have : a = m + 1 := by omega; rwa [this] at ha)
      -- Two distinct isolated elements → count ≥ 2
      have hne_sums : m + m ≠ m + s₂ := by omega
      calc isolatedCount A
          = ((sumsetFinset A).filter (fun s =>
              s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A)).card := rfl
        _ ≥ ({m + m, m + s₂} : Finset ℕ).card := by
            apply Finset.card_le_card; intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨h2m_in, h2m_left, h2m_right⟩
            · exact Finset.mem_filter.mpr ⟨hms₂_in, hms₂_left, hms₂_right⟩
        _ = 2 := Finset.card_pair hne_sums
  · by_cases hm1 : m + 1 ∈ A
    · -- M-1 ∉ A, m+1 ∈ A: 2M is isolated. Second isolated: M + s_last.
      -- s_last = max(A \ {M}), the second-largest element.
      have hM4 : M ≥ 4 := by
        have : A ⊆ Finset.range (M + 1) := fun a ha =>
          Finset.mem_range.mpr (Nat.lt_succ.mpr (Finset.le_max' A a ha))
        linarith [Finset.card_le_card this, Finset.card_range (M + 1)]
      have hA'ne : (A.erase M).Nonempty :=
        Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hM_mem]; omega)
      set sL := (A.erase M).max' hA'ne
      have hsL_er : sL ∈ A.erase M := Finset.max'_mem _ hA'ne
      have hsL_mem : sL ∈ A := Finset.mem_of_mem_erase hsL_er
      have hsL_ne_M : sL ≠ M := Finset.ne_of_mem_erase hsL_er
      have hsL_lt_M : sL < M := lt_of_le_of_ne (Finset.le_max' A sL hsL_mem) hsL_ne_M
      have hsL_le_M2 : sL ≤ M - 2 := by
        have : M - 1 ≠ sL := fun h => hM1 (h ▸ hsL_mem); omega
      have hsL_max : ∀ x ∈ A, x ≠ M → x ≤ sL :=
        fun x hx hxM => Finset.le_max' _ x (Finset.mem_erase.mpr ⟨hxM, hx⟩)
      -- sL - 1 ∉ A: Sidon prevents second consecutive pair (m, m+1 already exists)
      have hsL_prev_not : sL - 1 ∉ A := by
        intro hsL_prev
        -- Sidon: sL + m = (sL-1) + (m+1) → {sL, m} = {sL-1, m+1}
        have heq : sL + m = (sL - 1) + (m + 1) := by omega
        have hpair := hS sL m (sL - 1) (m + 1) hsL_mem hm_mem hsL_prev hm1 heq
        have : sL ∈ ({sL - 1, m + 1} : Finset ℕ) :=
          hpair ▸ Finset.mem_insert_self _ _
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · omega  -- sL = sL - 1
        · -- sL = m + 1 → A ⊆ {m, m+1, M} → |A| ≤ 3
          have hsub : A ⊆ ({m, m + 1, M} : Finset ℕ) := by
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton]
            by_cases hxM : x = M; · right; right; exact hxM
            · left; have := hsL_max x hx hxM; have := Finset.min'_le A x hx; omega
          linarith [Finset.card_le_card hsub,
            Finset.card_insert_le m ({m + 1, M} : Finset ℕ),
            Finset.card_insert_le (m + 1) ({M} : Finset ℕ),
            Finset.card_singleton M]
      -- sL + 1 ∉ A (between sL and M, no elements since sL = max(A\{M}))
      have hsL_next_not : sL + 1 ∉ A := by
        intro hs; have := hsL_max (sL + 1) hs (by omega); omega
      -- M + sL ∈ A+A, and both neighbors absent
      have hMsL_in : M + sL ∈ sumsetFinset A := Finset.add_mem_add hM_mem hsL_mem
      have hMsL_right : M + sL + 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        by_cases haM : a = M
        · exact hsL_next_not (by have : b = sL + 1 := by omega; rwa [this] at hb)
        · by_cases hbM : b = M
          · exact hsL_next_not (by have : a = sL + 1 := by omega; rwa [this] at ha)
          · -- a ≤ sL, b ≤ sL → a + b ≤ 2sL < M + sL + 1 (since sL < M)
            linarith [hsL_max a ha haM, hsL_max b hb hbM]
      have hMsL_left : M + sL - 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        by_cases haM : a = M
        · -- b = sL - 1, but sL - 1 ∉ A
          exact hsL_prev_not (by have : b = sL - 1 := by omega; rwa [this] at hb)
        · by_cases hbM : b = M
          · exact hsL_prev_not (by have : a = sL - 1 := by omega; rwa [this] at ha)
          · -- a ≤ sL, b ≤ sL → a + b ≤ 2sL. But a + b = M + sL - 1
            -- → sL ≥ M - 1, contradicting sL ≤ M - 2
            linarith [hsL_max a ha haM, hsL_max b hb hbM]
      -- 2M is also isolated
      have h2M_in : M + M ∈ sumsetFinset A := Finset.add_mem_add hM_mem hM_mem
      have h2M_right : M + M + 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp h
        linarith [Finset.le_max' A a ha, Finset.le_max' A b hb]
      have h2M_left : M + M - 1 ∉ sumsetFinset A := by
        intro h; obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp h
        have ha_le := Finset.le_max' A a ha; have hb_le := Finset.le_max' A b hb
        by_cases ha_eq : a = M
        · exact hM1 (by have : b = M - 1 := by omega; rwa [this] at hb)
        · exact hM1 (by have : a = M - 1 := by omega; rwa [this] at ha)
      -- Two distinct isolated elements → count ≥ 2
      have hne_sums : M + M ≠ M + sL := by omega
      calc isolatedCount A
          = ((sumsetFinset A).filter (fun s =>
              s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A)).card := rfl
        _ ≥ ({M + M, M + sL} : Finset ℕ).card := by
            apply Finset.card_le_card; intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨h2M_in, h2M_left, h2M_right⟩
            · exact Finset.mem_filter.mpr ⟨hMsL_in, hMsL_left, hMsL_right⟩
        _ = 2 := Finset.card_pair hne_sums
    · -- Neither M-1 nor m+1 in A: both endpoints isolated
      exact two_isolated_no_consecutive A hS (by omega) hm_pos hM1 hm1
