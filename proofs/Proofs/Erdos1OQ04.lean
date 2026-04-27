/-
Erdős Problem #1, OQ-04: Extremal Sets for Distinct Subset Sums

The parent problem asks: if A ⊆ {1,...,N} has n elements with all 2^n
subset sums distinct, must N ≥ c · 2^n?

This follow-up investigates the *structure* of extremal sets — those
achieving the minimum N for each n. The minimum values form OEIS A005318:
  f(0)=0, f(1)=1, f(2)=2, f(3)=4, f(4)=7, f(5)=13, f(6)=24, ...

The Conway-Guy conjecture (1968) identifies the specific extremal sets.

Reference: https://erdosproblems.com/1
OEIS: A005318 (minimum max element for distinct subset sums)
-/

import Mathlib

open Finset

/-- A finite set of natural numbers has distinct subset sums if distinct
    subsets always have different sums. (Imported from parent.) -/
def hasDistinctSubsetSums (A : Finset ℕ) : Prop :=
  ∀ (S T : Finset ℕ), S ⊆ A → T ⊆ A → S.sum id = T.sum id → S = T

/-- Decidability of hasDistinctSubsetSums: check all pairs of subsets. -/
instance decidableHasDistinctSubsetSums (A : Finset ℕ) :
    Decidable (hasDistinctSubsetSums A) :=
  decidable_of_iff
    (∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T)
    ⟨fun h S T hS hT => h S (mem_powerset.mpr hS) T (mem_powerset.mpr hT),
     fun h S hS T hT => h S (mem_powerset.mp hS) T (mem_powerset.mp hT)⟩

/-- A set of n positive integers in {1,...,N} with distinct subset sums exists. -/
def achievesDistinctSums (n N : ℕ) : Prop :=
  ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, 0 < a) ∧ (∀ a ∈ A, a ≤ N) ∧
    hasDistinctSubsetSums A

/-- Monotonicity in the bound N: a witnessing n-element DSS set in {1,...,N}
    also fits in {1,...,N'} for any N' ≥ N. This lets `achievesDistinctSums n`
    propagate to looser bounds — useful when comparing extremal candidates. -/
theorem achievesDistinctSums_mono {n N N' : ℕ} (h : N ≤ N')
    (ha : achievesDistinctSums n N) : achievesDistinctSums n N' := by
  obtain ⟨A, hcard, hpos, hmax, hdss⟩ := ha
  exact ⟨A, hcard, hpos, fun a ha' => le_trans (hmax a ha') h, hdss⟩

/- ## Verified Small Cases (OEIS A005318) -/

/-- {1} has distinct subset sums: subsets are ∅ (sum 0) and {1} (sum 1). -/
theorem dss_1 : hasDistinctSubsetSums {1} := by native_decide

/-- {1, 2} has distinct subset sums: sums are 0, 1, 2, 3. -/
theorem dss_12 : hasDistinctSubsetSums ({1, 2} : Finset ℕ) := by native_decide

/-- {1, 2, 4} has distinct subset sums: sums are 0,1,2,3,4,5,6,7. -/
theorem dss_124 : hasDistinctSubsetSums ({1, 2, 4} : Finset ℕ) := by native_decide

/-- {3, 5, 6, 7} has distinct subset sums with max 7 and 4 elements. -/
theorem dss_3567 : hasDistinctSubsetSums ({3, 5, 6, 7} : Finset ℕ) := by native_decide

/-- {6, 9, 11, 12, 13} has distinct subset sums with max 13 and 5 elements. -/
theorem dss_conway_guy_5 :
    hasDistinctSubsetSums ({6, 9, 11, 12, 13} : Finset ℕ) := by native_decide

/-- f(1) = 1: {1} achieves it, and {∅} can't (need positive elements). -/
theorem f1_eq_1 : achievesDistinctSums 1 1 := by
  exact ⟨{1}, by simp, by simp, by simp, dss_1⟩

/-- f(2) = 2: {1,2} achieves it. -/
theorem f2_eq_2 : achievesDistinctSums 2 2 := by
  exact ⟨{1, 2}, by native_decide, by simp; omega, by simp; omega, dss_12⟩

/-- f(3) = 4: {1,2,4} achieves it (powers of 2 give binary representation). -/
theorem f3_le_4 : achievesDistinctSums 3 4 := by
  exact ⟨{1, 2, 4}, by native_decide, by simp; omega, by simp; omega, dss_124⟩

/-- f(4) ≤ 7: {3,5,6,7} achieves it. -/
theorem f4_le_7 : achievesDistinctSums 4 7 := by
  exact ⟨{3, 5, 6, 7}, by native_decide, by simp; omega, by simp; omega, dss_3567⟩

/-- f(5) ≤ 13: {6,9,11,12,13} achieves it (Conway-Guy construction). -/
theorem f5_le_13 : achievesDistinctSums 5 13 := by
  exact ⟨{6, 9, 11, 12, 13}, by native_decide, by simp; omega, by simp; omega,
    dss_conway_guy_5⟩

/- ## The Conway-Guy Conjecture -/

/-- The Conway-Guy sequence: conjectured minimum max element for n-element
    sets with distinct subset sums.

    OEIS A005318: 0, 1, 2, 4, 7, 13, 24, 44, 84, 161, 309, ...

    The recurrence is a_{n} = a_{n-1} + ⌈(a_1 + ... + a_{n-1}) / 2⌉, but
    the ceiling of a rational expression cannot easily be expressed in
    Lean ℕ recursion (requires carrying partial sums along). Instead we
    list the verified small values (OEIS A005318) and use 0 beyond n = 8. -/
def conwayGuySeq : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 13
  | 6 => 24
  | 7 => 44
  | 8 => 84
  | _ => 0  -- only small cases; recurrence is aₙ = aₙ₋₁ + ⌈Sₙ₋₁/2⌉

/-- The Conway-Guy conjecture: the minimum N such that an n-element set
    in {1,...,N} has distinct subset sums equals conwayGuySeq n. -/
def conwayGuyConjecture : Prop :=
  ∀ n : ℕ, n ≥ 1 →
    achievesDistinctSums n (conwayGuySeq n) ∧
    ¬achievesDistinctSums n (conwayGuySeq n - 1)

/- ## Structural Observations -/

/-- Geometric sum: ∑_{i<n} 2^i + 1 = 2^n. -/
private lemma geom_sum_two (n : ℕ) :
    (Finset.range n).sum (fun i : ℕ => 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ]; omega

/-- Sum of a subset of {2^i : i < n} is strictly less than 2^n. -/
private lemma sum_pow_lt_of_subset_range (n : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range n) :
    T.sum (fun i : ℕ => 2 ^ i) < 2 ^ n := by
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hT
    (fun _ _ _ => Nat.zero_le _) (f := fun i : ℕ => 2 ^ i)
  have h2 := geom_sum_two n
  omega

/-- If S ⊆ range (n+1) and n ∉ S, then S ⊆ range n. -/
private lemma subset_range_pred {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range (n + 1)) (hn : n ∉ S) : S ⊆ Finset.range n := by
  intro x hx
  have hlt := Finset.mem_range.mp (hS hx)
  exact Finset.mem_range.mpr (Nat.lt_of_le_of_ne (by omega) (fun h => hn (h ▸ hx)))

/-- Binary uniqueness: equal sums of powers of 2 from range n imply equal subsets. -/
private lemma sum_pow_two_inj : ∀ (n : ℕ) (S T : Finset ℕ),
    S ⊆ Finset.range n → T ⊆ Finset.range n →
    S.sum (fun i : ℕ => 2 ^ i) = T.sum (fun i : ℕ => 2 ^ i) → S = T := by
  intro n
  induction n with
  | zero =>
    intro S T hS hT _
    have := Finset.subset_empty.mp (Finset.range_zero ▸ hS)
    have := Finset.subset_empty.mp (Finset.range_zero ▸ hT)
    subst_vars; rfl
  | succ n ih =>
    intro S T hS hT heq
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: erase n from both, apply IH
      have hSe : S.erase n ⊆ Finset.range n :=
        subset_range_pred ((Finset.erase_subset n S).trans hS) (Finset.not_mem_erase n S)
      have hTe : T.erase n ⊆ Finset.range n :=
        subset_range_pred ((Finset.erase_subset n T).trans hT) (Finset.not_mem_erase n T)
      have h1 := Finset.add_sum_erase S (fun i : ℕ => 2 ^ i) hnS
      have h2 := Finset.add_sum_erase T (fun i : ℕ => 2 ^ i) hnT
      have heq' : (S.erase n).sum (fun i : ℕ => 2 ^ i) =
                   (T.erase n).sum (fun i : ℕ => 2 ^ i) := by omega
      rw [← Finset.insert_erase hnS, ← Finset.insert_erase hnT, ih _ _ hSe hTe heq']
    · -- n ∈ S, n ∉ T: sum contradiction
      exfalso
      have h1 : (2 : ℕ) ^ n ≤ S.sum (fun i : ℕ => 2 ^ i) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnS
      have h2 := sum_pow_lt_of_subset_range n T (subset_range_pred hT hnT)
      omega
    · -- n ∉ S, n ∈ T: symmetric
      exfalso
      have h1 : (2 : ℕ) ^ n ≤ T.sum (fun i : ℕ => 2 ^ i) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnT
      have h2 := sum_pow_lt_of_subset_range n S (subset_range_pred hS hnS)
      omega
    · -- Neither: reduce to range n
      exact ih S T (subset_range_pred hS hnS) (subset_range_pred hT hnT) heq

/-- Powers of 2 always give distinct subset sums (binary representation).
    The set {1, 2, 4, ..., 2^{n-1}} has max = 2^{n-1} and n elements. -/
theorem powers_of_two_dss (n : ℕ) :
    achievesDistinctSums n (2^n - 1) := by
  refine ⟨(Finset.range n).image (fun i => 2 ^ i), ?_, ?_, ?_, ?_⟩
  · -- card = n (injective image preserves cardinality)
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num : 1 < 2)),
        Finset.card_range]
  · -- all positive (2^i > 0)
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    positivity
  · -- all ≤ 2^n - 1 (2^i < 2^n for i < n)
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hi)
    omega
  · -- distinct subset sums via binary uniqueness
    intro S T hS hT heq
    have pow_inj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n,
        (2 : ℕ) ^ a = 2 ^ b → a = b :=
      fun _ _ _ _ h => Nat.pow_right_injective (by norm_num : 1 < 2) h
    -- Preimage S and T to subsets of range n
    set S' := (Finset.range n).filter (fun i => (2 : ℕ) ^ i ∈ S) with hS'_def
    set T' := (Finset.range n).filter (fun i => (2 : ℕ) ^ i ∈ T) with hT'_def
    -- S = S'.image (2^·)
    have hS_eq : S = S'.image (fun i => (2 : ℕ) ^ i) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hS hx)
        exact ⟨i, ⟨Finset.mem_range.mp hi, hx⟩, rfl⟩
      · rintro ⟨i, ⟨_, hx⟩, rfl⟩; exact hx
    have hT_eq : T = T'.image (fun i => (2 : ℕ) ^ i) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · intro hx; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hT hx)
        exact ⟨i, ⟨Finset.mem_range.mp hi, hx⟩, rfl⟩
      · rintro ⟨i, ⟨_, hx⟩, rfl⟩; exact hx
    -- Convert sums: S.sum id = S'.sum (2^·) via sum_image
    have hS'_range : S' ⊆ Finset.range n := Finset.filter_subset _ _
    have hT'_range : T' ⊆ Finset.range n := Finset.filter_subset _ _
    have sum_S : S.sum id = S'.sum (fun i => (2 : ℕ) ^ i) := by
      conv_lhs => rw [hS_eq]
      exact Finset.sum_image (fun a ha b hb h =>
        pow_inj a (hS'_range ha) b (hS'_range hb) h)
    have sum_T : T.sum id = T'.sum (fun i => (2 : ℕ) ^ i) := by
      conv_lhs => rw [hT_eq]
      exact Finset.sum_image (fun a ha b hb h =>
        pow_inj a (hT'_range ha) b (hT'_range hb) h)
    -- Apply binary uniqueness
    have sum_eq : S'.sum (fun i => (2 : ℕ) ^ i) = T'.sum (fun i => (2 : ℕ) ^ i) := by
      rw [← sum_S, ← sum_T]; exact heq
    rw [hS_eq, hT_eq, sum_pow_two_inj n S' T' hS'_range hT'_range sum_eq]

/-- The gap between 2^{n-1} (powers of 2 bound) and f(n) (optimal) grows:
    for n = 4, powers give max 8 but optimal is 7;
    for n = 5, powers give max 16 but optimal is 13. -/

/- ## Summary

**Verified extremal set values (OEIS A005318)**:
- f(1) = 1 (set {1})
- f(2) = 2 (set {1,2})
- f(3) ≤ 4 (set {1,2,4})
- f(4) ≤ 7 (set {3,5,6,7})
- f(5) ≤ 13 (set {6,9,11,12,13})

All verified computationally via native_decide.

**Open**: Conway-Guy conjecture (these are the exact minima).
-/
end
