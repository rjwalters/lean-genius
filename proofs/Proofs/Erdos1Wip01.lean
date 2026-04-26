/-
  Erdős Problem #1, WIP-01: Powers of 2 Form a Distinct Subset Sums Set

  This provides the existence basis for Erdős Problem #1 formalization:
  for any n, there exists an n-element set with distinct subset sums.

  The construction is A = {2⁰, 2¹, ..., 2^{n-1}} = image (2^·) (range n).

  Key properties proved:
  1. |A| = n (powers of 2 are distinct)
  2. All elements ≤ n · 2^n (each 2^i < 2^n ≤ n · 2^n for i < n)
  3. A has distinct subset sums (binary representation uniqueness)

  The binary uniqueness proof is by strong induction on n: either both
  subsets S, T contain the largest element 2^{n-1}, or neither does.
  In both cases, subtracting 2^{n-1} from both sides (or leaving as-is)
  reduces to a smaller instance by the IH.

  This fills the sorry in Erdos1OQ03.lean that was blocking the definition
  of `minDSSBound` (the well-definedness of the minimum DSS bound function).

  Status: VERIFIED — 0 sorries, 0 axioms
  Tags: erdos, additive-combinatorics, distinct-subset-sums, powers-of-two
-/

import Proofs.Erdos1Problem
import Mathlib

open Finset

namespace Erdos1Wip01

-- ════════════════════════════════════════════════════════════════
-- PART I: Auxiliary Lemmas for Binary Injectivity
-- ════════════════════════════════════════════════════════════════

/-- Geometric sum: ∑_{i < n} 2^i + 1 = 2^n. -/
private lemma geom_sum_pow2 (n : ℕ) :
    (Finset.range n).sum (fun i : ℕ => 2 ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ, two_mul]; omega

/-- Any subset of {0,...,n-1} has power-of-2 sum < 2^n. -/
private lemma sum_pow2_lt_of_subset_range (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range n) :
    S.sum (fun i : ℕ => 2 ^ i) < 2 ^ n := by
  have h1 : S.sum (fun i : ℕ => 2 ^ i) ≤ (Finset.range n).sum (fun i : ℕ => 2 ^ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  linarith [geom_sum_pow2 n]

/-- If S ⊆ range (n+1) and n ∉ S, then S ⊆ range n. -/
private lemma subset_range_pred {S : Finset ℕ} {n : ℕ}
    (hS : S ⊆ Finset.range (n + 1)) (hn : n ∉ S) : S ⊆ Finset.range n := by
  intro x hx
  have hlt : x < n + 1 := Finset.mem_range.mp (hS hx)
  have hne : x ≠ n := fun h => hn (h ▸ hx)
  exact Finset.mem_range.mpr (by omega)

/-- **Binary Representation Uniqueness**: subsets of {0,...,n-1} with equal
    power-of-2 sums are identical.

    Proof by induction on n: consider whether n-1 belongs to each subset.
    The key bound: sum of any subset of {0,...,n-1} is < 2^n, so
    if one subset contains n-1 and the other doesn't, their sums differ. -/
private lemma pow2_sum_inj (n : ℕ) (S T : Finset ℕ)
    (hS : S ⊆ Finset.range n) (hT : T ⊆ Finset.range n)
    (heq : S.sum (fun i : ℕ => 2 ^ i) = T.sum (fun i : ℕ => 2 ^ i)) :
    S = T := by
  induction n generalizing S T with
  | zero =>
    rw [Finset.range_zero] at hS hT
    rw [Finset.subset_empty.mp hS, Finset.subset_empty.mp hT]
  | succ n ih =>
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: erase n from both sides and apply IH
      have hSe : S.erase n ⊆ Finset.range n :=
        subset_range_pred ((Finset.erase_subset n S).trans hS) (Finset.not_mem_erase n S)
      have hTe : T.erase n ⊆ Finset.range n :=
        subset_range_pred ((Finset.erase_subset n T).trans hT) (Finset.not_mem_erase n T)
      have hSeq : S.sum (fun i : ℕ => 2 ^ i) =
                  2 ^ n + (S.erase n).sum (fun i : ℕ => 2 ^ i) :=
        (Finset.add_sum_erase S _ hnS).symm
      have hTeq : T.sum (fun i : ℕ => 2 ^ i) =
                  2 ^ n + (T.erase n).sum (fun i : ℕ => 2 ^ i) :=
        (Finset.add_sum_erase T _ hnT).symm
      have heq' : (S.erase n).sum (fun i : ℕ => 2 ^ i) =
                  (T.erase n).sum (fun i : ℕ => 2 ^ i) := by omega
      rw [← Finset.insert_erase hnS, ← Finset.insert_erase hnT, ih _ _ hSe hTe heq']
    · -- n ∈ S, n ∉ T: sum(S) ≥ 2^n > sum(T), contradiction
      exfalso
      have hSge : (2 : ℕ) ^ n ≤ S.sum (fun i : ℕ => 2 ^ i) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnS
      have hTlt : T.sum (fun i : ℕ => 2 ^ i) < 2 ^ n :=
        sum_pow2_lt_of_subset_range n T (subset_range_pred hT hnT)
      omega
    · -- n ∉ S, n ∈ T: symmetric
      exfalso
      have hTge : (2 : ℕ) ^ n ≤ T.sum (fun i : ℕ => 2 ^ i) :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hnT
      have hSlt : S.sum (fun i : ℕ => 2 ^ i) < 2 ^ n :=
        sum_pow2_lt_of_subset_range n S (subset_range_pred hS hnS)
      omega
    · -- Neither contains n: restrict to range n, apply IH
      exact ih _ _ (subset_range_pred hS hnS) (subset_range_pred hT hnT) heq

-- ════════════════════════════════════════════════════════════════
-- PART II: The DSS Property of {2^i : i < n}
-- ════════════════════════════════════════════════════════════════

/-- The set {2^0, 2^1, ..., 2^{n-1}} has distinct subset sums.

    Proof: Given S, T ⊆ A with S.sum id = T.sum id, let S', T' be the
    "index preimages" (subsets of {0,...,n-1} with S = S'.image (2^·)).
    Then S.sum id = S'.sum (2^·) by sum_image. Apply binary uniqueness
    to conclude S' = T', hence S = T. -/
theorem powersOfTwo_hasDistinctSubsetSums (n : ℕ) :
    hasDistinctSubsetSums ((Finset.range n).image (fun i => (2 : ℕ) ^ i)) := by
  intro S T hS hT heq
  -- Index sets: S' = preimage of S in {0,...,n-1}
  set S' := (Finset.range n).filter (fun i => (2 : ℕ) ^ i ∈ S) with hS'_def
  set T' := (Finset.range n).filter (fun i => (2 : ℕ) ^ i ∈ T) with hT'_def
  have hS'_sub : S' ⊆ Finset.range n := Finset.filter_subset _ _
  have hT'_sub : T' ⊆ Finset.range n := Finset.filter_subset _ _
  -- S = image of S' under (2^·)
  have hS_eq : S = S'.image (fun i => (2 : ℕ) ^ i) := by
    ext x; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, S']
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hS hx)
      exact ⟨i, ⟨Finset.mem_range.mp hi, hx⟩, rfl⟩
    · rintro ⟨i, ⟨_, hx⟩, rfl⟩; exact hx
  have hT_eq : T = T'.image (fun i => (2 : ℕ) ^ i) := by
    ext x; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, T']
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hT hx)
      exact ⟨i, ⟨Finset.mem_range.mp hi, hx⟩, rfl⟩
    · rintro ⟨i, ⟨_, hx⟩, rfl⟩; exact hx
  -- Injectivity of (2^·) on range n
  have pow2_inj : ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n,
      (2 : ℕ) ^ a = 2 ^ b → a = b :=
    fun _ _ _ _ h => Nat.pow_right_injective (by norm_num : 1 < 2) h
  -- Convert sums: S.sum id = S'.sum (2^·)
  have hS_sum : S.sum id = S'.sum (fun i => (2 : ℕ) ^ i) := by
    conv_lhs => rw [hS_eq]
    exact Finset.sum_image (fun a ha b hb h => pow2_inj a (hS'_sub ha) b (hS'_sub hb) h)
  have hT_sum : T.sum id = T'.sum (fun i => (2 : ℕ) ^ i) := by
    conv_lhs => rw [hT_eq]
    exact Finset.sum_image (fun a ha b hb h => pow2_inj a (hT'_sub ha) b (hT'_sub hb) h)
  -- S'.sum (2^·) = T'.sum (2^·)
  have heq_idx : S'.sum (fun i => (2 : ℕ) ^ i) = T'.sum (fun i => (2 : ℕ) ^ i) :=
    hS_sum.symm.trans (heq.trans hT_sum)
  -- Apply binary uniqueness: S' = T', hence S = T
  have hS'T' : S' = T' := pow2_sum_inj n S' T' hS'_sub hT'_sub heq_idx
  rw [hS_eq, hT_eq, hS'T']

-- ════════════════════════════════════════════════════════════════
-- PART III: Existence of n-Element DSS Sets (Main Theorem)
-- ════════════════════════════════════════════════════════════════

/-- **DSSExistence**: For any n, there exists an n-element set of naturals,
    all bounded by n · 2^n, with distinct subset sums.

    Construction: A = {1, 2, 4, ..., 2^{n-1}} = image (2^·) (range n).

    This fills the sorry in `Erdos1OQ03.lean` that was needed to make
    `minDSSBound` well-defined via `Nat.find`. -/
theorem dss_existence (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ n * 2 ^ n) ∧
    hasDistinctSubsetSums A := by
  refine ⟨(Finset.range n).image (fun i => (2 : ℕ) ^ i), ?_, ?_, ?_⟩
  · -- Card = n (injectivity of 2^·)
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num : 1 < 2)),
        Finset.card_range]
  · -- All elements ≤ n · 2^n
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi_lt : i < n := Finset.mem_range.mp hi
    have hn_pos : 0 < n := by omega
    have h1 : (2 : ℕ) ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hi_lt
    have h2 : (2 : ℕ) ^ n ≤ n * 2 ^ n := Nat.le_mul_of_pos_left _ hn_pos
    linarith
  · -- Distinct subset sums
    exact powersOfTwo_hasDistinctSubsetSums n

end Erdos1Wip01
