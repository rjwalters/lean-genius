/-
  Erdős Problem #1 — WIP Extension: Structural Theory

  This file extends the Erdős #1 gallery with structural results that were
  missing from the OQ01–OQ04 files:

  1. **Superincreasing extension lemma**: if A has DSS and b > sum(A),
     then (insert b A) has DSS. This is the combinatorial core underlying
     the powers-of-2 construction.

  2. **Powers-of-2 DSS**: {1, 2, 4, …, 2^(n−1)} has distinct subset sums
     for any n, proved by induction using the superincreasing lemma.

  3. **DSS existence for any n**: For every n there exists a set of n
     positive integers with distinct subset sums. This fills the sorry in
     OQ03's `minDSSBound` definition.

  4. **Positivity of elements**: A set has DSS only if all its elements are
     positive (otherwise ∅ and {0} have the same sum 0).

  5. **Counting lower bound via element sum**: sum(A) ≥ 2^n − 1 for any
     n-element DSS set, proved directly from injectivity (strengthens
     the per-element bound to a global one).

  References:
  - Erdős (1955): Problems in additive number theory
  - Dubroff, Fox, Xu (2021): Best known lower bound
  - Conway, Guy (1968): Upper bound construction
  - OEIS A005318: f(n) = minimum max element of DSS set of size n
-/

import Proofs.Erdos1Problem
import Mathlib

open Finset

namespace Erdos1WIP

/-! ═══════════════════════════════════════════════════════════════════════════
PART I: SUPERINCREASING EXTENSION LEMMA

The key structural result: appending an element larger than the entire sum
preserves the distinct-subset-sums property.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Superincreasing Extension Lemma**: If `A` has distinct subset sums and
    `b > sum(A)`, then `insert b A` also has distinct subset sums.

    Proof by case analysis on whether `b` belongs to each of the two subsets.
    The key observation: any subset of `insert b A` that contains `b` has
    sum ≥ b > `sum(A)`, while any subset not containing `b` has sum ≤ `sum(A)`.
    So the two cases (contains `b` vs. doesn't) are sum-disjoint, and within
    each case DSS follows from DSS of `A`. -/
theorem dss_superincreasing_extend {A : Finset ℕ}
    (hDSS : hasDistinctSubsetSums A)
    {b : ℕ} (hb : A.sum id < b) (hbA : b ∉ A) :
    hasDistinctSubsetSums (insert b A) := by
  intro S T hS hT heq
  by_cases hbS : b ∈ S <;> by_cases hbT : b ∈ T
  · -- Case: b ∈ S and b ∈ T. Erase b from both and apply DSS of A.
    have hSe_sub : S.erase b ⊆ A := by
      intro x hx
      have hxne : x ≠ b := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase hx)) with rfl | hxA
      · exact absurd rfl hxne
      · exact hxA
    have hTe_sub : T.erase b ⊆ A := by
      intro x hx
      have hxne : x ≠ b := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx)) with rfl | hxA
      · exact absurd rfl hxne
      · exact hxA
    -- After erasing b, the sums are still equal.
    have hsum_erase : (S.erase b).sum id = (T.erase b).sum id := by
      have hS' := Finset.add_sum_erase S id hbS
      have hT' := Finset.add_sum_erase T id hbT
      have h1 : id b + (S.erase b).sum id = id b + (T.erase b).sum id :=
        hS'.trans (heq.trans hT'.symm)
      exact Nat.add_left_cancel h1
    -- By DSS of A, the erased sets are equal; reinsert b.
    have herase_eq := hDSS _ _ hSe_sub hTe_sub hsum_erase
    rw [← Finset.insert_erase hbS, ← Finset.insert_erase hbT, herase_eq]
  · -- Case: b ∈ S but b ∉ T. Contradiction since sum(S) > sum(A) ≥ sum(T).
    exfalso
    have hT_sub : T ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with rfl | hxA
      · exact absurd hx hbT
      · exact hxA
    have hb_le_S : b ≤ S.sum id :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hbS
    have hT_le : T.sum id ≤ A.sum id :=
      Finset.sum_le_sum_of_subset_of_nonneg hT_sub (fun _ _ _ => Nat.zero_le _)
    linarith [heq]
  · -- Case: b ∉ S but b ∈ T. Symmetric contradiction.
    exfalso
    have hS_sub : S ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with rfl | hxA
      · exact absurd hx hbS
      · exact hxA
    have hb_le_T : b ≤ T.sum id :=
      Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _) hbT
    have hS_le : S.sum id ≤ A.sum id :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ => Nat.zero_le _)
    linarith [heq]
  · -- Case: b ∉ S and b ∉ T. Both subsets lie in A; apply DSS of A directly.
    have hS_sub : S ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with rfl | hxA
      · exact absurd hx hbS
      · exact hxA
    have hT_sub : T ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with rfl | hxA
      · exact absurd hx hbT
      · exact hxA
    exact hDSS S T hS_sub hT_sub heq

/-! ═══════════════════════════════════════════════════════════════════════════
PART II: GEOMETRIC SUM BOUND

We need: ∑_{i<n} 2^i < 2^n (to verify the superincreasing property for
powers of 2).
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Geometric sum**: ∑_{i<n} 2^i + 1 = 2^n. -/
private lemma sum_two_pow_range_add_one (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

/-- **Strict bound**: ∑_{i<n} 2^i < 2^n. -/
lemma sum_two_pow_lt (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) < 2 ^ n := by
  linarith [sum_two_pow_range_add_one n]

/-! ═══════════════════════════════════════════════════════════════════════════
PART III: POWERS OF 2 GIVE DISTINCT SUBSET SUMS

The set {1, 2, 4, …, 2^(n−1)} has distinct subset sums.
Proved by induction using `dss_superincreasing_extend`.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Powers-of-2 set has DSS**: The set `{2^0, 2^1, …, 2^(n-1)}` has distinct
    subset sums for any `n`.

    Proof by induction on `n`:
    - Base: the empty set trivially has DSS.
    - Step: the set for `n+1` is `{2^0, …, 2^(n-1)} ∪ {2^n}`. Since
      `2^n > ∑_{i<n} 2^i` (by `sum_two_pow_lt`), we apply
      `dss_superincreasing_extend` to the induction hypothesis. -/
theorem powers_of_two_has_dss (n : ℕ) :
    hasDistinctSubsetSums ((Finset.range n).image (2 ^ · : ℕ → ℕ)) := by
  induction n with
  | zero =>
    simp [hasDistinctSubsetSums, Finset.subset_empty]
  | succ n ih =>
    rw [Finset.range_succ, Finset.image_insert]
    apply dss_superincreasing_extend ih
    · -- 2^n > sum({2^0,...,2^(n-1)})
      have hsum : ((Finset.range n).image (2 ^ · : ℕ → ℕ)).sum id =
          ∑ i ∈ Finset.range n, (2 : ℕ) ^ i := by
        apply Finset.sum_image
        intro i hi j hj heq
        exact Nat.pow_right_injective (by norm_num : 1 < 2) heq
      rw [hsum]
      exact sum_two_pow_lt n
    · -- 2^n ∉ {2^0,...,2^(n-1)}
      simp only [Finset.mem_image, Finset.mem_range]
      push_neg
      intro i hi
      exact Nat.ne_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hi)

/-! ═══════════════════════════════════════════════════════════════════════════
PART IV: DSS EXISTENCE FOR ANY N

For every n, we can construct an n-element set with distinct subset sums.
This fills the existential gap in OQ03's `minDSSBound`.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **DSS existence**: For every `n`, there exists an `n`-element set of natural
    numbers with distinct subset sums, all bounded by `n * 2^n`.

    Construction: take `A = {2^0, 2^1, …, 2^(n-1)}`.
    - Cardinality `n`: the map `i ↦ 2^i` is injective on `{0,...,n-1}`.
    - Bounded by `n * 2^n`: max element is `2^(n-1) ≤ 2^n ≤ n * 2^n`.
    - DSS: proved by `powers_of_two_has_dss`. -/
theorem dss_exists (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ n * 2 ^ n) ∧
      hasDistinctSubsetSums A := by
  use (Finset.range n).image (2 ^ · : ℕ → ℕ)
  refine ⟨?_, ?_, powers_of_two_has_dss n⟩
  · -- Cardinality: 2^· is injective on ℕ
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num : 1 < 2))]
    simp
  · -- All elements ≤ n * 2^n
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range] at hi
    -- 2^i < 2^n (since i < n), and 2^n ≤ n * 2^n (since n ≥ 1)
    have h1 : (2 : ℕ) ^ i ≤ 2 ^ n := by
      apply Nat.pow_le_pow_right; norm_num; omega
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hi
    · linarith [Nat.le_mul_of_pos_left (2 ^ n) hn]

/-- **Positive DSS existence**: For any `n`, there exists an `n`-element DSS set
    of positive integers with max element `≤ 2^n - 1`. -/
theorem dss_positive_exists (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, 0 < a) ∧ (∀ a ∈ A, a ≤ 2 ^ n) ∧
      hasDistinctSubsetSums A := by
  use (Finset.range n).image (2 ^ · : ℕ → ℕ)
  refine ⟨?_, ?_, ?_, powers_of_two_has_dss n⟩
  · rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num : 1 < 2))]
    simp
  · intro a ha
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp ha
    positivity
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_range] at hi
    exact Nat.le_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hi)

/-! ═══════════════════════════════════════════════════════════════════════════
PART V: STRUCTURAL PROPERTIES OF DSS SETS

Elementary structural constraints forced by the DSS property.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **0 prevents DSS**: If `0 ∈ A`, then `A` does NOT have distinct subset sums.
    Proof: `∅` and `{0}` are distinct subsets of `A`, both with sum 0. -/
theorem not_dss_of_mem_zero {A : Finset ℕ} (h0 : 0 ∈ A) :
    ¬ hasDistinctSubsetSums A := by
  intro hDSS
  have h := hDSS ∅ {0} (Finset.empty_subset A) (Finset.singleton_subset_iff.mpr h0)
  simp at h

/-- **Positivity from DSS**: If `A` has distinct subset sums, all elements of `A`
    are positive. (Otherwise, `0 ∈ A` would make ∅ and {0} have equal sums.) -/
theorem dss_elements_pos {A : Finset ℕ}
    (hDSS : hasDistinctSubsetSums A) : ∀ a ∈ A, 0 < a := by
  intro a ha
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · exact absurd hDSS (not_dss_of_mem_zero ha)
  · exact hpos

/-- **Monotone subset property**: Any subset of a DSS set also has DSS. -/
theorem dss_subset {A B : Finset ℕ} (hDSS : hasDistinctSubsetSums A) (hBA : B ⊆ A) :
    hasDistinctSubsetSums B :=
  fun S T hS hT heq => hDSS S T (hS.trans hBA) (hT.trans hBA) heq

/-- **Singleton DSS**: Any singleton {a} has distinct subset sums. -/
/- Note: `dss_singleton a` requires `a > 0`. If `a = 0`, then `∅` and `{0}` are
   distinct subsets of `{0}` both with sum 0. -/
theorem dss_singleton {a : ℕ} (ha : 0 < a) : hasDistinctSubsetSums ({a} : Finset ℕ) := by
  intro S T hS hT heq
  rw [Finset.subset_singleton_iff] at hS hT
  rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
  · rfl
  · simp at heq; omega
  · simp at heq; omega
  · rfl

/-! ═══════════════════════════════════════════════════════════════════════════
PART VI: SUM LOWER BOUND

For any n-element DSS set, the total sum is at least 2^n − 1.
This is stronger than the max-element lower bound.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Sum lower bound**: If `A` has `n` elements and distinct subset sums,
    then `sum(A) + 1 ≥ 2^n`.

    Proof: The 2^n subsets of `A` have distinct sums by injectivity, all
    lying in `{0, …, sum(A)}`. By pigeonhole, `2^n ≤ sum(A) + 1`. -/
theorem dss_sum_lower_bound {A : Finset ℕ} (hDSS : hasDistinctSubsetSums A) :
    2 ^ A.card ≤ A.sum id + 1 := by
  -- The subset-sum map is injective on the powerset
  have hinj : Set.InjOn (fun S : Finset ℕ => S.sum id)
      (↑A.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
    exact hDSS S T hS hT heq
  -- The image has size 2^n
  have himg_card : (A.powerset.image (·.sum id)).card = 2 ^ A.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset]
  -- All sums are in {0, …, sum(A)}
  have himg_sub : A.powerset.image (·.sum id) ⊆ Finset.range (A.sum id + 1) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨S, hS, rfl⟩ := hx
    rw [Finset.mem_powerset] at hS
    rw [Finset.mem_range]
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := id) hS (fun _ _ _ => Nat.zero_le _)
    linarith
  calc 2 ^ A.card
    = (A.powerset.image (·.sum id)).card := himg_card.symm
    _ ≤ (Finset.range (A.sum id + 1)).card := Finset.card_le_card himg_sub
    _ = A.sum id + 1 := Finset.card_range _

/-- **Corollary**: The total sum of an `n`-element DSS set is at least `2^n − 1`.
    (The counting bound `n · max(A) ≥ 2^n − 1` follows since `sum(A) ≤ n · max(A)`.) -/
theorem dss_sum_ge_pow_sub_one {A : Finset ℕ} (hDSS : hasDistinctSubsetSums A) :
    2 ^ A.card - 1 ≤ A.sum id := by
  have h := dss_sum_lower_bound hDSS
  omega

/-! ═══════════════════════════════════════════════════════════════════════════
PART VII: CONNECTION TO MINDSSBOUNDQ (OQ03 FIX)

We provide the clean existence witness for the `minDSSBound` definition in
OQ03.lean, which uses `Nat.find` with an existential that previously had a
sorry.
═══════════════════════════════════════════════════════════════════════════ -/

/-- **Existence witness for minDSSBound** (OQ03 fix): For any `n`, there exists
    `N` and an `n`-element DSS set bounded by `N`. This is the existential
    witness that was previously left as a `sorry` in OQ03. -/
theorem minDSS_witness (n : ℕ) :
    ∃ N : ℕ, ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ N) ∧
      hasDistinctSubsetSums A :=
  ⟨n * 2 ^ n, dss_exists n⟩

end Erdos1WIP
