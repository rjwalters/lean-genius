/-
  Ballot Problem OQ01 OQ01 OQ02:
  Abstract Cycle Lemma for Arbitrary Integer Sequences

  Source: ballot-problem-oq-01-oq-01-oq-02
  Parent: BallotProblemOQ01OQ01 (Dvoretzky-Motzkin Cycle Lemma for {+1,-k})

  This file extends the cycle lemma infrastructure beyond {+1,-k} sequences,
  identifying which properties of the step alphabet determine cycle lemma behavior.

  Part I: Unit-Decrement Sequences (all steps ≥ -1)
  - Consecutive prefix sums can drop by at most 1 per step.
  - Downward IVT: the prefix sum cannot skip an integer level going downward.
  - Consequence: every level in [minPrefixSum, 0] is achieved by some prefix sum.

  Part II: All-Positive-Step Sequences (all steps > 0)
  - Prefix sums are strictly increasing.
  - Every cyclic rotation is a good rotation.
  - |goodRotations l| = l.length (the maximum possible count).

  Key contrast: for {+1,-k} sequences, |goodRotations| = sum S (proven in
  BallotProblemOQ01.lean). For all-positive sequences, |goodRotations| = length.
  The unit-decrement IVT gives the downward half needed for the {+1,-k} lower bound.

  Status: 0 axioms, 0 sorries
-/

import Proofs.BallotProblemOQ01OQ01
import Mathlib.Tactic

open GeneralizedBallot

namespace BallotAbstractCycleLemma

-- ============================================================================
-- § 1. UNIT-DECREMENT SEQUENCES (all steps ≥ -1)
-- ============================================================================

/-- For sequences with all steps ≥ -1, the prefix sum can drop by at most 1
    per step: prefixSum l (j+1) ≥ prefixSum l j - 1. -/
theorem unit_decrement_step_bound (l : List ℤ)
    (h_step : ∀ x ∈ l, -1 ≤ x)
    (j : ℕ) (hj : j < l.length) :
    prefixSum l j - 1 ≤ prefixSum l (j + 1) := by
  simp only [prefixSum]
  rw [List.sum_take_succ l j hj]
  linarith [h_step l[j] (List.getElem_mem hj)]

/-- **Downward IVT for unit-decrement sequences.**

    For a sequence with all steps ≥ -1: if the prefix sum at position i
    exceeds v but at position j > i it is ≤ v, then some k ∈ (i, j]
    achieves prefix sum exactly v.

    Proof: Let kstar be the leftmost position in (i, j] with prefix sum ≤ v.
    The predecessor kstar - 1 must have prefix sum > v (by minimality).
    Since the step is ≥ -1, the prefix sum can drop by at most 1, so
    prefixSum l kstar ≥ prefixSum l (kstar-1) - 1 > v - 1, giving ≥ v.
    Combined with ≤ v from membership in S: prefixSum l kstar = v. -/
theorem unit_decrement_downward_ivt (l : List ℤ)
    (h_step : ∀ x ∈ l, -1 ≤ x)
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_gt : v < prefixSum l i)
    (hj_le : prefixSum l j ≤ v) :
    ∃ k, i < k ∧ k ≤ j ∧ prefixSum l k = v := by
  -- S = positions in (i, j] with prefix sum ≤ v
  let S := (Finset.Ico (i + 1) (j + 1)).filter (fun k => prefixSum l k ≤ v)
  have hS_ne : S.Nonempty :=
    ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hj_le⟩⟩
  let kstar := S.min' hS_ne
  have hkstar_mem : kstar ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨hkstar_ico, hkstar_le_v⟩ := Finset.mem_filter.mp hkstar_mem
  rw [Finset.mem_Ico] at hkstar_ico
  have hkstar_gt_i : i < kstar := by omega
  have hkstar_le_j : kstar ≤ j := by omega
  -- kstar - 1 has prefix sum > v
  have hpred_gt : v < prefixSum l (kstar - 1) := by
    by_cases heq : kstar = i + 1
    · -- kstar - 1 = i: use hi_gt
      have : kstar - 1 = i := by omega
      rw [this]; exact hi_gt
    · -- kstar - 1 ∈ (i, kstar): use minimality of kstar
      by_contra hle; push_neg at hle
      have hpred_mem : kstar - 1 ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hle⟩
      have := Finset.min'_le S (kstar - 1) hpred_mem
      omega
  -- The step at kstar - 1 is ≥ -1
  have hpred_lt_len : kstar - 1 < l.length := by omega
  have hstep_bound : -1 ≤ l[kstar - 1] :=
    h_step l[kstar - 1] (List.getElem_mem hpred_lt_len)
  -- prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1]
  have hsucc : prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1] := by
    simp only [prefixSum]
    conv_lhs => rw [show kstar = kstar - 1 + 1 from by omega]
    rw [List.sum_take_succ l (kstar - 1) hpred_lt_len]
  -- Conclude: prefixSum l kstar = v
  exact ⟨kstar, hkstar_gt_i, hkstar_le_j, by linarith⟩

/-- For unit-decrement sequences, every integer level in
    [minPrefixSum l, 0] is achieved by some prefix sum position. -/
theorem unit_decrement_levels_achieved (l : List ℤ)
    (h_step : ∀ x ∈ l, -1 ≤ x)
    (v : ℤ) (hlo : minPrefixSum l ≤ v) (hhi : v ≤ 0) :
    ∃ j ≤ l.length, prefixSum l j = v := by
  rcases eq_or_lt_of_le hhi with rfl | hv_neg
  · -- v = 0: position 0 achieves it
    exact ⟨0, Nat.zero_le _, prefixSum_zero l⟩
  · -- v < 0: use downward IVT from position 0 to rightmostMinPos l
    -- rightmostMinPos l achieves minPrefixSum l ≤ v
    have hrmp_le : rightmostMinPos l ≤ l.length := rightmostMinPos_le l
    have hrmp_eq : prefixSum l (rightmostMinPos l) = minPrefixSum l :=
      prefixSum_rightmostMinPos l
    have hrmp_le_v : prefixSum l (rightmostMinPos l) ≤ v := by linarith
    -- rightmostMinPos l > 0 since minPrefixSum l ≤ v < 0 = prefixSum l 0
    have hrmp_pos : 0 < rightmostMinPos l := by
      rcases Nat.eq_or_lt_of_le (Nat.zero_le (rightmostMinPos l)) with h0 | h0
      · rw [← h0, prefixSum_zero] at hrmp_eq; linarith
      · exact h0
    have h0_gt : v < prefixSum l 0 := by rw [prefixSum_zero]; linarith
    obtain ⟨k, hk_pos, hk_le_rmp, hk_eq⟩ :=
      unit_decrement_downward_ivt l h_step v 0 (rightmostMinPos l)
        hrmp_pos hrmp_le h0_gt hrmp_le_v
    exact ⟨k, by omega, hk_eq⟩

-- ============================================================================
-- § 2. ALL-POSITIVE-STEP SEQUENCES (all steps > 0)
-- ============================================================================

/-- For sequences with all steps > 0, each step strictly increases the prefix sum. -/
theorem all_positive_prefixSum_step (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x)
    (j : ℕ) (hj : j < l.length) :
    prefixSum l j < prefixSum l (j + 1) := by
  simp only [prefixSum]
  rw [List.sum_take_succ l j hj]
  linarith [h_step l[j] (List.getElem_mem hj)]

/-- For sequences with all steps > 0, prefix sums are strictly increasing. -/
theorem all_positive_prefixSum_strictMono (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x)
    (i j : ℕ) (hij : i < j) (hj : j ≤ l.length) :
    prefixSum l i < prefixSum l j := by
  induction j with
  | zero => omega
  | succ j' ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hij) with rfl | h
    · exact all_positive_prefixSum_step l h_step i (by omega)
    · exact lt_trans (ih h (by omega)) (all_positive_prefixSum_step l h_step j' (by omega))

/-- For all-positive-step sequences, all prefix sums at interior positions
    are strictly less than the total list sum. -/
theorem all_positive_prefixSum_lt_sum (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x)
    (i : ℕ) (hi : i < l.length) :
    prefixSum l i < l.sum := by
  have := all_positive_prefixSum_strictMono l h_step i l.length hi (le_refl _)
  rwa [prefixSum_length] at this

/-- For all-positive-step sequences, all prefix sums are non-negative. -/
theorem all_positive_prefixSum_nonneg (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x)
    (i : ℕ) :
    0 ≤ prefixSum l i := by
  simp only [prefixSum]
  apply List.sum_nonneg
  intro x hx
  exact le_of_lt (h_step x ((List.take_prefix i l).subset hx))

/-- **All cyclic rotations are good for all-positive-step sequences.**

    When every step is strictly positive, prefix sums are strictly increasing,
    so every cyclic rotation has strictly positive prefix sums throughout:
    - Non-wrapping part: uses strict monotonicity of the original prefix sums.
    - Wrapping part: uses that the starting prefix sum is strictly less than the
      total sum (and that prefix sums of the wrapped portion are non-negative). -/
theorem all_positive_all_rotations_good (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x)
    (i : ℕ) (hi : i < l.length) :
    isGoodRotation l i := by
  intro j hj hjn
  rw [cyclicRotation_prefixSum l i j (le_of_lt hi) hjn]
  split_ifs with hwrap
  · -- Non-wrapping: (l.take (i+j)).sum - (l.take i).sum > 0
    have hmono : prefixSum l i < prefixSum l (i + j) :=
      all_positive_prefixSum_strictMono l h_step i (i + j) (by omega) hwrap
    simp only [prefixSum] at hmono; linarith
  · -- Wrapping: (l.take (i+j-n)).sum + l.sum - (l.take i).sum > 0
    push_neg at hwrap
    have hlt : prefixSum l i < l.sum :=
      all_positive_prefixSum_lt_sum l h_step i hi
    have hnn : 0 ≤ (l.take (i + j - l.length)).sum :=
      List.sum_nonneg (fun x hx =>
        le_of_lt (h_step x ((List.take_prefix (i + j - l.length) l).subset hx)))
    simp only [prefixSum] at hlt; linarith

/-- For all-positive-step sequences, every position is a good rotation, so
    |goodRotations l| = l.length (the maximum possible value). -/
theorem all_positive_goodRotations_card (l : List ℤ)
    (h_step : ∀ x ∈ l, 0 < x) :
    (goodRotations l).card = l.length := by
  have heq : goodRotations l = Finset.range l.length := by
    ext i
    simp only [goodRotations, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨hi, _⟩ => hi,
           fun hi => ⟨hi, all_positive_all_rotations_good l h_step i hi⟩⟩
  rw [heq, Finset.card_range]

end BallotAbstractCycleLemma
