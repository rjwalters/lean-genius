/-
  Ballot Problem OQ01 OQ01 OQ02 OQ01:
  m-Jump Downward IVT (generalization of the unit-decrement IVT)

  Source: ballot-problem-oq-01-oq-01-oq-02-oq-01
  Parent: BallotProblemOQ01OQ01OQ02 (Abstract Cycle Lemma — unit-decrement
          + all-positive cases)

  S1 OBSERVE refuted the parent meta's `openQuestions[0]` conjecture
  `(step ≥ -m) ∧ (S > 0) → ⌈S/m⌉ ≤ |goodRotations|` by exhibiting
  `l = [-m, m + S]` with `|goodRotations| = 1 < ⌈S/m⌉` for any `m ≥ 2`,
  `S = m + 1`.

  This file (S2 ACT) formalizes **conjecture D** from the S1 OBSERVE: the
  m-jump downward IVT — the genuine m-generalization of the parent's
  `unit_decrement_downward_ivt`. At `m = 1` the conclusion window
  `[v - m + 1, v]` collapses to `{v}` and the parent statement is recovered.

  The proof template transfers verbatim from the parent (leftmost-crossing
  `Finset.min'`), with `-1` replaced by `-(m : ℤ)`.

  Status: 0 axioms, 0 sorries, build pending
-/

import Proofs.BallotProblemOQ01OQ01OQ02
import Mathlib.Tactic

open GeneralizedBallot

namespace BallotMJumpCycleLemma

/-- For sequences with all steps ≥ -m, the prefix sum can drop by at most m
    per step: prefixSum l (j+1) ≥ prefixSum l j - m. -/
theorem m_jump_step_bound (l : List ℤ) (m : ℕ)
    (h_step : ∀ x ∈ l, -(m : ℤ) ≤ x)
    (j : ℕ) (hj : j < l.length) :
    prefixSum l j - (m : ℤ) ≤ prefixSum l (j + 1) := by
  simp only [prefixSum]
  rw [List.sum_take_succ l j hj]
  linarith [h_step l[j] (List.getElem_mem hj)]

/-- **m-jump downward IVT.**

    For a sequence with all steps ≥ -m: if the prefix sum at position i
    exceeds v but at position j > i it is ≤ v, then some k ∈ (i, j]
    has prefix sum in the window `[v - m + 1, v]`.

    At m = 1, the window collapses to `{v}` and this reduces to the parent's
    `unit_decrement_downward_ivt`. At m ≥ 2, the conclusion is genuinely
    weaker (cannot hit `v` exactly when the step alphabet allows jumps of
    size up to m).

    Proof: Let kstar be the leftmost position in (i, j] with prefix sum ≤ v.
    The predecessor kstar - 1 must have prefix sum > v (by minimality).
    Since the step at kstar - 1 is ≥ -m, the prefix sum drops by at most m,
    giving prefixSum l kstar ≥ prefixSum l (kstar - 1) - m > v - m, i.e.
    prefixSum l kstar ≥ v - m + 1. Combined with ≤ v from membership: the
    prefix sum lies in [v - m + 1, v]. -/
theorem m_jump_downward_ivt (l : List ℤ) (m : ℕ)
    (h_step : ∀ x ∈ l, -(m : ℤ) ≤ x)
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_gt : v < prefixSum l i)
    (hj_le : prefixSum l j ≤ v) :
    ∃ k, i < k ∧ k ≤ j ∧ v - (m : ℤ) + 1 ≤ prefixSum l k ∧ prefixSum l k ≤ v := by
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
  -- The step at kstar - 1 is ≥ -m
  have hpred_lt_len : kstar - 1 < l.length := by omega
  have hstep_bound : -(m : ℤ) ≤ l[kstar - 1] :=
    h_step l[kstar - 1] (List.getElem_mem hpred_lt_len)
  -- prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1]
  have hsucc : prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1] := by
    simp only [prefixSum]
    conv_lhs => rw [show kstar = kstar - 1 + 1 from by omega]
    rw [List.sum_take_succ l (kstar - 1) hpred_lt_len]
  -- Conclude: prefixSum l kstar ∈ [v - m + 1, v]
  refine ⟨kstar, hkstar_gt_i, hkstar_le_j, ?_, hkstar_le_v⟩
  -- Lower bound: prefixSum l kstar ≥ v - m + 1
  -- From hpred_gt: prefixSum l (kstar - 1) ≥ v + 1
  -- hsucc: prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1]
  -- hstep_bound: l[kstar - 1] ≥ -m
  -- So prefixSum l kstar ≥ (v + 1) + (-m) = v - m + 1
  linarith

/-- **m = 1 sanity check**: at m = 1, the m-jump IVT window `[v - 1 + 1, v] = {v}`
    coincides with the unit-decrement IVT, so the parent's theorem is recovered. -/
theorem m_jump_downward_ivt_unit_recovery (l : List ℤ)
    (h_step : ∀ x ∈ l, -(1 : ℤ) ≤ x)
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_gt : v < prefixSum l i)
    (hj_le : prefixSum l j ≤ v) :
    ∃ k, i < k ∧ k ≤ j ∧ prefixSum l k = v := by
  obtain ⟨k, hk_gt, hk_le, hk_lo, hk_hi⟩ :=
    m_jump_downward_ivt l 1 (by simpa using h_step) v i j hij hjlen hi_gt hj_le
  refine ⟨k, hk_gt, hk_le, ?_⟩
  -- hk_lo : v - 1 + 1 ≤ prefixSum l k, i.e. v ≤ prefixSum l k
  -- hk_hi : prefixSum l k ≤ v
  linarith

/-! ## Upward IVT (B′ companion)

The S1c PREP (`sessions/2026-05-13-s1c-prep-conjecture-b-prime-two-sided-alphabet.md`)
identifies conjecture **B′** — the two-sided alphabet variant `-m ≤ x ≤ m`
that survives the S1b refutation — and lays out a four-stage discharge plan.
The first new ingredient is **D′**, the *upward* m-jump IVT: a symmetric
dual of `m_jump_downward_ivt` that bounds prefix-sum *increases* by `m` per
step.

This section adds the dual step-bound and the upward IVT (D′), with the
m = 1 sanity check recovering an upward-unit IVT.
-/

/-- For sequences with all steps ≤ m, the prefix sum can rise by at most m
    per step: prefixSum l (j+1) ≤ prefixSum l j + m. -/
theorem m_jump_step_bound_upward (l : List ℤ) (m : ℕ)
    (h_step : ∀ x ∈ l, x ≤ (m : ℤ))
    (j : ℕ) (hj : j < l.length) :
    prefixSum l (j + 1) ≤ prefixSum l j + (m : ℤ) := by
  simp only [prefixSum]
  rw [List.sum_take_succ l j hj]
  linarith [h_step l[j] (List.getElem_mem hj)]

/-- **m-jump upward IVT** (D′ — symmetric dual of `m_jump_downward_ivt`).

    For a sequence with all steps ≤ m: if the prefix sum at position i
    is below v but at position j > i it reaches or exceeds v, then some
    k ∈ (i, j] has prefix sum in the window `[v, v + m - 1]`.

    At m = 1, the window collapses to `{v}` and this reduces to an upward-
    unit IVT (the dual of `unit_decrement_downward_ivt`). At m ≥ 2, the
    conclusion is genuinely weaker (cannot hit `v` exactly when the step
    alphabet allows jumps of size up to m).

    Proof: Let kstar be the leftmost position in (i, j] with prefix sum ≥ v.
    The predecessor kstar - 1 must have prefix sum < v (by minimality).
    Since the step at kstar - 1 is ≤ m, the prefix sum rises by at most m,
    giving prefixSum l kstar ≤ prefixSum l (kstar - 1) + m < v + m, i.e.
    prefixSum l kstar ≤ v + m - 1. Combined with ≥ v from membership: the
    prefix sum lies in [v, v + m - 1]. -/
theorem m_jump_upward_ivt (l : List ℤ) (m : ℕ)
    (h_step : ∀ x ∈ l, x ≤ (m : ℤ))
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_lt : prefixSum l i < v)
    (hj_ge : v ≤ prefixSum l j) :
    ∃ k, i < k ∧ k ≤ j ∧ v ≤ prefixSum l k ∧ prefixSum l k ≤ v + (m : ℤ) - 1 := by
  -- S = positions in (i, j] with prefix sum ≥ v
  let S := (Finset.Ico (i + 1) (j + 1)).filter (fun k => v ≤ prefixSum l k)
  have hS_ne : S.Nonempty :=
    ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hj_ge⟩⟩
  let kstar := S.min' hS_ne
  have hkstar_mem : kstar ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨hkstar_ico, hkstar_ge_v⟩ := Finset.mem_filter.mp hkstar_mem
  rw [Finset.mem_Ico] at hkstar_ico
  have hkstar_gt_i : i < kstar := by omega
  have hkstar_le_j : kstar ≤ j := by omega
  -- kstar - 1 has prefix sum < v
  have hpred_lt : prefixSum l (kstar - 1) < v := by
    by_cases heq : kstar = i + 1
    · -- kstar - 1 = i: use hi_lt
      have : kstar - 1 = i := by omega
      rw [this]; exact hi_lt
    · -- kstar - 1 ∈ (i, kstar): use minimality of kstar
      by_contra hge; push_neg at hge
      have hpred_mem : kstar - 1 ∈ S :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hge⟩
      have := Finset.min'_le S (kstar - 1) hpred_mem
      omega
  -- The step at kstar - 1 is ≤ m
  have hpred_lt_len : kstar - 1 < l.length := by omega
  have hstep_bound : l[kstar - 1] ≤ (m : ℤ) :=
    h_step l[kstar - 1] (List.getElem_mem hpred_lt_len)
  -- prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1]
  have hsucc : prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1] := by
    simp only [prefixSum]
    conv_lhs => rw [show kstar = kstar - 1 + 1 from by omega]
    rw [List.sum_take_succ l (kstar - 1) hpred_lt_len]
  -- Conclude: prefixSum l kstar ∈ [v, v + m - 1]
  refine ⟨kstar, hkstar_gt_i, hkstar_le_j, hkstar_ge_v, ?_⟩
  -- Upper bound: prefixSum l kstar ≤ v + m - 1
  -- From hpred_lt: prefixSum l (kstar - 1) ≤ v - 1
  -- hsucc: prefixSum l kstar = prefixSum l (kstar - 1) + l[kstar - 1]
  -- hstep_bound: l[kstar - 1] ≤ m
  -- So prefixSum l kstar ≤ (v - 1) + m = v + m - 1
  linarith

/-- **m = 1 sanity check (upward)**: at m = 1, the upward m-jump IVT window
    `[v, v + 1 - 1] = {v}` coincides with an upward-unit IVT. -/
theorem m_jump_upward_ivt_unit_recovery (l : List ℤ)
    (h_step : ∀ x ∈ l, x ≤ (1 : ℤ))
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_lt : prefixSum l i < v)
    (hj_ge : v ≤ prefixSum l j) :
    ∃ k, i < k ∧ k ≤ j ∧ prefixSum l k = v := by
  obtain ⟨k, hk_gt, hk_le, hk_lo, hk_hi⟩ :=
    m_jump_upward_ivt l 1 (by simpa using h_step) v i j hij hjlen hi_lt hj_ge
  refine ⟨k, hk_gt, hk_le, ?_⟩
  -- hk_lo : v ≤ prefixSum l k
  -- hk_hi : prefixSum l k ≤ v + 1 - 1, i.e. prefixSum l k ≤ v
  linarith

end BallotMJumpCycleLemma
