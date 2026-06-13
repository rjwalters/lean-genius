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

  Later parts add: conjecture E (alphabet `{+1, -m}`), Path B (alphabet
  `{-m, …, -1, 1}`), Option C (S11 ACT — the two-sided bounded alphabet
  `{-m, …, 0, 1}`, completing Path B with the zero step), and the sharpest
  one-sided form (S12 — alphabet `x ≤ 1` with no lower bound; subsumes the
  Path B and Option C variants as immediate corollaries).

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
  -- hk_lo : v - ↑1 + 1 ≤ prefixSum l k, i.e. v ≤ prefixSum l k
  -- hk_hi : prefixSum l k ≤ v
  -- `omega` (not `linarith`) is needed because `↑(1 : ℕ) = (1 : ℤ)` is
  -- not auto-normalised by `linarith` in v4.26.0.
  omega

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

/-- **Two-sided step bound** (B′ alphabet `-m ≤ x ≤ m`): on a sequence whose
    steps lie in `[-m, m]`, consecutive prefix sums differ by at most `m` in
    absolute value. This packages the downward (`m_jump_step_bound`) and
    upward (`m_jump_step_bound_upward`) one-sided bounds into the single
    Lipschitz-in-index estimate underlying the two-sided IVT family. -/
theorem m_jump_step_abs_bound (l : List ℤ) (m : ℕ)
    (h_lo : ∀ x ∈ l, -(m : ℤ) ≤ x) (h_hi : ∀ x ∈ l, x ≤ (m : ℤ))
    (j : ℕ) (hj : j < l.length) :
    |prefixSum l (j + 1) - prefixSum l j| ≤ (m : ℤ) := by
  have h1 := m_jump_step_bound l m h_lo j hj
  have h2 := m_jump_step_bound_upward l m h_hi j hj
  rw [abs_le]
  constructor <;> linarith

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
  -- hk_hi : prefixSum l k ≤ v + ↑1 - 1, i.e. prefixSum l k ≤ v
  -- `omega` (not `linarith`) is needed because `↑(1 : ℕ) = (1 : ℤ)` is
  -- not auto-normalised by `linarith` in v4.26.0.
  omega

/-! ## Part: Conjecture E discharge — restricted alphabet `{+1, -m}`

S1 OBSERVE refuted the naive `⌈l.sum / m⌉ ≤ |goodRotations|` bound on the
broad `step ≥ -m` family. **Conjecture E** restricts attention to the
alphabet `{+1, -m}`, on which the parent's `cycle_lemma` (in `GeneralizedBallot`,
`BallotProblemOQ01.lean:764`) gives the *exact* count

```
(goodRotations l).card = a - m·b = l.sum.toNat
```

where `a = l.count 1`, `b = l.count (-m)`. This dominates `⌈l.sum / m⌉` since
`m ≥ 1`. The discharge is a thin restatement of the parent — not a
consequence of the m-jump IVTs (D, D′) above, whose conclusion windows are
strictly weaker. The only non-trivial atom is the residual arithmetic
`⌈S/m⌉ ≤ S` for `S > 0` and `m ≥ 1`.
-/

/-- Residual arithmetic atom for conjecture E: for `S > 0` and `m ≥ 1`,
    `⌈S/m⌉ ≤ S` in `Int.toNat`. -/
private lemma ceil_div_le_toNat (S : ℤ) (m : ℕ) (hm : 1 ≤ m) (hS : 0 < S) :
    Int.toNat ⌈(S : ℚ) / m⌉ ≤ S.toNat := by
  have hm_pos : (0 : ℚ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hSQ : (0 : ℚ) < S := by exact_mod_cast hS
  have hmQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  -- S / m ≤ S since m ≥ 1 and S > 0
  have hle : (S : ℚ) / m ≤ S := by
    rw [div_le_iff₀ hm_pos]
    nlinarith
  -- Therefore ⌈S/m⌉ ≤ S (in ℤ)
  have hceil_le : ⌈(S : ℚ) / m⌉ ≤ S := by
    rw [Int.ceil_le]; exact_mod_cast hle
  -- ⌈S/m⌉ ≥ 0 since S/m > 0
  have h_pos : (0 : ℚ) < (S : ℚ) / m := div_pos hSQ hm_pos
  have hceil_nonneg : (0 : ℤ) ≤ ⌈(S : ℚ) / m⌉ :=
    Int.ceil_nonneg h_pos.le
  -- Combine into toNat
  omega

/-- **Conjecture E**: on the restricted alphabet `{+1, -m}` with positive sum,
    the fractional cycle-lemma bound `⌈l.sum / m⌉ ≤ (goodRotations l).card`
    holds.

    A thin restatement of the parent's `cycle_lemma`
    (`BallotProblemOQ01.lean:764`): with `a := l.count 1`, `b := l.count (-m)`,
    we have `l ∈ kCountedSequence m a b` and `m·b < a`, so
    `(goodRotations l).card = a - m·b = l.sum.toNat`. The residual
    `⌈S/m⌉ ≤ S` follows from `m ≥ 1`.

    **Contrast with S1 OBSERVE**: the analogous bound on the broad `step ≥ -m`
    family is FALSE — the refuting witness `l = [-m, 2m+1]` has
    `|goodRotations| = 1 < ⌈(m+1)/m⌉ = 2`. The alphabet restriction
    `x = 1 ∨ x = -m` blocks that family (the only allowed positive value is
    `1`, not `2m+1`). -/
theorem step_in_one_neg_m_count (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)) (hS : 0 < l.sum) :
    Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ (goodRotations l).card := by
  -- Bridge: l ∈ kCountedSequence m (l.count 1) (l.count (-m))
  have hl_mem : l ∈ kCountedSequence m (l.count 1) (l.count (-(m : ℤ))) :=
    ⟨rfl, rfl, h_step⟩
  -- Sum identity from the parent
  have hsum : l.sum = (l.count 1 : ℤ) - m * (l.count (-(m : ℤ))) :=
    kCountedSequence_sum hl_mem
  -- Positivity of l.sum forces m·b < a
  have hab : m * l.count (-(m : ℤ)) < l.count 1 := by
    have h_pos : (0 : ℤ) < (l.count 1 : ℤ) - m * (l.count (-(m : ℤ))) := hsum ▸ hS
    have habℤ : (m * l.count (-(m : ℤ)) : ℤ) < (l.count 1 : ℤ) := by linarith
    exact_mod_cast habℤ
  -- Apply parent's cycle_lemma: exact count
  have hcard : (goodRotations l).card = l.count 1 - m * l.count (-(m : ℤ)) :=
    cycle_lemma hl_mem hab
  rw [hcard]
  -- Bridge `(a - m*b : ℕ) = l.sum.toNat`
  have h_eq : (l.count 1 - m * l.count (-(m : ℤ)) : ℕ) = l.sum.toNat := by
    have habℤ : (m * l.count (-(m : ℤ)) : ℤ) ≤ (l.count 1 : ℤ) := by exact_mod_cast hab.le
    rw [hsum]
    -- ((a : ℤ) - m * b).toNat = a - m * b when m·b ≤ a
    omega
  rw [h_eq]
  exact ceil_div_le_toNat l.sum m hm hS


/-! ## Part: Path B (S7 ACT) — Mixed-down alphabet variant of the cycle lemma

S5 PREP §3.2 (`sessions/2026-05-13-s5-prep-discharge-sketch-audit.md`) and
S7 PREP §3 (`sessions/2026-05-14-s7-prep-path-b-transfer-audit.md`) identify
**Path B**: the alphabet `x = 1 ∨ ∃ k ∈ {1,…,m}, x = −k` (one-up plus
arbitrary mixed-down). Under this hypothesis, the parent's `cycle_lemma`
chain (`BallotProblemOQ01.lean:563–774`) transfers via a single
`rcases`-pattern adjustment to destructure the existential. The
`linarith [show (0 : ℤ) ≤ k …]` discharge in the parent depends only on
`0 ≤ k`, **not** on `1 ≤ k` or `k ≤ m`, so the adaptation is purely
syntactic. The conclusion strengthens from B′'s slack form to an
**equality**:

```
(goodRotations l).card = l.sum.toNat
```

The parent's `levelPos` private helpers are not cross-file callable; this
file re-defines them as `private` in the slug namespace (per S7 PREP §3.4
implementation choice (b)).
-/

/-- Path B private helper: rightmost position with prefix sum ≤ `minPrefixSum + n`.
    Verbatim from `BallotProblemOQ01.lean:665`. -/
private noncomputable def levelPosB (l : List ℤ) (n : ℕ) : ℕ :=
  ((Finset.range (l.length + 1)).filter (fun i => prefixSum l i ≤ minPrefixSum l + n)).max'
    ⟨rightmostMinPos l, Finset.mem_filter.mpr ⟨
      Finset.mem_range.mpr (Nat.lt_succ_of_le (rightmostMinPos_le l)),
      by rw [prefixSum_rightmostMinPos]; omega⟩⟩

private theorem levelPosB_mem (l : List ℤ) (n : ℕ) :
    levelPosB l n ∈ (Finset.range (l.length + 1)).filter
      (fun i => prefixSum l i ≤ minPrefixSum l + n) := by
  unfold levelPosB; exact Finset.max'_mem _ _

private theorem levelPosB_le (l : List ℤ) (n : ℕ) : levelPosB l n ≤ l.length :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp (levelPosB_mem l n)).1)

private theorem levelPosB_prefixSum_le (l : List ℤ) (n : ℕ) :
    prefixSum l (levelPosB l n) ≤ minPrefixSum l + n :=
  (Finset.mem_filter.mp (levelPosB_mem l n)).2

private theorem levelPosB_max (l : List ℤ) (n p : ℕ)
    (hp : p ≤ l.length) (hp_le : prefixSum l p ≤ minPrefixSum l + n) :
    p ≤ levelPosB l n :=
  Finset.le_max' _ p (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_le⟩)

private theorem levelPosB_lt (l : List ℤ) (n : ℕ) (hn : (n : ℤ) < l.sum) :
    levelPosB l n < l.length := by
  rcases Nat.eq_or_lt_of_le (levelPosB_le l n) with h | h
  · have hle := levelPosB_prefixSum_le l n
    rw [h, prefixSum_length] at hle
    linarith [minPrefixSum_le_zero l]
  · exact h

private theorem levelPosB_right (l : List ℤ) (n p : ℕ)
    (hp_gt : levelPosB l n < p) (hp_le : p ≤ l.length) :
    minPrefixSum l + (n : ℤ) < prefixSum l p := by
  by_contra hle; push_neg at hle
  exact absurd (levelPosB_max l n p hp_le hle) (by omega)

/-- **Path B `levelPos_eq`** — the parent's `levelPos_eq`
    (`BallotProblemOQ01.lean:703`) adapted to the mixed-down alphabet.
    The proof is identical except for a single `rcases`-pattern change to
    destructure the existential `∃ k ∈ {1,…,m}, x = −k`. The
    `linarith [show (0 : ℤ) ≤ k …]` discharge depends only on `0 ≤ k`. -/
private theorem levelPosB_eq (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (n : ℕ) (hn : (n : ℤ) < l.sum) :
    prefixSum l (levelPosB l n) = minPrefixSum l + n := by
  have hj_lt : levelPosB l n < l.length := levelPosB_lt l n hn
  have hj_le : prefixSum l (levelPosB l n) ≤ minPrefixSum l + n := levelPosB_prefixSum_le l n
  have hj1_gt : minPrefixSum l + (n : ℤ) < prefixSum l (levelPosB l n + 1) := by
    by_contra hle; push_neg at hle
    exact absurd (levelPosB_max l n (levelPosB l n + 1) (by omega) hle) (by omega)
  have helem : l[levelPosB l n] = (1 : ℤ) := by
    rcases hmem l[levelPosB l n] (List.getElem_mem hj_lt) with h1 | ⟨k, _hk_lo, _hk_hi, hx_eq⟩
    · exact h1
    · exfalso
      have hstep : prefixSum l (levelPosB l n + 1)
          = prefixSum l (levelPosB l n) + l[levelPosB l n] := by
        simp only [prefixSum]; exact List.sum_take_succ l (levelPosB l n) hj_lt
      rw [hstep, hx_eq] at hj1_gt
      linarith [show (0 : ℤ) ≤ (k : ℤ) from Int.natCast_nonneg k]
  have hstep : prefixSum l (levelPosB l n + 1) = prefixSum l (levelPosB l n) + 1 := by
    simp only [prefixSum]; rw [List.sum_take_succ l (levelPosB l n) hj_lt, helem]
  linarith

/-- **Path B lower bound** — analog of `goodRotations_card_ge`
    (`BallotProblemOQ01.lean:731`), free of the `kCountedSequence` structure.
    Uses `hS : 0 < l.sum` directly; the count `l.sum.toNat` replaces the
    parent's `a - k * b`. -/
private theorem goodRotations_card_ge_pathB (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    l.sum.toNat ≤ (goodRotations l).card := by
  -- Bridge `n < l.sum.toNat ↔ (n : ℤ) < l.sum` via `Int.toNat_of_nonneg hS.le`.
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  rw [← Finset.card_range l.sum.toNat]
  apply Finset.card_le_card_of_injOn (levelPosB l)
  · -- Each `levelPosB n` lies in goodRotations.
    intro n hn
    have hn_lt : n < l.sum.toNat := Finset.mem_range.mp (Finset.mem_coe.mp hn)
    have hn' : (n : ℤ) < l.sum := by
      have : (n : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn_lt
      omega
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (levelPosB_lt l n hn'),
        rightmostAtLevel_good l (minPrefixSum l + n) hS
          (by linarith [show (0 : ℤ) ≤ (n : ℤ) from Int.natCast_nonneg n])
          (by linarith)
          (levelPosB l n) (levelPosB_lt l n hn')
          (levelPosB_eq l m hmem n hn')
          (fun p hp hpl => levelPosB_right l n p hp hpl)⟩)
  · -- `levelPosB` is injective on `Finset.range l.sum.toNat`.
    intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hn₁ hn₂
    have hn₁' : (n₁ : ℤ) < l.sum := by
      have : (n₁ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₁
      omega
    have hn₂' : (n₂ : ℤ) < l.sum := by
      have : (n₂ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₂
      omega
    have h₁ := levelPosB_eq l m hmem n₁ hn₁'
    have h₂ := levelPosB_eq l m hmem n₂ hn₂'
    rw [heq] at h₁
    have : (n₁ : ℤ) = n₂ := by linarith
    exact_mod_cast this

/-- **Path B equality** — combines the parent's `goodRotations_card_le`
    upper bound (alphabet-agnostic) with Path B's lower bound to give an
    exact count. This is the strict-equality version of B′'s slack form
    (`step_in_one_pos_mixed_neg_card_bound` below). -/
theorem step_in_one_pos_mixed_neg_card_eq (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat :=
  le_antisymm (goodRotations_card_le hS) (goodRotations_card_ge_pathB l m hmem hS)

/-- **Path B slack-form corollary** — recovers B′'s slack inequality
    `l.sum ≤ m · |gR| + (m − 1) · l.length` from the strict equality,
    via `Int.toNat_of_nonneg`. The slack term is non-negative when
    `m ≥ 1`; equality holds when `m = 1`. -/
theorem step_in_one_pos_mixed_neg_card_bound (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hmem : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + ((m : ℤ) - 1) * l.length := by
  have heq := step_in_one_pos_mixed_neg_card_eq l m hmem hS
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  have h_card_eq : ((goodRotations l).card : ℤ) = l.sum := by
    have : ((goodRotations l).card : ℤ) = (l.sum.toNat : ℤ) := by exact_mod_cast heq
    omega
  -- Goal: l.sum ≤ m * (goodRotations l).card + (m - 1) * l.length
  -- After substitution: l.sum ≤ m * l.sum + (m - 1) * l.length
  -- i.e. 0 ≤ (m - 1) * l.sum + (m - 1) * l.length = (m - 1) * (l.sum + l.length)
  have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hlen : (0 : ℤ) ≤ (l.length : ℤ) := by exact_mod_cast l.length.zero_le
  nlinarith [hS, hmZ, hlen, h_card_eq]

/-! ## Part: S12 — Sharpest one-sided alphabet `x ≤ 1`

S7 ACT's Path B (`step_in_one_pos_mixed_neg_card_eq`, above) handles the
alphabet `x = 1 ∨ x = -k` for `1 ≤ k ≤ m`, element set `{-m, …, -1, 1}` —
missing the zero step. S11 ACT (Option C) added the zero step via the
two-sided bounded alphabet

```
∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1
```

and noted that the lower bound `-(m : ℤ) ≤ x` is **inert** — the `omega`
proof of the level identity consumes only `x ≤ 1`, the downstream count
routes the alphabet hypothesis solely through that lemma, and the upper
bound `goodRotations_card_le` is alphabet-agnostic.

This Part acts on that observation: the cycle-lemma equality
`(goodRotations l).card = l.sum.toNat` holds for the broader one-sided
alphabet `∀ x ∈ l, x ≤ 1` *with no lower bound on negative steps at all*.
The level-visitation guarantee that powers the unit-decrement cycle lemma
needs only the upward cap: capping positive steps at `+1` makes the prefix
sum climb by exactly one per up-step, hitting every integer level on the
way up; steps `≤ 0` of any magnitude merely delay the climb.

S1's refutation (the `[-m, m + S]` family) used an *uncapped* positive jump
`+(m + S)` to skip levels — once the cap `x ≤ 1` is in place, no analogous
counterexample survives. So `x ≤ 1` is the maximal clean alphabet for the
strict equality.

The earlier Option C variants `step_in_one_pos_pm_card_eq` and
`step_in_one_pos_pm_card_bound` are preserved as public API and become thin
corollaries: drop the `.2` of the conjunctive hypothesis and forward to
`step_le_one_card_eq`. The previously private Option C helpers
(`levelPosB_eq_optionC`, `goodRotations_card_ge_pathB_optionC`) are
replaced by their unconstrained `_capOne` counterparts; their bodies are
identical except for the dropped, never-consumed lower-bound assumption.
-/

/-- Sharpest level identity — strengthening of the now-removed
    `levelPosB_eq_optionC` (Path B Option C variant) with the inert
    lower-bound assumption dropped. For sequences with all steps `≤ 1`, the
    maximal position landing at or below level `minPrefixSum + n` lands
    *exactly* at it (when `n < l.sum`).

    Proof: maximality of `levelPosB l n` forces a strict upward jump at the
    boundary (`hj1_gt`); combined with `prefixSum ≤ minPrefixSum + n`
    (`hj_le`) and the cap `x ≤ 1`, `omega` pins both `l[idx] = 1` and
    `prefixSum = minPrefixSum + n`. -/
private theorem levelPosB_eq_capOne (l : List ℤ)
    (hmem : ∀ x ∈ l, x ≤ 1)
    (n : ℕ) (hn : (n : ℤ) < l.sum) :
    prefixSum l (levelPosB l n) = minPrefixSum l + n := by
  have hj_lt : levelPosB l n < l.length := levelPosB_lt l n hn
  have hj_le : prefixSum l (levelPosB l n) ≤ minPrefixSum l + n :=
    levelPosB_prefixSum_le l n
  have hj1_gt : minPrefixSum l + (n : ℤ) < prefixSum l (levelPosB l n + 1) := by
    by_contra hle; push_neg at hle
    exact absurd (levelPosB_max l n (levelPosB l n + 1) (by omega) hle) (by omega)
  have hstep_eq : prefixSum l (levelPosB l n + 1)
      = prefixSum l (levelPosB l n) + l[levelPosB l n] := by
    simp only [prefixSum]; exact List.sum_take_succ l (levelPosB l n) hj_lt
  have hxle : l[levelPosB l n] ≤ 1 :=
    hmem l[levelPosB l n] (List.getElem_mem hj_lt)
  rw [hstep_eq] at hj1_gt
  omega

/-- Sharpest lower bound — strengthening of the now-removed
    `goodRotations_card_ge_pathB_optionC` with the inert lower-bound
    hypothesis dropped. Routes the level identity through
    `levelPosB_eq_capOne`. -/
private theorem goodRotations_card_ge_capOne (l : List ℤ)
    (hmem : ∀ x ∈ l, x ≤ 1)
    (hS : 0 < l.sum) :
    l.sum.toNat ≤ (goodRotations l).card := by
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  rw [← Finset.card_range l.sum.toNat]
  apply Finset.card_le_card_of_injOn (levelPosB l)
  · intro n hn
    have hn_lt : n < l.sum.toNat := Finset.mem_range.mp (Finset.mem_coe.mp hn)
    have hn' : (n : ℤ) < l.sum := by
      have : (n : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn_lt
      omega
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (levelPosB_lt l n hn'),
        rightmostAtLevel_good l (minPrefixSum l + n) hS
          (by linarith [show (0 : ℤ) ≤ (n : ℤ) from Int.natCast_nonneg n])
          (by linarith)
          (levelPosB l n) (levelPosB_lt l n hn')
          (levelPosB_eq_capOne l hmem n hn')
          (fun p hp hpl => levelPosB_right l n p hp hpl)⟩)
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hn₁ hn₂
    have hn₁' : (n₁ : ℤ) < l.sum := by
      have : (n₁ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₁
      omega
    have hn₂' : (n₂ : ℤ) < l.sum := by
      have : (n₂ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₂
      omega
    have h₁ := levelPosB_eq_capOne l hmem n₁ hn₁'
    have h₂ := levelPosB_eq_capOne l hmem n₂ hn₂'
    rw [heq] at h₁
    have : (n₁ : ℤ) = n₂ := by linarith
    exact_mod_cast this

/-- **Sharpest cycle-lemma equality** — for any list `l : List ℤ` with all
    steps `≤ 1` and positive total sum, the count of good rotations is
    exactly `l.sum.toNat`. This is the maximal clean alphabet on which the
    strict equality survives: S1's refutation (the `[-m, m + S]` family)
    shows it fails as soon as the cap `x ≤ 1` is relaxed to any wider
    upward alphabet. Subsumes Option C and the earlier Path B variants —
    each of those adds an inert lower bound for parameterisation, not
    necessity. -/
theorem step_le_one_card_eq (l : List ℤ)
    (hmem : ∀ x ∈ l, x ≤ 1)
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat :=
  le_antisymm (goodRotations_card_le hS) (goodRotations_card_ge_capOne l hmem hS)

/-- **Option C equality** (S11 ACT public API, preserved) — for sequences
    with every step in `{-m, …, 0, 1}` and positive total sum, the count of
    good rotations is exactly `l.sum.toNat`. Now a thin corollary of
    `step_le_one_card_eq`: drop the inert lower bound and forward to the
    sharper theorem. -/
theorem step_in_one_pos_pm_card_eq (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat :=
  step_le_one_card_eq l (fun x hx => (hmem x hx).2) hS

/-- **Option C slack-form** (S11 ACT public API, preserved) — recovers the
    B′-style bound `l.sum ≤ m·|gR| + (m − 1)·l.length` from the strict
    equality. The `m` parameter governs only the slack magnitude; the
    underlying equality is the alphabet-free `step_le_one_card_eq`. The
    slack term `(m − 1)·l.length` is non-negative when `m ≥ 1`; equality
    holds at `m = 1`. -/
theorem step_in_one_pos_pm_card_bound (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + ((m : ℤ) - 1) * l.length := by
  have heq := step_le_one_card_eq l (fun x hx => (hmem x hx).2) hS
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  have h_card_eq : ((goodRotations l).card : ℤ) = l.sum := by
    have : ((goodRotations l).card : ℤ) = (l.sum.toNat : ℤ) := by exact_mod_cast heq
    omega
  have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hlen : (0 : ℤ) ≤ (l.length : ℤ) := by exact_mod_cast l.length.zero_le
  nlinarith [hS, hmZ, hlen, h_card_eq]

end BallotMJumpCycleLemma
