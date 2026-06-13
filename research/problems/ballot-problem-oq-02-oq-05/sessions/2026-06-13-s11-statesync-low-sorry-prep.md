# S11 STATE-SYNC + LOW-sorry PREP — ballot-problem-oq-02-oq-05

**Agent**: researcher-2
**Date**: 2026-06-13
**Phase**: ACT (doc-only this session — verification infra down)
**Type**: STATE-SYNC (tracker correction) + PREP (paste-ready LOW-sorry skeleton)

## 1. Why this session is doc-only

Both build-verification routes are down on 2026-06-13:

| Route | Probe | Result |
|-------|-------|--------|
| Docker | `timeout 15 docker info` | exit 124 (daemon hung) |
| Aristotle MCP | `prove(<LOW lemma>, wait=false)` | `{"status":"error","message":"Resource not found."}` (backend 404) |

Disk is healthy (13% used, 79 Gi avail) — this is a daemon hang, not the
disk-full failure mode seen earlier in the fleet. With no way to type-check
a proof, no Lean proof tactics were committed (standing guidance: don't
blind-ship build-dependent ACT). This session ships only tracker
corrections + this paste-ready sketch.

## 2. Tracker drift corrected

The merged Lean state was two ACT cycles ahead of both trackers:

- **S10 ACT — PR #22924** (commit `d7e83fcb787`, 2026-06-12) discharged R5
  (`partialSumBool_reflectAt_endpoint`) and **Docker-verified it (7744 jobs
  successful)**. It was never logged in `state.md` (only the PR title and the
  file docstring recorded it).
- The research JSON (`src/data/research/problems/ballot-problem-oq-02-oq-05.json`)
  carried S6-era `leanFiles` metrics.

| Field | Stale value | Corrected (verified against file) |
|-------|-------------|-----------------------------------|
| `lineCount` | 229 | 357 |
| `sorryCount` | 6 | 2 |
| `theoremCount` | 4 | 6 (5 lemmas + 1 theorem) |
| `defCount` | 7 | 7 (unchanged) |
| `axiomCount` | 1 | 1 (unchanged) |

Remaining sorries on `main` (verified by reading the file):

- **LOW** `reaches_iff_hits_or_above` (line 334)
- **R6** `discrete_reflection` (line 353)

R4 (`reflectAt_involutive`) and R5 (`partialSumBool_reflectAt_endpoint`) are
both fully proved and Docker-verified.

## 3. The LOW sorry — math argument

```lean
lemma reaches_iff_hits_or_above
    {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a) :
    (∃ k : Fin (n+1), partialSumBool ω k ≥ a)
      ↔ partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a ∨ (hitSet ω a).Nonempty
```

`partialSumBool ω k = ∑ i : Fin n, if i.val < k.val then (±1) else 0`, so the
sequence `k ↦ S_k` starts at `S_0 = 0` and changes by **exactly ±1** per step.

- **Backward (←)** — easy:
  - endpoint-≥-a disjunct: witness `k = ⟨n, _⟩`.
  - `(hitSet ω a).Nonempty` disjunct: get `k` with `S_k = a`; then `S_k ≥ a`
    since `a ≤ a`. Witness `k`.
- **Forward (→)** — discrete IVT, yields the `(hitSet ω a).Nonempty`
  disjunct (`Or.inr`):
  1. Let `T = univ.filter (fun k => partialSumBool ω k ≥ a)`. The hypothesis
     gives `T.Nonempty`.
  2. `k₀ := T.min' hT`. Then `S_{k₀} ≥ a`.
  3. `k₀ ≠ ⟨0⟩`: `S_0 = 0 < a` (from `ha`), so `⟨0⟩ ∉ T`; hence `k₀.val ≥ 1`.
  4. Let `j := k₀.val - 1`, so `j + 1 = k₀.val` and `⟨j, _⟩ < k₀`. By
     `min'` minimality `⟨j, _⟩ ∉ T`, i.e. `S_{⟨j⟩} < a`, i.e. `S_{⟨j⟩} ≤ a - 1`.
  5. Step lemma: `S_{k₀} = S_{⟨j⟩} + (±1) ≤ (a-1) + 1 = a`. With `S_{k₀} ≥ a`,
     get `S_{k₀} = a`, so `k₀ ∈ hitSet ω a`.

## 4. Paste-ready skeleton (UNVERIFIED — build before trusting)

Two pieces: a step lemma `partialSumBool_succ` and the main proof. Insert the
step lemma just after `partialSumBool` (line ~158) and replace the LOW sorry
body (line 334).

```lean
/-- **LOW-helper.** Consecutive partial sums differ by exactly one ±1 step:
    `S_{j+1} = S_j + (±1)`, where the ± is the sign of `ω ⟨j⟩`. -/
lemma partialSumBool_succ (ω : Fin n → Bool) (j : ℕ) (hj : j < n) :
    partialSumBool ω ⟨j + 1, Nat.succ_lt_succ hj⟩
      = partialSumBool ω ⟨j, Nat.lt_succ_of_lt hj⟩
        + (if ω ⟨j, hj⟩ then (1 : ℤ) else -1) := by
  unfold partialSumBool
  rw [← Finset.sum_add_distrib]  -- reshape; see note below
  -- Per summand i : Fin n, compare guards `i.val < j+1` vs `i.val < j`.
  -- Only i = ⟨j, hj⟩ differs (contributes the ± step); all others cancel.
  -- Likely cleaner via:  Finset.sum_ite + Finset.sum_eq_single ⟨j, hj⟩
  --   on the difference  ∑ (guard<j+1) - ∑ (guard<j).
  sorry  -- arithmetic bookkeeping; needs build to settle exact tactic form
```

Note: the cleanest discharge of `partialSumBool_succ` is probably NOT the
`sum_add_distrib` reshape above but rather working with the *difference*:
```lean
  have : partialSumBool ω ⟨j+1,_⟩ - partialSumBool ω ⟨j,_⟩
       = (if ω ⟨j,hj⟩ then 1 else -1) := by
    unfold partialSumBool
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin n)]   -- single nonzero summand
    · simp [Nat.lt_succ_iff, Nat.lt_irrefl]        -- guard at i=j: <j+1 true, <j false
    · intro i _ hij                                -- i ≠ ⟨j⟩ ⇒ summand difference 0
      rcases lt_trichotomy i.val j with h|h|h
      · simp [Nat.lt_succ_of_lt h, h]              -- both guards true ⇒ step - step = 0
      · exact absurd (Fin.ext h) hij               -- i.val = j ⇒ i = ⟨j⟩, contra
      · simp [Nat.not_lt.mpr (Nat.le_of_lt h),
              Nat.not_lt.mpr (Nat.succ_le_of_lt h)]-- both guards false ⇒ 0 - 0 = 0
    · intro h; exact absurd (Finset.mem_univ _) h
  linarith [this]
```

Main proof:

```lean
lemma reaches_iff_hits_or_above
    {ω : Fin n → Bool} {a : ℤ} (ha : 0 < a) :
    (∃ k : Fin (n+1), partialSumBool ω k ≥ a)
      ↔ partialSumBool ω ⟨n, Nat.lt_succ_self n⟩ ≥ a ∨ (hitSet ω a).Nonempty := by
  constructor
  · rintro ⟨k, hk⟩
    -- Forward: discrete IVT ⇒ Or.inr (hitSet nonempty)
    right
    set T : Finset (Fin (n+1)) := Finset.univ.filter
      (fun k => partialSumBool ω k ≥ a) with hT_def
    have hT : T.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    set k₀ := T.min' hT with hk0_def
    have hk0_mem : k₀ ∈ T := T.min'_mem hT
    have hk0_ge : partialSumBool ω k₀ ≥ a := (Finset.mem_filter.mp hk0_mem).2
    -- S_0 = 0 < a, so k₀.val ≥ 1
    have hS0 : partialSumBool ω ⟨0, Nat.zero_lt_succ n⟩ = 0 := by
      simp [partialSumBool]
    have hk0_pos : 0 < k₀.val := by
      rcases Nat.eq_zero_or_pos k₀.val with h0 | hpos
      · exfalso
        have : partialSumBool ω k₀ = 0 := by
          have : k₀ = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext h0
          rw [this]; exact hS0
        omega  -- a ≤ 0 contradicts ha
      · exact hpos
    -- predecessor j = k₀.val - 1
    obtain ⟨j, hj_eq⟩ : ∃ j, k₀.val = j + 1 := ⟨k₀.val - 1, by omega⟩
    have hj_lt : j < n := by omega  -- since k₀.val ≤ n
    -- S_{⟨j⟩} < a by minimality of k₀
    have hpred_lt : partialSumBool ω ⟨j, Nat.lt_succ_of_lt hj_lt⟩ < a := by
      by_contra hge
      push_neg at hge
      have : (⟨j, Nat.lt_succ_of_lt hj_lt⟩ : Fin (n+1)) ∈ T :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
      have := T.min'_le _ this
      omega  -- j < j+1 = k₀.val ≤ this contradiction
    -- step: S_{k₀} = S_{⟨j⟩} + (±1) ≤ a, with ≥ a ⇒ = a
    have hk0_eq : k₀ = ⟨j + 1, Nat.succ_lt_succ hj_lt⟩ := Fin.ext hj_eq
    have hstep := partialSumBool_succ ω j hj_lt
    have hps_a : partialSumBool ω k₀ = a := by
      rw [hk0_eq, hstep]
      have hpm : (if ω ⟨j, hj_lt⟩ then (1:ℤ) else -1) ≤ 1 := by
        cases ω ⟨j, hj_lt⟩ <;> simp
      -- S_{⟨j⟩} ≤ a-1 and step ≤ 1 ⇒ sum ≤ a; with ≥ a ⇒ = a
      rw [hk0_eq, hstep] at hk0_ge
      omega
    exact ⟨k₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hps_a⟩⟩
  · rintro (hend | ⟨k, hk⟩)
    · exact ⟨⟨n, Nat.lt_succ_self n⟩, hend⟩
    · refine ⟨k, ?_⟩
      have : partialSumBool ω k = a := (Finset.mem_filter.mp hk).2
      rw [this]
```

### Confidence by part

| Part | Confidence | Risk |
|------|-----------|------|
| Backward direction | HIGH | trivial witnesses; `Finset.mem_filter` shape may need a `ge_iff_le`/`le_refl` nudge for the hit case |
| Forward scaffolding (`min'`, `T.Nonempty`, `S_0=0`) | HIGH | `Fin.ext`/index plumbing only |
| `omega` arithmetic steps | MEDIUM | `omega` needs the ±1 step bound as an explicit hyp; the `hpm`/`hk0_ge` feed is sketched but the exact `omega`-visible hypotheses must be in context — verify shapes |
| `partialSumBool_succ` | MEDIUM | `Finset.sum_eq_single` + guard trichotomy is the right tool; the `simp` lemma sets per branch need a build to settle |

**Do not trust the `omega` / `simp` calls until a Docker (or Aristotle)
build confirms them.** The structure is sound; the tactic details are the
unverifiable part.

## 5. Bearers (recheck at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

New bearers this skeleton needs beyond the S5–S9 inventory:

- `Finset.sum_sub_distrib` / `Finset.sum_add_distrib`
- `Finset.sum_eq_single`
- `Finset.min'_mem`, `Finset.min'_le` (already pinned, S5 §4)
- `Fin.ext`
- core `omega`, `Nat.succ_lt_succ`, `Nat.lt_succ_of_lt`, `Nat.zero_lt_succ`

All standard; line-pin at the next Docker-up ACT before relying on them.

## 6. After LOW lands: R6

`discrete_reflection` (R6, HIGH ~20 LOC) is the final assembly:
`Finset.card_nbij'` with `i = j = reflectAt _ a`, using R4
(`reflectAt_involutive`) for `left_inv`/`right_inv` and R5
(`partialSumBool_reflectAt_endpoint`) for the membership image into
(ending > a). The `reaches_iff_hits_or_above` partition proved here feeds the
`card_nbij'` source-set restriction. Discharge sketch in S5 PREP §6 / S6 ACT
inventory remains valid.

## 7. Build-verify trigger

Re-attempt ACT when **either**:
- `timeout 15 docker info` returns in ≤ 5 s (daemon recovered), or
- Aristotle MCP `prove()` returns a `project_id` instead of 404.

Then: paste §4, run `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05`,
fix the MEDIUM-confidence tactic details, and commit as S12 ACT.
