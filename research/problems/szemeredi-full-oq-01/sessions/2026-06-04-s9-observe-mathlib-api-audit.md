# Session 9 — OBSERVE: Mathlib API Audit + Host-Recovery Confirmation

- **Date**: 2026-06-04
- **Author**: researcher-1 (claim `researcher-6552`)
- **Worktree**: `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1`
- **Mode**: REVISIT (depth-first claim, knowledge score 35 RICH, tier MODERATE+, 718-available pool)
- **Phase**: ACT (slug) → OBSERVE (this session, doc-only — no Lean edits)
- **Outcome**: progress (host-recovery + API audit; ACT no longer gated)

---

## 1. Why S9 fires

Session 8 (2026-05-17, three near-simultaneous doc-only STATE-SYNC PRs:
`#19974`, `#19976`, `#19977`) absorbed the Session 7 / PR #14878
transition that fixed 6 Mathlib API drift root errors but explicitly
deferred the actual Lean edit (filling `limit_invariant_on_cylinder` at
`FurstenbergCorrespondenceOQ01.lean:779`) to **"S9 ACT
(host-recovery-gated)"**.

S8's host-recovery gates:

| Gate | S8 requirement | S8 observed (2026-05-17) |
|---|---|---|
| `docker info` returns Server: section within 5 s | yes | hangs at 5 s, no Server: |
| `df -h /` shows Avail ≥ 30 Gi | yes | 3.4 Gi |

Neither passed at S8. S8 documented this and explicitly chose not to
attempt ACT.

S9 begins by checking these gates again, 18 days later.

---

## 2. Host-recovery check (2026-06-04T16:00Z)

```
$ timeout 5 docker info
Client:
 Version:    29.4.1
 Context:    desktop-linux
 Debug Mode: false
 Plugins:
...
---exit: 0---

$ timeout 8 docker info | grep -E "Server:|Server Version"
Server:
 Server Version: 29.4.1

$ df -h /
Filesystem        Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s1s1   926Gi    12Gi    39Gi    24%    459k  409M    0%   /
```

| Gate | S8 | S9 | Δ |
|---|---|---|---|
| `docker info` Server: | hangs | < 8 s, Server Version 29.4.1 | RECOVERED |
| `df -h /` Avail | 3.4 Gi | 39 Gi | RECOVERED (39 ≥ 30 floor) |

**Both gates pass.** S8's HOST blocker is discharged.

---

## 3. Why I did NOT go straight to S9 ACT

Three reasons, in order of severity:

### 3.1 Worktree `.lake` is unusable in this isolation

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  rwalters  staff  47 May 29 11:42 .lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake

$ ls /Users/rwalters/GitHub/lean-genius/proofs/.lake/packages
ls: ... Too many levels of symbolic links
```

The worktree's `proofs/.lake` is a self-referencing symlink. So local
Mathlib source resolution is unavailable from this worktree. Any Lean
edit I make would be blind to tactic-level drift — I'd only catch errors
when Docker build runs.

The right place for the Lean edit is the main checkout at
`/Users/rwalters/GitHub/lean-genius`, where `.lake/packages/mathlib`
presumably resolves. That's S10's job.

### 3.2 File-level honesty constraint

The file comment at L776-778 of `FurstenbergCorrespondenceOQ01.lean`
says:

> Cannot fill in this proof until the surrounding file's 35 Mathlib API
> drift errors are repaired. Adding ~60 unvalidated lines here would mask
> the real blocker.

The "real blocker" (35 drift errors) was discharged by PR #14878. But
the spirit of the constraint — "don't paste unvalidated Lean" — still
applies when `.lake` is broken. S9 from this isolation respects it.

### 3.3 ACT without local validation gives weak signal

Even if I write a syntactically reasonable proof and ship it as
"build pending" (standard pattern in this repo), the value is low when
the validation cycle is "wait for human to run Docker on main checkout."
Better to give S10 ACT a clean, auditable starting point.

---

## 4. Mathlib v4.26 API audit — verification of all proof-draft lemmas

Verification method: raw GitHub fetch at Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. This is the exact pin in
`proofs/lake-manifest.json` for `mathlib`.

### 4.1 The five lemmas the proof draft (file comment L757-778) cites

| # | Lemma | Mathlib v4.26 location | Verdict |
|---|---|---|---|
| 1 | `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` (ENNReal Portmanteau) | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:333` | ✅ |
| 2 | `IsClopen.frontier_eq` | `Mathlib/Topology/Clopen.lean:38` (simp-tagged alias) | ✅ |
| 3 | `le_of_tendsto_of_tendsto'` | `Mathlib/Topology/Order/OrderClosed.lean:631` | ✅ |
| 4 | `ENNReal.tendsto_nat_nhds_top` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:148` | ✅ |
| 5 | `ENNReal.tendsto_inv_nat_nhds_zero` | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:488` | ✅ |

All five exist at the pinned revision. Their signatures match the proof
draft's usage pattern.

### 4.2 Auxiliary lemmas (already used in the file, independently known to compile)

| Lemma | Used at | Status |
|---|---|---|
| `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto` (NNReal Portmanteau) | OQ01.lean:672, 684 | ✅ in-file proof of consistency |
| `ge_of_tendsto` | OQ01.lean:674 | ✅ |
| `Filter.eventually_of_forall` | OQ01.lean:674 | ✅ |
| `cesaroMeasure_preimage_le` | proven in this file at L529 | ✅ (the upper telescoping bound) |
| `cesaroMeasure_preimage_ge` | proven in this file at L548 | ✅ (the lower telescoping bound) |
| `isClopen_shift_preimage` | proven in this file at L738 | ✅ |

### 4.3 Instance check for `CantorSpace = ℕ → Bool`

`tendsto_measure_of_null_frontier_of_tendsto'` requires:

- `MeasurableSpace Ω` — `Pi.measurableSpace` derives this
- `TopologicalSpace Ω` — `Pi.topologicalSpace`
- `OpensMeasurableSpace Ω`
- `HasOuterApproxClosed Ω`

The latter two are the only nontrivial ones. **However**, the NNReal
sibling `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto`
(Portmanteau.lean:361) requires the same four instances, and it ALREADY
compiles in this file (lines 672 and 684). So the instances resolve for
`CantorSpace` at the current Mathlib pin. **Zero instance-resolution risk.**

---

## 5. Mathematical content reconfirmed (Session 5's draft, lemma-level annotated)

The proof goal at L756:
```
(μ : Measure CantorSpace) (shift ⁻¹' S) = (μ : Measure CantorSpace) S
```
given `S` measurable + clopen, `μs → μ` weakly, `(μs k : Measure) = cesaroMeasure x (Ns k + 1)`,
and `Ns → ∞`.

Strategy (with Mathlib citations from §4):

1. **Reduce clopen to null frontier**: For clopen `S`,
   `frontier S = ∅` (Clopen.lean:38 — `IsClopen.frontier_eq`), so
   `(μ : Measure)(frontier S) = 0`. Same for `shift⁻¹S` (clopen by
   `isClopen_shift_preimage`).
2. **Apply ENNReal Portmanteau** twice (Portmanteau.lean:333):
   - `μ_k(S) → μ(S)` in ℝ≥0∞
   - `μ_k(shift⁻¹S) → μ(shift⁻¹S)` in ℝ≥0∞
3. **Error term**: `(Ns k + 1 : ℝ≥0∞)⁻¹ → 0`. Via composition:
   - `Ns → ∞` (hypothesis)
   - `Ns + 1 → ∞`
   - `(Ns k + 1 : ℝ≥0∞) → ⊤` (ENNReal.tendsto_nat_nhds_top, Lemmas.lean:148)
   - `(Ns k + 1 : ℝ≥0∞)⁻¹ → 0` (composition with `⁻¹` continuity at ⊤)
4. **Limit arithmetic**: `μ_k(S) + (Ns k + 1)⁻¹ → μ(S) + 0 = μ(S)` via
   `Tendsto.add` (general). ENNReal addition is jointly continuous.
5. **Pass bound to limit** (OrderClosed.lean:631):
   - `μ_k(shift⁻¹S) ≤ μ_k(S) + (Ns k + 1)⁻¹` from
     `cesaroMeasure_preimage_le` (L529, after `hdef k` rewrite)
   - `le_of_tendsto_of_tendsto'` gives `μ(shift⁻¹S) ≤ μ(S)`.
6. **Symmetric direction** from `cesaroMeasure_preimage_ge` (L548).
7. **`le_antisymm`**.

Total ~60 LOC. Every step uses a Mathlib lemma confirmed in §4.

---

## 6. Honest calibration

What S9 actually delivers:

- ✅ Host gates discharged (Docker + 39 Gi disk)
- ✅ All 5 proof-draft lemmas verified to exist at pinned Mathlib
- ✅ Instance resolution risk for `CantorSpace` reduced to zero (via sibling-lemma compile evidence)
- ✅ Lemma-level structural proof outline (§5) ready for S10 paste
- ✅ State.md + knowledge.md + this memo + JSON refreshed

What S9 does **NOT** deliver (honestly flagged):

- ❌ No `.lean` edit. The `sorry` at L779 stands.
- ❌ No Docker build verification. Even with host gates passing, the
  worktree's `.lake` is broken, so a build attempt from here would fail
  on missing Mathlib packages, not on any actual code issue.
- ❌ No verification of `Tendsto.add` for ENNReal (assumed via standard
  Mathlib `ContinuousAdd` instance; S10 will confirm at build).
- ❌ No verification of the `cesaroMeasure_preimage_le` arity rewrite
  (the `Ns k + 1` vs `(Ns k) + 1` indexing) — S10 may need `convert ... using 2`
  refinement.
- ❌ The 3 attempt counts in JSON were already corrected by S8 — S9 does
  not re-correct, only bumps `currentApproach` and `total` for this audit
  iteration.

---

## 7. Files changed by this S9 PR

1. `research/problems/szemeredi-full-oq-01/state.md` — prepend S9 OBSERVE-API-AUDIT
   block above S8 STATE-SYNC; refresh head metadata; rewrite "Current Focus" /
   "Active Approach" / "Attempt Count" / "Blockers" / "Next Action" to S9 state.
2. `research/problems/szemeredi-full-oq-01/knowledge.md` — append Session 9
   (this audit) below Session 7.
3. `research/problems/szemeredi-full-oq-01/sessions/2026-06-04-s9-observe-mathlib-api-audit.md`
   — NEW (this file).
4. `src/data/research/problems/szemeredi-full-oq-01.json` — bump
   `currentState.iteration` 8 → 9; refresh `focus` / `nextAction` /
   `lastUpdate`; `attemptCounts.total` 7 → 8 (S9 audit counted as a session).
5. `research/registry.json` — bump `lastUpdate` to S9 timestamp.

No `.lean` edits. No `meta.json` edits. No `problem.md` edits. No pool
status changes via this PR; pool status will be released to `available`
via the standard `claim-problem.sh update completed` path on PR completion.

---

## 8. Next actions

- **S10 ACT** (Lean edit, from main checkout):
  1. `cd /Users/rwalters/GitHub/lean-genius` (NOT `.loom/worktrees/*`)
  2. Verify `proofs/.lake/packages/mathlib` is real
  3. `./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01` (baseline)
  4. Paste 60-line proof (template in §5 + state.md Next Action)
  5. Rebuild + ship
- **S11 ACT**: `seqCompact_probabilityMeasure_cantor` (~150-200 lines,
  Prokhorov ingredients in Mathlib v4.26).

---

## 9. Pointers for the next researcher

- The proof draft has not drifted in 38 days (Session 5 → today). Its
  Mathlib citations are good. Just paste and build.
- If the build fails on `convert ... using 2` (the `cesaroMeasure_preimage_le/ge`
  arity reconciliation), the fix is likely to bind `N := Ns k` explicitly
  via `set` or to call `cesaroMeasure_preimage_le x (Ns k) S hS` with the
  exact `Ns k + 1` form (note the helper takes `(N + 1)` literally — see
  L529 statement).
- If the build fails on `simp [hSclopen.frontier_eq]`, try
  `rw [hSclopen.frontier_eq]; simp` or
  `have : frontier S = ∅ := hSclopen.frontier_eq; rw [this, measure_empty]`.
