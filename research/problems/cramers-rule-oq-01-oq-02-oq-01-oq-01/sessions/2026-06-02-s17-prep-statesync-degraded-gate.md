# S17 PREP — post-S16 STATE-SYNC + ACT-readiness gate degradation observation (doc-only)

**Researcher**: researcher-1
**Date**: 2026-06-02 (8-day gap after S16 PREP at 2026-05-25T08:43:15Z)
**Phase**: S17 PREP (post-S16 quiescence sync; gate refresh)
**Predecessor**: S16 PREP (researcher-1, 2026-05-25, "9/9 GREEN" snapshot)
**Successor**: S16+1 ACT (per S15 PREP §6.2 7-step picker checklist; unchanged from S16 PREP plan)

## 0. Executive summary

8-day quiescence sync. S16 PREP declared a "9/9 GREEN" ACT-readiness
gate on 2026-05-25 with Docker RESPONSIVE and host disk at 97 Gi avail
(91.6 Gi recovered from S15 PREP's 5.4 Gi AMBER reading). This S17 PREP
re-probes:

- **Docker daemon**: RESPONSIVE (`timeout 10 docker info` returns the
  Server section cleanly within ~3 s; Client v29.4.1, Context
  `desktop-linux`).
- **Host disk**: **DEGRADED back to AMBER**: 7.8 Gi avail at 100%
  capacity (same neighbourhood as S15 PREP's 5.4 Gi AMBER reading; far
  below the 97 Gi declared GREEN at S16 PREP).

**Net gate refresh**: 9/9 GREEN → **8/9 GREEN + 1/9 AMBER (disk pressure)**.

The ACT plan itself is unchanged — S16+1 ACT picker should follow the
S15 PREP §6.2 7-step checklist verbatim (1 step discharged by S16 PREP
§1; renumbered to 7). The single open `sorry` in
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` (293 LOC, 9 thm, 0 ax,
**1 sorry** target) is the discharge target for `qdetN_step_eq_qdetF`
via the corrected Form 1 statement from S15 PREP §4.1:
`det(A.sub) = (-1)^((j : ℕ) + (j.succAbove q : ℕ) + 1) * ∑ p, A(i.succAbove p) j * adjugate M q p`.

This memo is a pure STATE-SYNC; **zero changes to Lean / meta.json /
gallery / candidate-pool**.

## 1. Field accuracy check at HEAD `5c1c35d272a`

| meta.json field (per JSON `leanFiles[]`) | declared | wc -l / grep | Status |
|---|---|---|---|
| `CramersRuleOQ01OQ02OQ01OQ01.lean` lineCount | (not in JSON leanFiles entry) | `wc -l = 293` | n/a — JSON entry lacks lineCount field |
| `CramersRuleOQ01OQ02OQ01OQ01.lean` sorryCount | 1 | matches per S16 PREP §2.1 inspection | ✓ |
| `CramersRuleOQ01OQ02OQ01OQ01.lean` theoremCount | 9 | per S16 PREP §2.1 | ✓ (assumed; not re-counted this PREP) |
| `CramersRuleOQ01OQ02OQ01OQ01.lean` axiomCount | 0 | per S16 PREP §2.1 | ✓ |

No new gallery entry was emitted for this slug (research-only). Gallery-
side audit not applicable.

## 2. ACT-readiness gate refresh (vs. S16 PREP §3 9/9 GREEN snapshot)

| # | Item | S16 PREP | S17 PREP | Notes |
|---|------|----------|----------|-------|
| 1 | Mathlib pin unchanged | GREEN | GREEN | `lake-manifest.json` rev unchanged |
| 2 | Form 1 statement verified | GREEN | GREEN | S15 PREP §4.1 |
| 3 | 7-step picker checklist refreshed | GREEN | GREEN | S15 PREP §6.2 |
| 4 | No open peer PRs on slug | GREEN | GREEN | Re-probed: `gh pr list --search "<slug>" --state open` empty |
| 5 | Lean prerequisites stable | GREEN | GREEN | `import Mathlib` chain at v4.26.0 |
| 6 | Companion `qdetF`/`submatrix_chain` infra ready | GREEN | GREEN | S12 PREP Option B (private lemma) |
| 7 | Docker daemon responsive | GREEN | **GREEN** | `timeout 10 docker info` returns Server section cleanly |
| 8 | Host disk ≥ 20 Gi avail | GREEN (97 Gi) | **AMBER** (7.8 Gi avail / 100% capacity) | regression from S16 PREP — same neighbourhood as S15 PREP's 5.4 Gi AMBER reading |
| 9 | No in-flight gate-blocking infra issue | GREEN | GREEN | no `.loom/signals/stop-*` present |

**Net**: 8/9 GREEN + **1/9 AMBER** (item 8 host disk regression).

The disk-pressure AMBER does NOT block the S16+1 ACT picker outright,
but matches the S15 PREP regime where Docker builds occasionally failed
on disk-exhaustion errors. The S16+1 ACT picker should:

- Re-probe `df -h /Users/rwalters` at branch creation; abort if avail < 5 Gi.
- Consider running `docker system prune --volumes -f` before build if
  avail < 10 Gi (frees ~10-30 Gi typically; should be safe but interrupts
  any in-progress builds by other agents).
- Apply the S15 PREP §5.2 fallback "ship the Lean delta with build-pending
  qualifier" if a build attempt fails on disk.

## 3. Files touched (3 — doc-only)

- `state.md`: prepend S17 PREP block; iteration 16 → 17;
  phase `S16 PREP` → `S17 PREP`.
- `sessions/2026-06-02-s17-prep-statesync-degraded-gate.md`: NEW
  (this file, ~110 LOC).
- `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`:
  `currentState.{phase, since, iteration, focus}` refresh; `lastUpdate`
  bump; 1 new `knowledge.insights` entry (S17 PREP gate-refresh result).

**Zero Lean / meta.json / gallery / candidate-pool edits.**

## 4. Verification log

- 2026-06-02 04:30Z: claimed `cramers-rule-oq-01-oq-02-oq-01-oq-01` via
  `scripts/research/claim-problem.sh claim-random` (knowledge score 30,
  RICH).
- 2026-06-02 04:32Z: synced worktree to `origin/main` HEAD `5c1c35d272a`.
- 2026-06-02 04:33Z: `timeout 10 docker info` returns Server section in
  ~3 s → Docker GREEN.
- 2026-06-02 04:33Z: `df -h /Users/rwalters` shows 7.8 Gi avail at 100%
  capacity → disk AMBER (regression from S16 PREP's 97 Gi GREEN).
- 2026-06-02 04:34Z: drafted gate refresh table (§2) and ACT picker
  guidance (§2.b).

## 5. Open questions for S16+1 ACT picker (unchanged from S16 PREP)

The 7-step picker checklist from S15 PREP §6.2 is unchanged; the AMBER
disk gate is the only new constraint. See S15 PREP §6.2 and S16 PREP §4
for the full guidance.
