# S20 STATE-SYNC 2026-06-03 — JSON registry catch-up post-S19 ACT + orphan registration

**Date**: 2026-06-03
**Researcher**: researcher-1
**Phase**: STATE-SYNC (doc-only)
**Type**: Registry-JSON catch-up to reflect five mergeable deltas since the
2026-05-16 lastUpdate. No Lean edits; no axiom/sorry delta; no
phase advance beyond what's already reflected on origin/main.
**Base HEAD**: `e89e9e882e1` (current `main`).

## Why this STATE-SYNC

The research registry JSON
(`src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`)
shows `lastUpdate: 2026-05-16T05:00:00.000Z` and `iteration: 17` — but
the slug's `state.md` is already at iteration 19 (S19 ACT g(5) ≥ 37 via
counting+omega, MERGED 2026-05-30 in PR #21124) and the gallery has
separately advanced through PR #21970 (orphan-companion registration,
2026-06-01). The JSON is the source of truth consumed by the
research-dashboard and by `claim-problem.sh` knowledge-scoring; the
state.md is the human-readable session ledger. The two should agree.

This S20 STATE-SYNC realigns the JSON to match state.md + origin/main
without claiming any new mathematical or build progress.

## Deltas catalogued

### Delta D1 — Iteration advance 17 → 19

- **State.md**: `**Iteration**: 19 (S19 ACT g(5) lower bound via counting+omega; researcher-1)`.
- **JSON (current)**: `"iteration": 17`.
- **Sync action**: set `"iteration": 19`.

### Delta D2 — Phase advance ACT-BLOCKED → ACT (parent-independent route confirmed)

The S19 ACT session memo
(`sessions/2026-05-29-s19-act-g5-counting-omega.md`, referenced by
state.md) identified that S5 / S6b / S7 ACTs are **parent-independent**:
the counting+omega template lives in a sibling Lean file that imports
only Mathlib, not the broken parent `LagrangeFourSquares.lean`. So
while B1 (parent regression) still blocks S4 and S6 (both use `waringG`
from the broken parent), it does NOT block S5 / S6b / S7.

- **State.md `**Phase**`**: `ACT (S5 / S6b / S7 unblocked via parent-independent route; S4 / S6 still blocked on broken LagrangeFourSquares.lean)`.
- **JSON (current) `currentState.phase`**: `ACT-BLOCKED`.
- **Sync action**: update `currentState.phase` to match state.md.

### Delta D3 — S19 ACT g(5) shipped (PR #21124 MERGED 2026-05-30)

- **State.md**: S19 ACT block (lines 7–59) documents the new
  `LagrangeFourSquaresWaringG2OQ01CountingG5.lean` (146 LOC on origin/main),
  `WaringG2OQ01.CountingG5.g5_lower_counting : ¬ IsSumOfFifthPowers 36 223`,
  Docker 7743 jobs clean, 0 sorries, 0 axioms, parent-independent.
- **JSON (current)**: no mention; `currentState.focus`, `nextAction`, and
  `attemptCounts` all frozen at S18 PREP state.
- **Sync action**: update `currentState.focus` + `nextAction` + `attemptCounts.total` to reflect S19 ACT shipment and post-S19 picker
  (S6b ACT next-recommended; S7 ACT after that).

### Delta D4 — `leanFiles[]` schema migration + missing entries

The JSON's `leanFiles[]` array uses the **old string-path schema**
(`"proofs/Proofs/...lean"`) instead of the **new object-with-metadata
schema** (`{path, filename, lineCount, theoremCount, axiomCount,
defCount, sorryCount, isAristotle, githubUrl}`) used by sibling
problem JSONs like `euler-identity-oq-01-oq-04.json`. Also, the JSON
lists only 2 of the 4 actual files on origin/main as of 2026-06-03.

The 4 actual companion files on origin/main (per PR #21970's
gallery-side meta.json registration):

| File | LOC | T | D | A | S | Provenance |
|---|---|---|---|---|---|---|
| `LagrangeFourSquaresWaringG2OQ01.lean` | 118 | 2 | 1 | 0 | 0 | S2 ACT (PR #18176 MERGED 2026-05-12) |
| `LagrangeFourSquaresWaringG2OQ01Counting.lean` | 141 | 1 | 0 | 0 | 0 | S2b ACT (PR #18928 MERGED 2026-05-13) |
| `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` | 155 | 1 | 1 | 0 | 0 | S3 ACT (PR #19129 MERGED 2026-05-14) |
| `LagrangeFourSquaresWaringG2OQ01CountingG5.lean` | 150 | 1 | 1 | 0 | 0 | S19 ACT (PR #21124 MERGED 2026-05-30) |

- **Sync action**: migrate `leanFiles[]` to the object schema and add the
  two missing entries (`CountingG4`, `CountingG5`). LOC/T/D/A/S counts
  come from PR #21970's commit message body (which the orphan-
  registration mechanic audited).

### Delta D5 — `lastUpdate` advance

- **State.md** last meaningful entry: 2026-05-29 (S19 ACT).
- **JSON `lastUpdate`**: `2026-05-16T05:00:00.000Z`.
- **Sync action**: bump to 2026-06-03 (this STATE-SYNC).

## What this STATE-SYNC does NOT do

1. **No Lean edits** — no source file changes.
2. **No build verification** — STATE-SYNC is doc-only; no Docker run.
3. **No advance of state.md** beyond appending this S20 STATE-SYNC entry.
4. **No Mechanic poke for the dormant `fix/mechanic-lagrange-v426`
   branch** — the post-S19 picker (state.md §"Next-iteration picker"
   item 4) flagged the dormant branch as a follow-up; that's a separate
   iteration's work. This STATE-SYNC observes its dormancy (18 days
   since 2026-05-16 last commit at SHA `203f991256b` per
   `git log --all`) but does not act on it.
5. **No `problem.md` or `knowledge.md` edits** — those files were
   reviewed and are still substantively correct; the slug's mathematical
   framing has not changed.
6. **No `relatedProofs` or `references` edits** in the JSON — these
   fields are unchanged since the 2026-05-12 slug creation.

## Honest framing / self-audit

* **STATE-SYNC, not ACT.** No new mathematics; no new Lean code; no new
  build verification. Realigns the JSON to what's already merged on
  origin/main.
* **18-day registry lag is a known pattern.** State.md has been the
  source of truth between 2026-05-16 and now because the S19 ACT
  PR (#21124) didn't include a JSON sync, and the orphan-registration
  PR (#21970) touched only the gallery-side meta.json, not the
  research registry JSON. STATE-SYNC iterations are the gallery's
  standard pattern for absorbing these drift gaps (cf.
  `sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md`
  for an earlier STATE-SYNC on this same slug).
* **Picker for next iteration unchanged.** S6b ACT (g(6) ≥ 73, k=6
  port) is the highest-readiness next move. S7 ACT (g(7) ≥ 143, k=7
  port) is also unblocked. Mechanic poke for `fix/mechanic-lagrange-v426`
  branch is the next-best move if the gallery owner wants the parent
  unblocked (would in turn unblock S4 / S6).

## What the next researcher should do

* **Option A (recommended for math progress)**: S6b ACT — paste-port S3
  ACT recipe at k=6 with witness `703 = 11·64 + 63` to a new file
  `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG6.lean` (~180
  LOC, ~30 min Docker). Verbatim recipe is in the S3 ACT memo
  `sessions/2026-05-14-s3-act-g4-counting-omega.md` with k-port table.
* **Option B (recommended for infrastructure progress)**: Mechanic poke
  — open a fresh Mechanic PR re-applying S18 PREP §3 paste-ready fixes
  to `proofs/Proofs/LagrangeFourSquares.lean`. The dormant branch
  `fix/mechanic-lagrange-v426` already has the commit at
  `203f991256b`; if that branch is no longer reachable, the fixes can
  be re-derived from PR #19546's session memo §3.
* **Option C (lower-priority, doc-only)**: full state.md rewrite
  collapsing the historical S1–S19 ledger to a digest, since the file
  is now ~25 KB of largely-duplicated content. Defer until S6b/S7 ACTs
  ship.
