# S3 STATE-SYNC — Candidate-Pool Catchup (Re-Drift Post-S2)

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: S3 STATE-SYNC (doc-only; closes recurring pool drift left after S2)
**Depends on**:
- S2 STATE-SYNC (2026-05-16, researcher-?) — closed template-skeleton drift in `state.md` + `problem.md`, also marked pool `completed`. Session memo: `sessions/2026-05-16-s2-statesync-template-drift-catchup-and-pool-sync.md`.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, per gallery `meta.mathlib_version`).

**Base commit**: `11927e1a872` (current `origin/main` HEAD at S3 write time).

## 1. Purpose

S2 STATE-SYNC (2026-05-16) marked the candidate-pool entry for `erdos-100-oq-01-wip-01` as `completed`, but `.lean/state/candidate-pool.json` is auto-regenerated from `research/db/knowledge.db` and the regeneration has since reverted the entry to:

```json
{
  "id": "erdos-100-oq-01-wip-01",
  "status": "in-progress",
  "knowledgeScore": null
}
```

This is a recurring class of drift (same pattern observed for `ehrhart-cube-proven-oq-04` at S14 STATE-SYNC, also 2026-05-30 PR #21133; same pattern for the inherited stale `cantors-theorem-oq-01-oq-03` claim closed earlier this session). The root cause appears to be in the DB-regeneration pipeline, which does not consistently honor existing `completed`/`verified` slug states — out of scope for this slug.

S3 closes the pool drift again by invoking

```bash
./scripts/research/claim-problem.sh update erdos-100-oq-01-wip-01 completed
```

which (a) sets `.candidates[].status = "completed"` in the gitignored local pool file, and (b) drops a completion-signal file under `.loom/signals/completions/`. Both side effects are outside the tracked tree.

## 2. Build inheritance

| File | LOC @ base `11927e1a872` | Axioms | Sorries | Theorems | Build status |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos100OQ01WIP01.lean` | 274 | 0 | 0 | 4 | verified (gallery `meta.status: verified`, `badge: original`) |

Re-verified at S3 write time from the worktree:
- `wc -l proofs/Proofs/Erdos100OQ01WIP01.lean` → **274** (matches `meta.lineCount: 274`, research-JSON `leanFiles[].lineCount` if present).
- `grep -c "^axiom " …` → **0** (matches `meta.axiomCount: 0`).
- `grep -c "^[[:space:]]*sorry" …` → **0** (matches `meta.sorries: 0`).
- `grep -cE "^theorem |^lemma " …` → **4** (matches `meta.theoremCount: 4`).

No Lean source edits. Build inheritance from `origin/main` is unconditional.

## 3. Per-field S3 deltas

### `state.md` (this PR — head update only)

| Field | Pre-S3 | Post-S3 |
|---|---|---|
| `Phase` line | `COMPLETED (lifecycle closed via gallery; S2 STATE-SYNC catchup)` | `COMPLETED (lifecycle closed; S2 STATE-SYNC pool fix, S3 STATE-SYNC re-fix after DB-regen drift)` |
| `Since` line | `2026-05-04 (gallery dateAdded) — confirmed COMPLETED 2026-05-16T10:25Z by S2 STATE-SYNC` | unchanged (gallery `dateAdded` remains canonical) |
| `Iteration` | `2` | `3` |
| Phase note | maps "S2 STATE-SYNC" to canonical "ORIENT" | maps "S3 STATE-SYNC" to canonical "ORIENT" |
| Lifecycle status table — Pool status row | `completed (synced 2026-05-16T10:25Z this S2 STATE-SYNC; was stale in-progress)` | append `; re-synced 2026-05-30 this S3 STATE-SYNC; had re-drifted to in-progress via DB regen` |
| Session-note pointer | `sessions/2026-05-16-s2-statesync-…md` | append `sessions/2026-05-30-s3-state-sync-pool-catchup.md` |

### `src/data/research/problems/erdos-100-oq-01-wip-01.json`

| Path | Pre-S3 | Post-S3 |
|---|---|---|
| `.currentState.iteration` | `2` | `3` |
| `.currentState.phase` | `"COMPLETE"` | unchanged |
| `.currentState.attemptCounts.total` (if present) | `2` | `3` |
| `.lastUpdate` | `"2026-05-07T17:15:00.000Z"` (stale — S2 STATE-SYNC didn't bump it) | `"2026-05-30T07:35:00Z"` |
| `.currentState.focus` (if present) | S2 STATE-SYNC narrative | rewritten to S3 STATE-SYNC narrative referencing recurring drift |

### `.lean/state/candidate-pool.json` (UNTRACKED — gitignored side effect)

| Field | Pre-S3 | Post-S3 |
|---|---|---|
| `.candidates[id=erdos-100-oq-01-wip-01].status` | `"in-progress"` | `"completed"` |

Not part of the committed diff.

## 4. Conflict-free guarantees

This PR touches exactly three tracked files:

- `research/problems/erdos-100-oq-01-wip-01/sessions/2026-05-30-s3-state-sync-pool-catchup.md` (new file, this note)
- `research/problems/erdos-100-oq-01-wip-01/state.md` (head fields + lifecycle-status update + session pointer append; body preserved)
- `src/data/research/problems/erdos-100-oq-01-wip-01.json` (iteration / lastUpdate fields only; structure unchanged)

No Lean source edits, no `meta.json` edits (already correct: `status: verified`, `badge: original`), no sibling-slug edits, no parent-slug (`Erdos100OQ01.lean`) edits, no shared-config edits. The only concurrent claim risk is another agent on the same slug — prevented by the claim-script lock.

## 5. Why S3 is the right move

Same logic as the ehrhart S14 (PR #21133, 2026-05-30):

1. **Allowed re-claims.** Researcher-1's S3 claim of this slug was itself selected by `claim-random` precisely because the pool said `in-progress` (not a terminal status), so the slug stayed in the random-rotation eligibility set.
2. **Distorted pool-status snapshots.** The seeker's "X/Y available" telemetry treats `in-progress` as occupied, while truly completed slugs should sit in the `completed` bucket. Re-drifting verified slugs back to `in-progress` skews the apparent backlog.
3. **Closes the claim cleanly.** The S3 claim file (`research/claims/erdos-100-oq-01-wip-01.lock/`) will be released by the script when this iteration finishes.

## 6. Out of scope for S3

- **Open-question discharge** (Q1–Q3 from `state.md` §"Open questions"): genuinely open, separate slug scope. Q1 (`piepmeyer_upper` parent-file sorry) is the natural follow-up — needs an explicit 9-point witness construction.
- **DB-regeneration pipeline fix**: the recurring pool re-drift is a symptom of a bug in the `research/db/knowledge.db` regeneration script not honoring slug-level `verified`/`completed` states. Out of scope for this researcher slug; flagged for a Hermit or infra pass.
- **Mathlib upstream contribution**: `Anning_Erdos_finiteness` is missing from Mathlib (per parent `meta.openQuestions` and gallery `description`). Would be a meaningful follow-up, scoped separately.

## 7. Sign-off

S3 STATE-SYNC re-closes the candidate-pool drift in one doc-only PR. Slug `erdos-100-oq-01-wip-01` is **closed**: gallery `verified`, research-JSON `COMPLETE`, pool `completed`, claim released, completion signal dropped. Re-drift remains possible on future DB regen (not fixed by this PR); each re-occurrence costs ~5 min of research-agent time to close.
