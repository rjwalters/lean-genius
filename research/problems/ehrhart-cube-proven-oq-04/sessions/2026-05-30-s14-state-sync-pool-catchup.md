# S14 STATE-SYNC — Candidate-Pool Catchup Post-S13 Verified Confirmation

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: S14 STATE-SYNC (doc-only; closes candidate-pool drift left by S13)
**Depends on**:
- PR #19101 (S9 ACT mechanic fix, MERGED 2026-05-15T22:59:15Z, commit `be08fef58bb`)
- PR #19334 (S12 STATE-SYNC build-verified confirmation, MERGED 2026-05-15)
- S13 STATE-SYNC research-JSON catchup PR (2026-05-15, set research-JSON `phase: VERIFIED`)

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged from S11/S12/S13). Pin verified at S14 write time via `proofs/lake-manifest.json`.

**Base commit**: `8ae064a390d` (current `origin/main` HEAD at S14 write time).

## 1. Purpose

S13 STATE-SYNC corrected the research-JSON drift (`phase: SCAFFOLDED → VERIFIED`, `iteration: 7 → 13`, etc.). At S14 claim time (2026-05-30), one drift surface remains: the **candidate-pool entry** in `.lean/state/candidate-pool.json` still shows

```json
{
  "id": "ehrhart-cube-proven-oq-04",
  "status": "available",
  "notes": "AVAILABLE"
}
```

The pool is auto-generated from `research/db/knowledge.db` (per the file's `source` field) and gitignored, so it can drift indefinitely from the merged source-of-truth slug state until either (a) the DB regeneration script catches up or (b) a researcher manually marks the slug `completed` via `claim-problem.sh update`. S13 STATE-SYNC did neither — it only touched the tracked `src/data/research/problems/ehrhart-cube-proven-oq-04.json` file.

This S14 STATE-SYNC closes the candidate-pool drift by invoking

```bash
./scripts/research/claim-problem.sh update ehrhart-cube-proven-oq-04 completed
```

which:
1. Sets `.candidates[].status = "completed"` in the gitignored `.lean/state/candidate-pool.json` (local-only, will persist until next DB regen).
2. Drops a completion-signal file under `.loom/signals/completions/` (untracked; consumed by the seeker/stats pipeline).

Both side effects are outside the tracked tree. The **tracked** S14 deliverables are the three doc-only edits captured in this PR (session memo + state.md head + research-JSON iteration bump).

## 2. Build inheritance

| File | LOC @ base | Axioms | Sorries | Build status |
|---|---|---|---|---|
| `proofs/Proofs/EhrhartCubeProvenOQ04.lean` | 775 | 0 | 0 | verified (S9 ACT PR #19101, 7743 jobs, ~10s warm-cache at v4.26.0) |
| `proofs/Proofs/EhrhartCubeProven.lean` | (parent, untouched) | 0 | 0 | verified (parent slug `verified`) |

No Lean source edits in this PR. Build inheritance from `origin/main` HEAD is unconditional. Verified at S14 write time:

- `wc -l proofs/Proofs/EhrhartCubeProvenOQ04.lean` → **775** (matches research-JSON `leanFiles[1].lineCount: 775` post-S13).
- `grep -c "^axiom " proofs/Proofs/EhrhartCubeProvenOQ04.lean` → **0**.
- `grep -c "^[[:space:]]*sorry" proofs/Proofs/EhrhartCubeProvenOQ04.lean` → **0** (the 2 `sorry` matches in the file body are inside comments at lines 15 and 66).
- `grep -cE "^theorem |^lemma " proofs/Proofs/EhrhartCubeProvenOQ04.lean` → **30** (matches meta.json `theoremCount: 30`).

## 3. Per-field S14 deltas

### `state.md` (this PR — head update only)

| Field | Pre-S14 | Post-S14 |
|---|---|---|
| `Phase` line | `VERIFIED (S9 ACT mechanic fix PR #19101 merged …; S13 STATE-SYNC absorbs research-JSON drift)` | `VERIFIED (S14 STATE-SYNC absorbs candidate-pool drift)` |
| `Since` line | `2026-05-15T22:59:15Z (S9 ACT mechanic fix merge — first clean Docker baseline)` | unchanged (S9 ACT remains the canonical verification timestamp) |
| `Iteration` | `13` | `14` |
| `Researcher` | `researcher-12 (S13 STATE-SYNC — research-JSON catchup)` | `researcher-1 (S14 STATE-SYNC — candidate-pool catchup)` |
| Current Focus § | S13 narrative + per-field drift table | prepended S14 narrative; S13 narrative preserved under "Prior STATE-SYNC: S13" |

### `src/data/research/problems/ehrhart-cube-proven-oq-04.json`

| Path | Pre-S14 | Post-S14 |
|---|---|---|
| `.currentState.phase` | `"VERIFIED"` | `"VERIFIED"` (unchanged) |
| `.currentState.since` | `"2026-05-15T22:59:15Z"` | unchanged |
| `.currentState.iteration` | `13` | `14` |
| `.currentState.focus` | S13 STATE-SYNC research-JSON narrative | rewritten to S14 STATE-SYNC candidate-pool narrative |
| `.currentState.nextAction` | "S14 (OPTIONAL Mathlib upstream) / S15 …" | rewritten — S14 now done; S15/S16/S17 remain optional |
| `.currentState.attemptCounts.total` | `13` | `14` |
| `.lastUpdate` | `"2026-05-15T23:30:00Z"` | `"2026-05-30T07:30:00Z"` (write time) |

### `.lean/state/candidate-pool.json` (UNTRACKED — gitignored, side effect of S14)

| Field | Pre-S14 | Post-S14 |
|---|---|---|
| `.candidates[id=ehrhart-cube-proven-oq-04].status` | `"available"` | `"completed"` |

This change is local-only and not part of the committed diff. Reproduce on any worktree by running the same `claim-problem.sh update … completed` command.

## 4. Conflict-free guarantees

This PR touches exactly three tracked files:

- `research/problems/ehrhart-cube-proven-oq-04/sessions/2026-05-30-s14-state-sync-pool-catchup.md` (new file, this note)
- `research/problems/ehrhart-cube-proven-oq-04/state.md` (head fields + Current Focus rewrite; body preserved verbatim under "Prior STATE-SYNC: S13" heading)
- `src/data/research/problems/ehrhart-cube-proven-oq-04.json` (7 field updates per §3; no structural changes)

No Lean source edits, no `meta.json` edits (already current per S12), no sibling-slug edits, no parent-slug edits, no shared-config edits. Pure orthogonal STATE-SYNC.

Conflict-risk window: the only concurrent claim that could touch the same files is another agent claiming `ehrhart-cube-proven-oq-04` — but the claim-script lock prevents that.

## 5. Why S14 is the right move

The slug has been **VERIFIED** in the gallery (`meta.status: verified`) and **VERIFIED** in the research-JSON (`currentState.phase: VERIFIED`) since 2026-05-15. The candidate-pool entry, however, remained `available` for two weeks, which:

1. **Allowed re-claims by random selection.** The `claim-random` command pulls from `.candidates[].status != "completed"` — so an `available` entry on a fully-verified slug keeps re-entering the rotation. This S14 was itself such a re-claim (researcher-1's stale claim on `cantors-theorem-oq-01-oq-03` was released for the same reason — that slug is also `available` in the pool despite being verified since S2 2026-05-12).
2. **Distorted pool-status snapshots.** The seeker logs "101/15 available" or similar; verified-but-unmarked slugs inflate the available-count and shift seeker prioritization away from genuinely new candidates.
3. **Held a slot in the active-claims registry.** The stale claim (`STALE, RICH, expires: 2026-05-30T08:30:41Z` per S14 claim time) needed a release-or-complete decision.

S14 marks the slug as `completed`, releases the claim implicitly via the script, and drops a completion signal — the canonical close-out trio. The seeker can now safely skip this slug on future `claim-random` runs.

## 6. Out of scope for S14

- **S15 (REGRESSION CHECK)** — prospective; only triggers on Mathlib v4.27.0+ bumps. The current pin remains v4.26.0 and the S8 inventory in `state.md` §Blockers is the surgical-fix reference if the 7-error surface recurs.
- **S16 (POLYNOMIAL-DEGREE COROLLARY)** — optional `cubeHStarPoly_natDegree` (~25-40 LOC); requires Docker build access and is not blocking slug closure.
- **S17 (HERMIT CROSS-GALLERY SCAN)** — flagged for Hermit on the `rw [pow_two, pow_two] at *` v4.26.0 no-op pattern. Out of scope for any single researcher slug.
- **S14-Mathlib upstream** — the larger Mathlib PR (`Nat.eulerianNumber`, `Nat.worpitzky_identity_cube`, etc.) listed as the original "S14" in S13's nextAction is renamed `S18-Mathlib` to keep this state-sync S14 distinct. The contribution-map session memo (`sessions/2026-05-15-s12-state-sync-build-verified.md` §7) remains the reference for that future work.

## 7. Sign-off

S14 STATE-SYNC closes the candidate-pool drift in one doc-only PR. Slug `ehrhart-cube-proven-oq-04` is **closed**: gallery `verified`, research-JSON `VERIFIED`, pool `completed`, claim released, completion signal dropped. No further work is required for slug resolution itself.
