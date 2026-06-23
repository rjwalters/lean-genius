# Session 5 (2026-05-16) — STATE-SYNC: pool drift catch-up

**Mode**: STATE-SYNC (doc-only, no Lean source changes)
**Agent**: researcher-4
**Branch**: `research/greens-oq01x4-oq01-s5-state-sync-pool-drift-1<timestamp>`
**Outcome**: pool sync applied + slug-local files refreshed; slug remains COMPLETED.

## Context

`claim-problem.sh claim-random` returned `greens-theorem-oq-01-oq-01-oq-01-oq-01`
(MODERATE tier, knowledge score 15). On inspection, the slug was already fully
discharged at iteration 4 (S4 ACT) but the candidate pool, the research JSON
`currentState.iteration`/`lastUpdate`, and the slug-local `problem.md` Status
header had not been synchronized after the discharging PR (#16934) merged.

This session is a doc-only catch-up: no Lean source touched, no Docker build
required, no axiomatic content changed.

Pre-flight note: a separate uncommitted edit in the main-repo working tree
(`/Users/rwalters/GitHub/lean-genius/src/data/research/problems/<slug>.json`)
showed the JSON `leanFiles[GreensTheoremOQ01OQ01OQ01OQ01.lean]` block at the
pre-fix values `lineCount: 517 / theoremCount: 4 / axiomCount: 1`. That working
tree is on an unrelated researcher branch (`research/ballot-...`) and not on
origin/main. The actual origin/main HEAD `ecb47b35601` already has the correct
values `lineCount: 516 / theoremCount: 10 / axiomCount: 0` for that block
(verified by `git show origin/main:src/data/research/problems/<slug>.json`).
This PR therefore does NOT touch those fields — they are already correct.

## Verification of COMPLETED status (origin/main HEAD = `ecb47b35601`)

### Lean source — `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean`

```
wc -l                                           → 516
grep -cE "^axiom\b"                             → 1   (false positive — see below)
grep -cE "^[[:space:]]*sorry([[:space:]]|$)"    → 0
grep -cE "^(theorem|lemma|...)\b"               → 10
```

The single `^axiom\b` hit is at line 513 inside a `/--  ... -/` docstring block:

```
512: **Impact**: Main theorem structure is now complete via `swap_induction_on`. Eliminates
513: axiom once both remaining sorries are resolved.
514: -/
```

This is comment text, not a real `axiom` declaration. `meta.json` correctly reports
`axiomCount: 0`. No structure-encoded assumptions (no `structure ... where` blocks
in this file).

### Parent file — `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean`

```
grep -nE "^axiom\b"   →   (no matches)
```

The previously-stated parent axiom `iteratedIntervalIntegral_order_independent` was
retired in PR #16934 (commit `7292d5776be`, merged 2026-05-08). Lines 250-257 now
contain a tombstone docstring noting the axiom was removed because it was unused
locally and a real theorem of the same statement exists downstream.

### Gallery meta — `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json`

| Field | Value |
|-------|-------|
| `status` | `verified` |
| `badge` | `verified` |
| `sorries` | 0 |
| `axiomCount` | 0 |
| `lineCount` | 516 |
| `theoremCount` | 10 |
| `mathlib_version` | `4.26.0` |

All numbers match the Lean source. No drift.

### Open PRs

`gh pr list --search "greens-theorem-oq-01-oq-01-oq-01-oq-01"` → `[]`. No
in-flight PRs touching this slug. Three open PRs on the sibling slug
`greens-theorem-oq-01-oq-01-oq-02-oq-01` (#17822 / #17838 / #17840) all touch
`GreensTheoremOQ01OQ01OQ02OQ01.lean` only, not our child file.

## Drift Inventory (per source-of-truth)

| Source | Field | Pre-S5 | Post-S5 (this PR) | Notes |
|--------|-------|--------|---------|-------|
| `.lean/state/candidate-pool.json` | `status` | `in-progress` | `completed` | Applied by `claim-problem.sh update`; file is gitignored — no commit needed. |
| `src/data/research/problems/<slug>.json` | `currentState.iteration` | 2 | 5 | state.md was at 4; +1 for this S5 STATE-SYNC. |
| `src/data/research/problems/<slug>.json` | `lastUpdate` | `2026-05-07T17:00:00.000Z` | `2026-05-16T09:30:00.000Z` | 9-day refresh. |
| `src/data/research/problems/<slug>.json` | `currentState.focus` | (unchanged) | + S5 STATE-SYNC summary appended | Documents pool sync + build inheritance from PR #16934. |
| `src/data/research/problems/<slug>.json` | `currentState.nextAction` | `"None."` | + deferred-cleanup note | Stale Lean docstring at lines 488-513; pure-comment, Docker-blocked. |
| `research/problems/<slug>/state.md` | `Iteration` | 4 | 5 | Matches JSON. |
| `research/problems/<slug>/state.md` | `Phase` annotation | `COMPLETED` | `COMPLETED (STATE-SYNC catch-up applied 2026-05-16)` | Audit trail. |
| `research/problems/<slug>/state.md` | Follow-Up section | unresolved oq-01 | struck-through + linked to PR #16934 | Resolved follow-up. |
| `research/problems/<slug>/state.md` | (new) Pool/JSON Drift Fixed in S5 | — | new section | Enumerates per-field changes. |
| `research/problems/<slug>/problem.md` | `Status` | `Active` | `Completed (S4 ACT PR #16934, 2026-05-07; S5 STATE-SYNC pending 2026-05-16)` | Was stale. |

**Not in drift on origin/main HEAD** `ecb47b35601` (so this PR leaves them alone):
- `src/data/research/problems/<slug>.json` `leanFiles[GreensTheoremOQ01OQ01OQ01OQ01.lean]`:
  `lineCount: 516`, `theoremCount: 10`, `axiomCount: 0`, `sorryCount: 0` — all correct.
  (The pre-fix values 517/4/1 visible in the main-repo working tree are uncommitted
   and not on origin/main.)
- `src/data/research/problems/<slug>.json` `phase`, `status`, `currentState.phase`,
  `currentState.blockers`, `knowledge.progressSummary` — all already reflect COMPLETED.
- Gallery meta.json — already accurate.
- Parent file axiom-elimination — done in PR #16934.

## Build-Inheritance Argument

No Lean source files are modified in this PR. The build state on origin/main
(commit `ecb47b35601`) is therefore inherited unchanged:

- Child file `GreensTheoremOQ01OQ01OQ01OQ01.lean` (516 LOC, 10 theorems, 0 axioms,
  0 sorries) builds clean on `mathlib_version 4.26.0` per the most recent merged
  PR touching it (#16934 — re-builds the parent module after axiom retirement;
  child file is a downstream import of the parent).
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (rev in
  `proofs/lake-manifest.json`) unchanged since pre-S4.
- Doc-only edits (state.md / problem.md / sessions/ / research JSON) do not
  affect `lake build` output.
- Host disk at 100% capacity / 6.9 Gi avail (`df -h /System/Volumes/Data`)
  precludes `docker-build.sh` re-verification, but no re-verify is needed
  for doc-only changes.

## Pool Sync Action (already applied)

```bash
RESEARCHER_ID=researcher-4 \
  scripts/research/claim-problem.sh update \
  greens-theorem-oq-01-oq-01-oq-01-oq-01 completed
# → "Updated greens-theorem-oq-01-oq-01-oq-01-oq-01 status to: completed"
```

The candidate-pool.json `notes` field still reads `"IN-PROGRESS"` (free-form,
not load-bearing). Leaving as-is — the `status` field is the source of truth
for `claim-random` filtering.

## Deferred (Not in This PR)

- **Stale Lean docstring cleanup** at `GreensTheoremOQ01OQ01OQ01OQ01.lean`
  lines 488-513. The block-comment still says "Remaining sorries (2 total)"
  and "Eliminates axiom once both remaining sorries are resolved" — both
  historically satisfied. Pure-comment edit, but per project policy any change
  to a Lean source under `proofs/Proofs/` requires Docker re-verify before
  merge. Host disk is currently at 100% capacity; deferring to a future cycle
  when Docker is restored. Filed as an optional follow-up in state.md.

- **candidate-pool.json `notes` field cleanup** (`"IN-PROGRESS"` → something
  like `"COMPLETED: axiom retired in PR #16934"`). Free-form, low-value,
  skipped to keep PR scope minimal. Future Seeker / Curator pass may sweep.

## References

- PR #16248 (2026-05-06): "prove swap_outer_two and 2D order independence"
- PR #16292 (2026-05-06): "prove iteratedIntervalIntegral_perm_tail"
- PR #16323 (2026-05-07): "prove main theorem via swap_induction_on (1 sorry remaining)"
- PR #16359 (2026-05-07): "prove iter_integral_swap_zero k≥2, fix Mathlib API drift"
- PR #16385 (2026-05-07): "audit: sync sorries 1→0, lineCount 471→516"
- PR #16405 (2026-05-07): "mark completed, promote to verified"
- PR #16934 (2026-05-08): "retire iteratedIntervalIntegral_order_independent axiom" (S4 ACT — discharging follow-up)

## Files Touched

1. `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/state.md` — iteration 4→5, S5 STATE-SYNC banner, follow-up strike-through, Pool/JSON Drift section.
2. `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/problem.md` — Status: Active → Completed.
3. `research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01/sessions/2026-05-16-s5-state-sync-pool-drift-catchup.md` — new (this file).
4. `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-01-oq-01.json` — `currentState.iteration: 2→5`, `currentState.focus` appended, `currentState.nextAction` annotated, `lastUpdate: 2026-05-07→2026-05-16`.

Zero Lean source edits. Zero `meta.json` edits. Zero `knowledge.md` edits (already
accurate — `Status: completed`, `Phase: COMPLETED`).
