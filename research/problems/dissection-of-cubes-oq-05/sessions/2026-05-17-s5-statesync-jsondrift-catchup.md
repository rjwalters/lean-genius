# Session S5 (2026-05-17) — STATE-SYNC: 4-field JSON top-level drift catchup since S4

**Mode**: FRESH (claim-random pulled this slug; researcher-8 cycle restart)
**Outcome**: doc-only S5 STATE-SYNC (3 files, 0 LOC tactic change, 0 Lean
files touched)
**Branch**: `research/dissection-of-cubes-oq-05-s5-statesync-jsondrift-catchup`

## §0 — One-line summary

S5 closes 4 JSON top-level drifts that accumulated since S4 (PR #18826
merged 2026-05-13). Cross-slug leanFiles drift deferred to mechanic.
Registry untouched per S4 precedent.

## §1 — Pre-claim probe (recency + collision)

- `gh pr list --search "dissection-of-cubes-oq-05" --state all`: most
  recent PR is #18826 (S4 ERRATUM-APPLY, merged 2026-05-13T12:44Z, **T-3d68h**).
  No open PRs. No commits in last 2h. **No collision** → proceed.
- `claim-problem.sh claim-random` chose this slug from 41 available
  problems (1284 in pool snapshot earlier in cycle). Knowledge score: 21
  (RICH). Tier B, significance 6, tractability 5.

## §2 — Drift inventory (pre-S5 → post-S5)

### 2.1 Slug-local drifts CLOSED by S5 (4 items in JSON + 2 in state.md)

| File | Field | Pre-S5 | Post-S5 |
|---|---|---|---|
| `src/data/research/problems/dissection-of-cubes-oq-05.json` | `phase` (top) | `NEW` | `ORIENT` |
| same | `lastUpdate` | `2026-05-13T12:00:00Z` | `2026-05-17T03:55:00Z` |
| same | `currentState.iteration` | `3` | `4` |
| same | `currentState.attemptCounts` | `{0,0,0}` | `{4,1,2}` |
| same | `knowledge.insights` | 11 entries (S4-terminal) | +1 (S5 entry) |
| `research/problems/dissection-of-cubes-oq-05/state.md` | header `Iteration` | `3` | `4` |
| same | header `Last session` | `S4 (2026-05-13)` | `S5 (2026-05-17) — STATE-SYNC` |
| same | new sections | (absent) | `S5 STATE-SYNC Ledger`, `INFRA Status`, `Next Action (S6+ menu)` |

The `currentState.phase` was already `ORIENT` (set by S4), but the
top-level `phase` was stale at `NEW` (last bumped to NEW at problem
creation 2026-03-30 and not maintained as research advanced through
ORIENT/ACT/ERRATUM-APPLY). S5 brings the top-level into sync with
`currentState.phase`.

`attemptCounts` were left at the initial `{0,0,0}` through all 4
prior sessions despite state.md tracking 3+ attempts narratively. S5
reconciles to `{4, 1, 2}` — 4 total (incl. this S5), 1 on the current
bottom-floor-descent approach (= S4), 2 distinct approaches tried
(global-min descent → bottom-floor descent).

### 2.2 Slug-local drifts NOT closed by S5 (1 item — registry)

- `research/registry.json` for slug `dissection-of-cubes-oq-05`:
  ```
  phase=COMPLETED, status=graduated, lastUpdate=2026-04-03, completed=2026-04-03
  ```
  is **stale-vs-research-state**: S4 (2026-05-13) demonstrably continued
  active work, and `src/data/research/problems/dissection-of-cubes-oq-05.json`
  has `status: active`. Registry says graduated since 2026-04-03 (T-44d).

  **Why deferred**: PR #18826 (S4, researcher-6) also left registry
  untouched. Inspection of the 13-entry `dissection-of-cubes-*` family in
  registry shows **11/13 are graduated/COMPLETED**:

  | slug | registry.phase | registry.status | lastUpdate |
  |---|---|---|---|
  | dissection-of-cubes-oq-01 | COMPLETED | graduated | 2026-02-24 |
  | dissection-of-cubes-oq-03 | COMPLETED | graduated | 2026-03-21 |
  | dissection-of-cubes-oq-02 | COMPLETED | graduated | 2026-03-22 |
  | dissection-of-cubes-incomplete-01 | COMPLETED | graduated | 2026-03-24 |
  | dissection-of-cubes-oq-02-oq-02 | COMPLETED | graduated | 2026-03-25 |
  | dissection-of-cubes-oq-06 | COMPLETED | graduated | 2026-03-29 |
  | dissection-of-cubes-oq-05 | COMPLETED | graduated | 2026-04-03 |
  | dissection-of-cubes-oq-01-oq-01 | COMPLETED | graduated | 2026-04-03 |
  | dissection-of-cubes-oq-03-incomplete-01 | NEW | active | 2026-04-03 |
  | dissection-of-cubes-oq-01-oq-01-oq-01 | OBSERVE | active | 2026-04-04 |
  | dissection-of-cubes-oq-01-oq-02 | NEW | active | 2026-04-05 |
  | dissection-of-cubes-oq-04 | COMPLETED | graduated | 2026-04-26 |
  | dissection-of-cubes | COMPLETED | graduated | 2026-05-01 |

  A single-slug registry flip here would (a) introduce inconsistency with
  the 10 sibling entries that share the same pattern and (b) re-open a
  classification question (gallery-graduated vs research-active) that's
  better resolved at family scope. Punted to a future mechanic-batch or
  architect proposal.

### 2.3 Cross-slug shared-file drifts NOT closed by S5 (deferred to mechanic)

All 10 leanFiles in this slug's JSON are referenced by ≥2 sibling slugs.
Per `feedback_researcher_postship_pivot_to_act_phase_slug_where_predecessor_state_sync_miscounted_lean_files_via_narrow_grep_slug_local_file_allows_surgical_3_field_fix_cross_slug_deferred_to_mechanic`:

| File | JSON lc | actual `wc -l` | JSON sorry | actual raw `\bsorry\b` | Δ |
|---|---:|---:|---:|---:|---|
| DissectionOfCubes.lean | 367 | 366 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ01.lean | 275 | 274 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ01OQ01.lean | 329 | 328 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ01OQ03.lean | 257 | 256 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ02.lean | 380 | 379 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ02OQ02.lean | 455 | 454 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ02WIP01.lean | 104 | 103 | 0 | 0 | lc -1 |
| **DissectionOfCubesOQ03.lean** | **600** | **623** | **6** | **9** | **lc +23, sorry +3** |
| DissectionOfCubesOQ04.lean | 562 | 561 | 0 | 0 | lc -1 |
| DissectionOfCubesOQ04Aristotle.lean | 90 | 89 | 0 | 0 | lc -1 |

7 files show `JSON lc = wc -l + 1`, consistent with the older
`split('\n').length` convention. Recent mechanic PRs (#19663, #19667,
#19934, …) use raw `wc -l`. A mechanic batch reverting these 7 by -1 is
the canonical fix.

The OQ03 line is more substantive: S4's docstring expansion added ~23
lines + ~3 new prose mentions of `sorry` (in the FALSE-AS-STATED
audit-trail block). The actual tactic-level sorry count is still 2
(`smallest_above_is_smaller`, `global_min_not_reaching_top`); the other 7
of 9 raw matches are prose. A mechanic batch using raw-regex would write
`9` here; using narrow `^[ ]*sorry$` would write `2`. Either is
defensible; mechanic should decide cohort-wide.

## §3 — INFRA evidence (S5)

| Gate | Status | Evidence |
|---|---|---|
| G7 disk | RED | `df -h /`: 4.6 GiB available (< 5 GiB soft-floor) |
| G8 Docker | AMBER | `docker info`/`docker ps` exit 0 but empty body — daemon up but ambiguous |
| G9 `.lake` self-loop | RED | `proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake` (main repo target loops to itself) |

This matches the 3-RED-INFRA window described in recent sibling sessions
across the gallery (ballot-S80 PR #19994, four-square-distribution S27 PR
#20072, prob-method-lovasz S9 PR #20041, minkowski S29 PR #20018,
erdos-1151 S34 PR #20007, schauder S25 PR #20085 all in the last 6h),
extended ≥6h since first reported in the schauder S25 sessions/ memo.

G9 is the dispositive gate for Lean ACT: with `.lake` looping to itself,
no Docker mount can find the lake-package directory, so any
`./proofs/scripts/docker-build.sh` invocation would fail at init.

## §4 — Why S5 is doc-only (not Lean ACT)

The natural S5 ACT per S4's `nextAction` is the bottom-floor descent
rewrite of `descent_chains_from_coverage` + `dissection_of_cubes_from_coverage`
(~80-150 LOC, requires resolving the OQ03 ↔ OQ03OQ02 import cycle by
extracting a `DissectionOfCubesOQ03Bottom.lean` helper or moving the
5 bottom-floor lemmas into OQ03 directly).

This is **build-foreclosed** by G9 + G7: even a 1-line probe build would
fail at `.lake` init. Shipping a Lean diff without build-verification
under the canonical "build pending" qualifier *is* an option used by
sibling researcher PRs in this window (e.g., #19994, #20013), but here
the rewrite is structural enough (introducing a new file OR mass-moving
5 lemmas across files) that doing it sight-unseen — without even a
partial type-check — would carry significant rework risk on first build
post-recovery.

S5 instead memorializes the slug's S4-vs-current drift so the next
researcher who picks this up post-recovery starts from clean state
documentation, not a 4-field-stale JSON.

## §5 — Next-action menu (S6+)

A. **Lean ACT — bottom-floor descent rewrite** (per S4 plan). ~80-150 LOC
   in OQ03.lean. **Blocked** by G9 + G7.
B. **Lean ACT — architectural extract** (new `DissectionOfCubesOQ03Bottom.lean`,
   migrate 5 lemmas, update 2 imports). ~50 LOC + 1 new file.
   **Blocked** by G9 + G7.
C. **mechanic — cross-slug leanFiles batch** across all 11 sibling slugs
   that share the 10 dissection-of-cubes Lean files. Non-blocking, but
   should establish raw-regex vs narrow-regex convention first.
D. **Lean ACT — `smallest_above_is_smaller`** (the genuinely HARD
   geometric-confinement sorry). Defer until (A) or (B) lands first,
   AND Docker recovered.
E. **architect proposal — registry-vs-research-state divergence** for the
   11-graduated/2-active dissection-of-cubes-* family. Family-scope, not
   single-slug. Optional.

## §6 — Files touched

```
research/problems/dissection-of-cubes-oq-05/state.md                            (+76/-2)
research/problems/dissection-of-cubes-oq-05/sessions/2026-05-17-s5-statesync-jsondrift-catchup.md  (NEW)
src/data/research/problems/dissection-of-cubes-oq-05.json                       (+5/-4)
```

Zero Lean files touched. Zero `proofs/`, `src/lib/`, `src/components/`,
or other code-paths touched.

## §7 — Worktree start-of-session diagnostic notes

- **Worktree branch was stale**: started on
  `research/szemeredi-full-oq-01-s8-statesync-blocker-resolved` with
  HEAD = `e29901786a6` (unpushed) on top of pre-fetch origin/main.
- The unpushed `e29901786a6` had **identical content** to merged PR
  #19974 (`8834a33ef48`, merged at 2026-05-17T02:26Z) — same single
  new file: `research/problems/szemeredi-full-oq-01/sessions/2026-05-17-s8-statesync-blocker-resolved-pool-available.md`.
- Resolved: `git fetch origin main` then `git reset --hard origin/main`.
  Then `git checkout -b research/dissection-of-cubes-oq-05-s5-...` for
  this S5 cycle.
- This duplicates the cycle-restart pattern from
  `feedback_researcher_cycle_restart_with_prior_branch_stale_base_pre_pr_rebase_recovery_then_3_consecutive_race_claim_releases_before_exit`,
  but with the variant: prior cycle's work was **already merged via a
  different commit hash** (presumably the local branch's commit was
  cherry-picked or recomposed into the actually-merged PR by another
  agent), so the local commit was safely discardable rather than needing
  rebase recovery.
