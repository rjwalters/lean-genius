# Session 4 — 2026-05-16 — STATE-SYNC: tracking surfaces → canonical COMPLETED

**Agent**: researcher-4
**Mode**: REVISIT (forced — claim-random selected `basel-problem-oq-04-oq-03` from candidate-pool tier MODERATE+ score 14)
**Phase**: ACT/OBSERVE (stale, drifted) → **DONE/COMPLETED**
**Outcome**: doc-only reconcile after T-13d drift; **0 Lean edits, 0 gallery edits, 0 mathematical work**.

---

## §1 — Why Session 4 fires

Slug `basel-problem-oq-04-oq-03` is **terminal-verified** via merged PR #15284
(`research(basel-problem-oq-04-oq-03): prove coprime_pair_density_limit — fully
verified 0-axiom proof`) at 2026-05-03 19:11:32 +0200 (commit `f057e200358`).
Gallery `src/data/proofs/basel-problem-oq-04-oq-03/meta.json` reflects the
terminal state: `status: verified`, `badge: original`, `axiomCount: 0`,
`sorries: 0`, `lineCount: 558`, `theoremCount: 24`, `definitionCount: 1`. The
on-disk Lean file `proofs/Proofs/BaselProblemOQ04OQ03.lean` matches byte-for-byte
via `wc -l` and the canonical count regex set (memory `feedback_mechanic_batch_sync_conventions_canonical_counts...`).

Despite this canonical reality, **four tracking surfaces** drifted at the
T-13d mark:

| Surface | Stale value | Canonical value |
|---|---|---|
| `src/data/research/problems/<slug>.json` top-level `phase` | `ACT` | `DONE` |
| same `status` | `active` | `completed` |
| same `currentState.phase` | `ACT` | `DONE` |
| same `currentState.focus` | *"Proof complete (0 sorries, 2 axioms). Residual: axiom elimination."* (internally inconsistent: claims 2 axioms while progressSummary says 0) | rewrite |
| same `currentState.nextAction` | *"Read problem.md thoroughly and acquire full context."* (Session 1's OBSERVE-phase nextAction, never refreshed) | rewrite |
| same `currentState.iteration` | `2` | `3` (knowledge.md has S1+S2+S3) |
| same `currentState.attemptCounts.total` | `0` | `3` |
| same `knowledge.nextSteps[0]` | *"Docker build verification pending - proof awaits Lean type-checking"* (PR merged 2026-05-03 → built successfully) | rewrite |
| same `knowledge.nextSteps[1]` | *"If build fails: check cast issues..."* | drop / fold into optional follow-up |
| same `lastUpdate` | `2026-05-03T12:00:00.000Z` | now |
| same `leanFiles[BaselProblemOQ04OQ03.lean].lineCount` | `559` | `558` |
| same `leanFiles[BaselProblemOQ04OQ03.lean].theoremCount` | `23` | `24` |
| `research/registry.json` `phase` for slug | `OBSERVE` | `DONE` |
| same `status` | `active` | `completed` |
| same `completed` field | absent | now |
| same `lastUpdate` | `2026-04-26T07:08:53.393Z` | now |
| `research/problems/<slug>/state.md` Phase | `OBSERVE` | `DONE (COMPLETED)` |
| same Iteration | `1` | `3` |
| same Since | `2026-04-26T08:14:43+02:00` | now |
| same Next Action | *"Read problem.md thoroughly..."* | rewrite |
| `.lean/state/candidate-pool.json` `status` for slug | `available` (re-selected this S4) | `completed` (via `claim-problem.sh update completed`) |

This is the **state.md + research-JSON joint drift** sub-pattern (distinct from
the JSON-only-stale pattern documented in memory
`feedback_researcher_postship_pivot_to_long_completed_slug_with_research_json_stale_while_statemd_gallery_lean_all_canonical_inverse_of_statemd_drift_pattern_ship_3file_statesync_with_15_field_json_reconcile`).
Here **both** state.md AND JSON are stale; gallery + Lean canonical.

---

## §2 — Canonical reality verification

```
$ wc -l proofs/Proofs/BaselProblemOQ04OQ03.lean
     558 proofs/Proofs/BaselProblemOQ04OQ03.lean
$ grep -cE "^(protected |private |noncomputable )*(theorem|lemma) " proofs/Proofs/BaselProblemOQ04OQ03.lean
24
$ grep -cE "^(def|noncomputable def|opaque def) " proofs/Proofs/BaselProblemOQ04OQ03.lean
1
$ grep -c "^axiom " proofs/Proofs/BaselProblemOQ04OQ03.lean
0
$ grep -c "\bsorry\b" proofs/Proofs/BaselProblemOQ04OQ03.lean
0
$ jq '.meta | {status, badge, sorries, axiomCount, lineCount, theoremCount, definitionCount}' \
    src/data/proofs/basel-problem-oq-04-oq-03/meta.json
{
  "status": "verified",
  "badge": "original",
  "sorries": 0,
  "axiomCount": 0,
  "lineCount": 558,
  "theoremCount": 24,
  "definitionCount": 1
}
```

`558 LOC / 24 thm / 1 def / 0 sorry / 0 axiom` — agrees on three surfaces:
file content (wc/grep), gallery `meta.json`, and gallery-aligned counts. Only
the research-JSON `leanFiles[]` entry and registry/state/pool dropped behind.

---

## §3 — Edits applied this session

### 3.1 `src/data/research/problems/basel-problem-oq-04-oq-03.json` (15 field edits)

| Field | Before | After |
|---|---|---|
| `phase` (top-level) | `"ACT"` | `"DONE"` |
| `status` (top-level) | `"active"` | `"completed"` |
| `currentState.phase` | `"ACT"` | `"DONE"` |
| `currentState.since` | `"2026-05-03T12:00:00.000Z"` | `"2026-05-16T22:10:00.000Z"` |
| `currentState.iteration` | `2` | `3` |
| `currentState.focus` | stale 2-axioms claim | S4 reconcile narrative |
| `currentState.nextAction` | stale S1 OBSERVE text | "None — slug is DONE/COMPLETED" |
| `currentState.attemptCounts.total` | `0` | `3` |
| `currentState.attemptCounts.approachesTried` | `0` | `1` (Möbius+LSeries succeeded) |
| `knowledge.progressSummary` | "COMPLETE: 0 axioms..." | prefixed with S4 STATE-SYNC date + PR refs |
| `knowledge.nextSteps[0]` | "Docker build verification pending" | "None — slug COMPLETED via PR #15284" |
| `knowledge.nextSteps[1]` | "If build fails: check cast issues..." | optional follow-up: k-tuples + Mertens error bound |
| `leanFiles[BaselProblemOQ04OQ03.lean].lineCount` | `559` | `558` |
| `leanFiles[BaselProblemOQ04OQ03.lean].theoremCount` | `23` | `24` |
| `lastUpdate` | `"2026-05-03T12:00:00.000Z"` | `"2026-05-16T22:10:00.000Z"` |

### 3.2 `research/registry.json` entry for slug (4 field edits)

| Field | Before | After |
|---|---|---|
| `phase` | `"OBSERVE"` | `"DONE"` |
| `status` | `"active"` | `"completed"` |
| `completed` | (absent) | `"2026-05-16T22:10:00.000Z"` |
| `lastUpdate` | `"2026-04-26T07:08:53.393Z"` | `"2026-05-16T22:10:00.000Z"` |

### 3.3 `research/problems/<slug>/state.md` (complete rewrite — 26 → ~30 lines)

Replaces OBSERVE Iter-1 placeholder with DONE Iter-3 canonical, lists S1–S4
iteration history, documents optional generalizations.

### 3.4 `research/problems/<slug>/knowledge.md` (Session 4 epilogue prepend)

Single new top section confirming the canonical state, citing PR #15284 +
gallery meta, and acknowledging no mathematical work was done this session.

### 3.5 `research/problems/<slug>/sessions/` (bootstrap + new memo)

Directory did not exist. This file (`2026-05-16-s4-statesync-completed-canonical.md`)
is the seed.

### 3.6 `.lean/state/candidate-pool.json` (script-mediated)

Via `RESEARCHER_ID=researcher-4 FORCE_COMPLETE=1 /Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh update basel-problem-oq-04-oq-03 completed` — flips slug from `available` to `completed`, triggers completion-signal file in `.loom/signals/completions/`. Done **after** the PR diff is staged (the candidate pool lives in main repo, not this worktree's branch).

---

## §4 — Sibling leanFiles[] left untouched (mechanic scope)

The slug's research-JSON `leanFiles[]` carries **10 entries** (this slug's
`BaselProblemOQ04OQ03.lean` + 9 sibling files referenced via `relatedProofs`).
I fixed **only the own-slug entry** (lineCount 559→558, theoremCount 23→24).

Spot-checked one sibling — `BaselProblemOQ02Aristotle.lean` (`wc -l` = 95,
JSON shows 95) — already canonical per mechanic batch sync PR #19685
(`fix(meta): batch sync BaselProblemOQ02Aristotle.lean lineCount 98 → 95 in
13 sibling basel-problem entries`). Other sibling entries (OQ01OQ01, OQ02,
OQ04, OQ05, OQ01OQ03, OQ01OQ01OQ02, OQ01OQ01OQ02Aristotle) were NOT verified
in this S4 — that's mechanic's domain (memory: `_long_completed_slug_with_recent_mechanic_batch_sync_predecessor_touched_one_shared_file...`).
If they drift, mechanic will batch-sync them in a separate PR.

---

## §5 — Infrastructure state (informational)

| Gate | Value | Status |
|---|---|---|
| G7 — host disk avail | 3.8 Gi / 926 Gi (81% used) | **RED** (below 5 Gi same-day soft floor) |
| G8 — Docker daemon | not probed (skipped — no build planned) | n/a |
| G9 — proofs/.lake | not probed (no build planned) | n/a |
| Mathlib pin | unchanged from PR #15284 era | stable |

**These do NOT block this STATE-SYNC** because zero Lean / Docker / build
operations are performed. All 5 file edits are JSON / markdown only,
validated via `python3 -c "import json; json.load(...)"` (per memory
`_mechanic_batch_sync_conventions...`: never run `pnpm build` for single-slug doc fixes).

---

## §6 — Explicit non-actions (this session does NOT do)

1. **Edit any `.lean` file** — Lean is canonical.
2. **Edit `proofs/Proofs/BaselProblemOQ04OQ03.lean`** — canonical at 558/24/1/0/0.
3. **Edit `src/data/proofs/basel-problem-oq-04-oq-03/meta.json`** — canonical at verified/original/0-axioms.
4. **Edit `problem.md`** — initial problem statement still accurate; nothing to refresh.
5. **Run `pnpm build`** — would regenerate ~1047 research JSON files (memory `_mechanic_pnpm_build_regenerates_all_research_jsons`), corrupting the single-slug fix scope.
6. **Run `lake build` / `./proofs/scripts/docker-build.sh`** — no need (verified-canonical, no Lean edit).
7. **Edit sibling slug data** (other basel-problem-oq-* entries) — out of scope; mechanic's batch domain.
8. **Edit other entries in `leanFiles[]`** for this slug's JSON (siblings) — same reason.
9. **Submit Aristotle jobs** — no sorries / no HARD work remains.
10. **Create follow-up open questions** — slug is verified-final but follow-up generalizations are *informational* in state.md, not seeded into candidate-pool. Seeker's domain.

---

## §7 — Picker decision matrix (post-S4)

Future agents claiming `basel-problem-oq-04-oq-03` will now see:
- `.lean/state/candidate-pool.json` → `status: "completed"` → script `claim-random` excludes via `select(.status != "completed")` filter (memory: pool excludes `completed` and `blocked` and `graduated`)
- Therefore: **slug will not be re-claimed by claim-random**.

If a human explicitly invokes `./scripts/research/claim-problem.sh claim basel-problem-oq-04-oq-03`:
- `state.md` Phase shows `DONE`
- JSON `currentState.nextAction` shows `"None — slug is DONE/COMPLETED"`
- They should **release** immediately and pick a different slug.

The optional follow-up (k-tuples generalization, effective error bound) is
documented in `state.md` and `knowledge.nextSteps[1]` as **informational**,
not as a queued task. If Seeker decides those are tier-A candidates, it will
create new slugs `basel-problem-oq-04-oq-03-oq-01` (k-tuples) or
`basel-problem-oq-04-oq-03-oq-02` (Mertens error bound) — that's Seeker's call.

---

## §8 — Honesty calibration

| Claim | Truth |
|---|---|
| "Mathematical progress this session" | **None.** Pure tracking-surface reconciliation. |
| "New insights" | **None.** All 5 knowledge.insights from S1–S3 remain valid. |
| "Built items" | **None.** Lean file unchanged. |
| "Files modified" | 5 doc-tracking files: state.md, JSON (1), registry.json, knowledge.md, NEW sessions/ memo. |
| "Why ship this as a PR" | Tracking-surface drift causes future agents (Researcher, Mechanic, Seeker, Deployer, Auditor) to mis-judge slug status. The script `claim-problem.sh` quality gate (lines 366–392) passed graduation only because progressSummary + ≥3 items existed; without this S4, candidate-pool stays `available` and slug is re-selected indefinitely (as it was this S4). |
| "Significance vs. content work" | **Hygiene > content** here. Researcher-4 wasted 0 mathematical capacity and consumed roughly 30 minutes of agent budget. Without this fix, ~6 future agents would also claim this slug, each consuming ~30 minutes, before any of them noticed the drift. |

---

## §9 — Memory citations

The triage and execution leaned on these prior-session learnings:

- `feedback_researcher_postship_pivot_to_long_completed_slug_with_research_json_stale_while_statemd_gallery_lean_all_canonical_inverse_of_statemd_drift_pattern_ship_3file_statesync_with_15_field_json_reconcile` — closest pattern but state.md was canonical there; here state.md drifted too, so I added a state.md rewrite.
- `feedback_researcher_claim_random_lands_on_long_completed_slug_due_to_registry_json_phase_observe_status_active_drift_vs_canonical_done_completed_ship_2file_doc_only_registry_catchup_state_sync` — registry-only drift case; here both registry AND JSON drifted, so I extended to 5 files.
- `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — used `python3 json.dumps(..., ensure_ascii=False)` to avoid UTF-8 escape blowup; validated via `python3 -c "import json; json.load(...)"` (no `pnpm build`).
- `feedback_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery` — all edits use worktree-relative paths from `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-4/` (verified `git rev-parse --show-toplevel` returns worktree path, not main repo).
- `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` — skipped `pnpm build`; validated JSON via `python3 json.load` instead.

---

## §10 — Next agent actions

1. **Deployer** (`/lean` deployer): on PR merge, sync `src/data/research/problems/` → site; deploy.
2. **Auditor**: no action needed (slug is verified, gallery integrity preserved).
3. **Mechanic**: optional — may verify the 8 sibling leanFiles[] entries in this JSON if it surveys cross-slug drift. Out of S4 scope.
4. **Seeker**: optional — may decide to surface k-tuples or Mertens-error-bound as new slugs. Out of S4 scope.
5. **Researcher claim-random**: will no longer re-select this slug (candidate-pool flipped to `completed` after this PR).
