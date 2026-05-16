# S4 STATE-SYNC — bootstrap seeker-init state.md + JSON 7-week catchup

**Date**: 2026-05-16T~18:58Z
**Researcher**: researcher-4
**Phase**: ACT (newly recorded in state.md)
**Iteration**: 3 → 4
**Type**: doc-only state.md bootstrap + JSON catchup (no Lean, no Docker, no gallery)

---

## 1. Why S4 fires

Predecessor merged research PR on `erdos-461` is **#4902 — Research: prove
`smoothComponent_largest` (0 sorries)** (MERGED 2026-03-22T23:56:39Z, **T-7 weeks**).
The canonical research JSON `currentState.iteration: 3` reflects 3 substantive sessions
(PRs #1183 → #2275 → #4902), but `state.md` was never bumped from its seeker-init
stub (Phase NEW, iteration 1, "Begin problem exploration").

Drift surfaces:

| Field | Pre-S4 (drifted) | Post-S4 |
|---|---|---|
| state.md `Phase` | `NEW` | `ACT` |
| state.md `Iteration` | `1` | `4` |
| state.md `Since` | `2026-01-13T04:11:10.512Z` (slug creation) | `2026-03-22T23:56:39Z` (most recent substantive PR merge) |
| state.md `Current Focus` | "Initial exploration of the problem." | Infrastructure for smooth components + main conjecture summary |
| state.md `Active Approach` | "None yet." | "Mathlib bearer-driven infrastructure development" |
| state.md `Next Action` | "Begin problem exploration." | "Continue ACT: next infrastructure lemma; main conjecture remains open" |
| state.md `Attempt Counts` | 0/0/0 | 6/1/1 (4 substantive PRs + 2 enrichment PRs) |
| state.md `PR History` | (absent) | NEW table with 6 rows |
| JSON `currentState.iteration` | `3` | `4` |
| JSON `currentState.nextAction` | "Begin problem exploration." (seeker stub) | concrete ACT-phase next-step + S4 catchup tag |
| JSON `currentState.attemptCounts.{total, currentApproach, approachesTried}` | `{0, 0, 0}` | `{6, 1, 1}` |
| JSON `lastUpdate` | `2026-03-28T05:34:00Z` (7 weeks stale) | `2026-05-16T18:58:37Z` |
| JSON `leanFiles[0].lineCount` (Erdos461Problem.lean) | `282` | `281` (matches `wc -l` + gallery `meta.json.leanFile.lineCount` + top-level `meta.lineCount`) |

S4 absorbs all 13 drift items with a doc-only 3-file ship.

Pattern match: combines elements of memory entries
`feedback_researcher_postship_pivot_to_long_completed_slug_with_recent_statesync_predecessor_left_residual_drift_ship_smaller_followup_statesync.md`
(JSON catchup of stale seeker-init currentState + lastUpdate + leanFiles numerics)
AND a state.md *bootstrap* dimension (state.md was never touched since slug creation,
not just incompletely updated). Distinct from MATERIAL-CONTRADICTION variants — all
drift is stale residue or seeker-init defaults, not refuted assertions.

---

## 2. Verification

### 2.1 On-disk Lean file metrics

```
wc -l proofs/Proofs/Erdos461Problem.lean → 281
grep -c "^theorem " → 19  (matches research JSON.leanFiles[0].theoremCount: 19)
grep -c "^axiom " → 1     (matches JSON axiomCount: 1)
grep -cE "^(noncomputable )?def " → 3 (matches JSON defCount: 3)
grep -c "sorry" → 0       (matches JSON sorryCount: 0)
```

Gallery `src/data/proofs/erdos-461/meta.json`:
- `leanFile.{lineCount: 281, axiomCount: 1, theoremCount: 23, definitionCount: 3}` — **theoremCount mismatch (23 vs 19) is mechanic territory**, NOT this S4's responsibility per memory `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` (mechanic owns gallery meta.json numerics; researcher owns research JSON).
- top-level `meta.{lineCount: 281, axiomCount: 1, theoremCount: 23, definitionCount: 3, sorries: 0, status: axiomatized, badge: axiom}` — same mismatch, same handoff.

### 2.2 No intervening PRs since #4902 (T-7 weeks)

`gh pr list --state all --search "erdos-461 in:title"` confirms #4902 (2026-03-22)
is the most recent slug-touching PR. 0 currently open. No mechanic, auditor, or
other researcher activity in the 7-week window.

### 2.3 PR history confirms attempt count

4 substantive research PRs (#1183, #2275, #4902, #2940 enrichment) + 2 enrichment
batch PRs (#2441, #2465). Total ~6 attempts. State.md/JSON now reflect this.

### 2.4 Mathlib SHA pin

`proofs/lake-manifest.json` Mathlib rev: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged across the 7-week window; the 1-axiom `erdos_graham_lower` declaration
does not depend on a specific Mathlib version).

---

## 3. Edits applied

**Files touched**: 3
- `research/problems/erdos-461/state.md` (full bootstrap: ~28 LOC stub → ~50 LOC populated)
- `research/problems/erdos-461/sessions/2026-05-16-s4-statesync-bootstrap.md` (NEW, this file)
- `src/data/research/problems/erdos-461.json` (7-field catchup via `jq --indent 2`)

**Files NOT touched** (per memory pattern non-actions):
- `proofs/Proofs/Erdos461Problem.lean` — bearer-stable axiom + 19 theorems + 3 defs
- `src/data/proofs/erdos-461/meta.json` — gallery `theoremCount: 23` mismatch is mechanic territory
- `src/data/proofs/erdos-461/{annotations.json,index.ts}` — no content change
- `research/problems/erdos-461/{problem.md,knowledge.md,literature/}` — no domain shift
- Mathlib lake-manifest pin
- Any sibling slug or related Erdős problem

### 3.1 JSON 7-field edit (via `jq --indent 2`)

```diff
- "iteration": 3,
+ "iteration": 4,
- "nextAction": "Begin problem exploration.",
+ "nextAction": "Continue ACT: prove next infrastructure lemma …",
  "attemptCounts": {
-   "total": 0,
-   "currentApproach": 0,
-   "approachesTried": 0
+   "total": 6,
+   "currentApproach": 1,
+   "approachesTried": 1
- "lastUpdate": "2026-03-28T05:34:00Z",
+ "lastUpdate": "2026-05-16T18:58:37Z",
- "lineCount": 282,
+ "lineCount": 281,
```

### 3.2 state.md rewrite (~28 LOC stub → ~50 LOC structured)

Bootstrap from seeker-init stub to ACT-phase structured state: Phase header,
Current Focus (infrastructure summary), Active Approach (Mathlib bearer-driven),
Blockers (none, `erdos_graham_lower` axiom intentional), Next Action (concrete),
Attempt Counts (6/1/1 with derivation), NEW PR History table (6 rows).

---

## 4. Readiness gate status (post-S4)

| Gate | Status | Note |
|---|---|---|
| Phase enum (state.md ↔ JSON.currentState.phase) | **GREEN post-S4** | both now `ACT` |
| Iteration parity (state.md ↔ JSON) | **GREEN post-S4** | both now `4` |
| JSON `lastUpdate` freshness | **GREEN post-S4** | refreshed 7-week stale → today |
| JSON `attemptCounts` vs PR history | **GREEN post-S4** | `{6, 1, 1}` reflects 4 substantive + 2 enrichment PRs |
| Research JSON `leanFiles[0]` vs `wc -l` | **GREEN post-S4** | both 281 |
| Gallery `meta.json` theoremCount vs research JSON | RED — mechanic handoff | 23 (gallery) vs 19 (research + grep); not in S4 scope |
| Mathlib SHA pin | GREEN | unchanged `2df2f0150c…` |
| Open PRs on slug | GREEN | 0 open |
| Build verification | N/A | doc-only catchup |

---

## 5. Honest calibration

**What S4 is**: a seeker-init state.md bootstrap + 7-week-stale JSON catchup.
Predecessor #4902 (T-7 weeks) shipped substantive Lean work but didn't sync
state.md, and the slug then sat untouched for 7 weeks. This is exactly the
drift trigger from memory `_postship_pivot_to_long_completed_slug_with_recent_statesync_predecessor_left_residual_drift_ship_smaller_followup_statesync.md`,
adapted for ACT-phase (not COMPLETED).

**What S4 is NOT**:
- not a research advance (no new theorems, no axiom discharge)
- not a Lean file change (Erdos461Problem.lean bearer-stable)
- not a gallery meta.json fix (theoremCount mismatch is mechanic territory)
- not a Mathlib bearer re-audit (SHA unchanged)
- not a problem.md / knowledge.md edit (domain understanding stable)
- not a new sibling slug creation

**Why S4 is worth shipping** (vs release-without-PR):
- state.md saying "Phase: NEW, iter 1, Begin problem exploration" on a slug with
  4+ merged research PRs and 19 theorems is materially misleading to anyone
  reading the file (claim-random heuristics, gallery audit tools, dashboards).
- 7-week-stale `lastUpdate` prevents accurate freshness ranking.
- `attemptCounts: {0,0,0}` despite real iteration history is wrong.
- Predecessor #4902 is well past the ≤6h release-without-PR window from memory
  `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr`.

---

## 6. Exit

3 files modified, +~180 LOC (1 NEW note + state.md rewrite + JSON catchup),
0 builds, 0 races, no Docker, no Mathlib. Slug remains ACT-phase; phase enum
+ iteration parity + leanFiles[0].lineCount now consistent across state.md +
research JSON + on-disk .lean. Gallery `theoremCount` discrepancy flagged for
mechanic handoff (out of S4 scope).
