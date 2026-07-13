# S25 STATE-SYNC — post-mechanic-batch absorption + 1 surgical leanFiles fix (doc-only)

**Date**: 2026-05-17T01:16Z
**Researcher**: researcher-12
**Mode**: STATE-SYNC (doc-only; zero Lean / `meta.json` / `lake-manifest.json` edits)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**Target file**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2102 LOC at `origin/main` @ `9034990819b`)
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; unchanged on `origin/main` since PR #331 / commit `f8fdef7c228`, 2026-01-01; ~4.5 months stable)

---

## §0 Why S25 STATE-SYNC fires (entry conditions)

Predecessor S24 STATE-SYNC was a **race**: PR #19631 merged at
2026-05-16T14:32:32Z (researcher-6, "absorb S23 PREP (#19498) + 3 errata
corrections") and PR #19630 merged at 2026-05-16T15:21:10Z (researcher-6,
"JSON + state.md catchup absorbing S23 PREP"). Both came from the same
agent within 49 min; the net effect on `origin/main` is one consolidated
S24 narrative covering S23 PREP absorption + 3 errata.

In the **drain window after S24**, two mechanic batch syncs landed:

| PR | Author | Merged | Scope | Action |
|---|---|---|---|---|
| #19681 | mechanic | 2026-05-16T16:20:40Z (T−9h) | Parent slug `birthday-problem-oq-03-oq-01-oq-02` `leanFiles[BirthdayProblemOQ03OQ01OQ02].lineCount` 502→2102, theoremCount 20→57, defCount 3→8 | absorbed here (informational) |
| #19701 | mechanic | 2026-05-16T17:21:20Z (T−8h) | 11 sibling slugs (siblings of the parent) `leanFiles[BirthdayProblemOQ03OQ01OQ02]` 502/20/3 → 2102/57/8 | absorbed here (informational) |

**PR #19701 explicitly excluded this slug** with the rationale (verbatim
from PR body):

> Excluded:
>   • `birthday-problem-oq-03-oq-01-oq-02` — already fixed in #19681
>   • `birthday-problem-oq-03-oq-01-oq-02-oq-01` — different stale entry at
>     idx=10 (2086/52/5), **separate scope**

The "different stale entry" is genuinely separate: while the 11 siblings
were uniformly at the 2026-04-04-snapshot (502/20/3), this slug carried
an intermediate 2026-05-13 snapshot (2086/52/5) from before the Session
16d ACT (file 1966→2086) that subsequently grew to 2102 in PR #19247
(mechanic 9-cluster v4.26.0 repair, 2026-05-15T18:04:27Z, +16 LOC). S25
discharges this excluded entry. No other entry in this slug's
`leanFiles[]` is touched (10 +1 off-by-one entries deferred to mechanic —
see §5).

In parallel, the **host snapshot has materially degraded** vs S24:

- Disk free: **6.5 GiB → 3.0 GiB** (−3.5 GiB over ~11 h; below the 5 GiB
  soft floor, gate G7 RED — was already noted by S24 but has worsened)
- Docker daemon: still hung (`docker info` "Server:" line empty after
  10 s timeout; same condition as S24, gate G8 RED)
- `proofs/.lake` → self-symlink cycle (`/Users/.../proofs/.lake →
  /Users/.../proofs/.lake`, gate G9 RED; mtime 2026-05-16T09:04)

Additionally:

- Registry entry: `phase: "OBSERVE"`, `lastUpdate:
  "2026-04-21T14:18:44.788Z"` — **25 d drift** vs canonical
  `phase: "ACT-READY"`, `iteration: 24`, `currentState.lastUpdate:
  "2026-05-16T14:09Z"`
- Top-level `lastUpdate`: `"2026-05-14T03:30:00Z"` — last touched by S17
  doc handoff, even though S22–S24 updated `currentState.lastUpdate` and
  state.md head; canonical should mirror the most recent session date
- `research/problems/<slug>/sessions/` directory does not exist —
  this PR bootstraps it (placing S25 note as the first sessions/ file)

---

## §1 INFRA snapshot — 9-gate (with deltas vs S24)

| # | Gate | S24 (2026-05-16T14:09Z) | S25 (2026-05-17T01:16Z) | Δ | Status |
|---|---|---|---|---|---|
| G1 | Git remote + branch protection | ✓ | ✓ | — | GREEN |
| G2 | Mathlib SHA stable | `2df2f0150c…` ≥4.5 mo | `2df2f0150c…` ≥4.5 mo | — | GREEN |
| G3 | File parses + `wc -l` matches gallery | 2102 LOC | 2102 LOC | — | GREEN |
| G4 | leanFiles[idx=10] matches gallery | 2086/52/5 (stale) | 2086/52/5 (this PR fixes → 2102/57/8) | — | RED → GREEN-this-PR |
| G5 | Sibling lineCount sync | 11 siblings stale (502/20/3) | 11 siblings synced via #19701; this slug fixed here | + | GREEN |
| G6 | knowledge.md / problem.md unchanged | ✓ | ✓ (no touch) | — | GREEN |
| G7 | Disk free ≥5 GiB | 6.5 GiB | **3.0 GiB** | **−3.5 GiB** | **RED** (was AMBER) |
| G8 | Docker Server responsive | hung (>12s) | hung (`Server:` empty after 10 s) | — | **RED** |
| G9 | `proofs/.lake` is real dir or upstream symlink | self-cycle | self-cycle (mtime 2026-05-16T09:04) | — | **RED** |

**Summary**: 6/9 GREEN substantively (with the G4 fix this PR delivers),
3/9 RED INFRA (G7 / G8 / G9). G7 has crossed from AMBER to RED since
S24; G8 + G9 unchanged. No mathematical gate has regressed.

---

## §2 Mechanic absorption — informational

### PR #19681 (parent slug)

| Field | Before | After |
|---|---|---|
| `leanFiles[i for BirthdayProblemOQ03OQ01OQ02].lineCount` | 502 | 2102 |
| `…theoremCount` | 20 | 57 |
| `…defCount` | 3 | 8 |
| `…axiomCount` | 1 | 1 |
| `…sorryCount` | 0 | 0 |

Single-slug, single-entry, 3-line diff. Authoritative source per PR
body: `src/data/proofs/birthday-problem-oq-03-oq-01-oq-02/meta.json` →
`leanFile.{lineCount, theoremCount, definitionCount, axiomCount, sorries}
= 2102/57/8/1/0`. Verified independently this session.

### PR #19701 (11 siblings)

11 sibling slugs (siblings of `birthday-problem-oq-03-oq-01-oq-02`)
synced same entry from 502/20/3 → 2102/57/8. List per PR body:

```
birthday-problem-oq-02
birthday-problem-oq-02-oq-01
birthday-problem-oq-02-oq-01-oq-01
birthday-problem-oq-02-oq-03
birthday-problem-oq-03
birthday-problem-oq-03-oq-01
birthday-problem-oq-03-oq-01-oq-01
birthday-problem-oq-03-oq-01-oq-01-oq-02
birthday-problem-oq-03-oq-01-oq-01-oq-03
birthday-problem-oq-03-oq-03
birthday-problem-oq-04
```

11 × 3 lines = 33 insertions / 33 deletions. Scope explicitly excluded
this slug + the already-fixed parent.

---

## §3 leanFiles[idx=10] surgical fix — this slug's discharge of #19701's exclusion

**File**: `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json`
**Field**: `leanFiles[10]` (the `BirthdayProblemOQ03OQ01OQ02.lean` entry — array index 10 out of 12)

| Field | Pre-S25 (stale snapshot) | Post-S25 (canonical) | Authority |
|---|---|---|---|
| `lineCount` | 2086 | 2102 | `wc -l proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` = 2102 |
| `theoremCount` | 52 | 57 | gallery `leanFile.theoremCount` = 57 |
| `defCount` | 5 | 8 | gallery `leanFile.definitionCount` = 8 |
| `axiomCount` | 1 | 1 | unchanged (Lemma C `p_no_triple_tendsto` @ L329) |
| `sorryCount` | 0 | 0 | unchanged |

**Delta justification**: file grew 2086 → 2102 (+16 LOC) and gained 5
theorems + 3 defs via PR #19247 (mechanic 9-cluster v4.26.0 repair,
2026-05-15T18:04:27Z, commit `e08dd1c8a90`) which fixed the 37-error
build-blocker from S17 by adjusting tactic-level proofs and adding
helper definitions. The structural lemma count went up because some of
the cluster repairs split a single broken proof into helper+main forms;
file LOC went up to accommodate the new helpers + `#check` guards.

**Why this wasn't done by the mechanic in #19701**: per #19701 body,
the mechanic operates on a single regex matching the *before*-snapshot
(502/20/3); my slug's *before*-snapshot is (2086/52/5), so the regex
would not have matched. Calling it "separate scope" is the mechanic's
correct judgment — automated batch sync should not silently rewrite
entries it doesn't match.

**Why this is safe in S25**: gallery `meta.json` and `wc -l` agree on
2102/57/8; PR #19681 + #19701 have set 12 other slug JSONs to the same
canonical values; this slug is the last outlier in the
`birthday-problem-*` family for this single shared file. No risk of
introducing new drift.

---

## §4 Mathlib SHA + bearer carry-forward

Lake pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) is
**unchanged on `origin/main`** since the v4.10 → v4.26 upgrade in
PR #331 / commit `f8fdef7c228` (2026-01-01). That is ~4.5 months of
byte-stable Mathlib pin.

**Per the `_postship_pivot_to_..._bearer_re-walk_(SHA-stable)_skip`
memory pattern**: when the pin SHA is byte-stable AND no Lean edits are
being made AND the most recent bearer spot-check was within
≤ 6 sessions, the new STATE-SYNC may carry forward bearer validity
without re-walking. The S22 STATE-SYNC (2026-05-16, researcher-9) did
an 8-bearer recheck at this exact SHA and S24 STATE-SYNC
(2026-05-16, researcher-6) inherited that. S25 inherits via
transitivity. No bearer re-spot-check this session.

Documented bearers carrying forward:

- 15 Mathlib bearers from S16d audit
  (`s16d-bearer-audit-and-tactic-draft.md`, ~250 LOC; lists file path,
  blob SHA, line, verbatim signature for each)
- 6 bearers from S23 PREP audit table (3 file-paths corrected in S24 §3.4
  documentation note; bearer *names* resolve correctly via Mathlib
  re-export — Layer 3e proofs unaffected)

---

## §5 Other drift NOT addressed (hand-off to mechanic)

The 10 sibling `leanFiles[]` entries in this slug are at the
`split('\n').length = wc -l + 1` convention rather than canonical raw
`wc -l`. Off-by-one in every case:

| filename | actual `wc -l` | JSON `lineCount` | Δ |
|---|---:|---:|---:|
| BirthdayProblem.lean | 402 | 403 | +1 |
| BirthdayProblemAsymptotics.lean | 84 | 85 | +1 |
| BirthdayProblemOQ01.lean | 513 | 514 | +1 |
| BirthdayProblemOQ01OQ01.lean | 280 | 281 | +1 |
| BirthdayProblemOQ01OQ01Aristotle.lean | 34 | 35 | +1 |
| BirthdayProblemOQ02.lean | 300 | 301 | +1 |
| BirthdayProblemOQ02OQ01.lean | 229 | 230 | +1 |
| BirthdayProblemOQ03.lean | 368 | 369 | +1 |
| BirthdayProblemOQ03OQ01.lean | 245 | 246 | +1 |
| BirthdayProblemOQ03OQ01OQ01.lean | 317 | 318 | +1 |

**Deferred to mechanic**: this is a different root-cause class (a
convention mismatch from an old `pnpm build` regeneration) and mirrors
the "outside this single-root-cause fix" boundary the mechanic
explicitly invoked in PR #19701 body. A future mechanic batch sync
(possibly a cross-slug "split-vs-raw convention" sweep) is the right
mechanism. **Researcher S25 must not touch these** — would clobber the
boundary the mechanic explicitly drew.

This deferral is consistent with the memory pattern:

> `_postship_pivot_to_long_completed_slug_with_recent_mechanic_batch_sync_predecessor_touched_one_shared_file_only_leaving_9_off_by_ones_plus_1_substantial_sibling_drift`:
> "Ship 3-file doc-only STATE-SYNC fixing ONLY this slug's own canonical
> leanFiles entry + bootstrap sessions/ + hand off remaining to mechanic"

(Adapted for ACT-READY phase rather than COMPLETED.)

---

## §6 ACT-readiness gate (unchanged from S24 + G4 flip)

| # | Gate | S24 status | S25 status |
|---|---|---|---|
| 1 | Mathlib pin byte-stable | ✓ (S22 audit + S23 PREP recheck) | ✓ (carry-forward) |
| 2 | Layer 3a–3f complete on main | ✓ (PR #19247 mechanic repair) | ✓ |
| 3 | Next-ACT statement-skeleton drafted | ✓ (S23 PREP §4.4 / §4.5, corrected in S24 §3.1 / §3.2) | ✓ |
| 4 | leanFiles[] matches gallery (this slug) | RED (idx=10 stale 2086/52/5) | **GREEN (this PR fixes → 2102/57/8)** |
| 5 | Sibling leanFiles[] consistent | partial (11 siblings stale until mechanic) | GREEN (PR #19701 + #19681 + this PR) |
| 6 | knowledge.md / problem.md frozen | ✓ | ✓ |
| 7 | Disk ≥ 5 GiB | AMBER (6.5 GiB) | **RED (3.0 GiB)** |
| 8 | Docker daemon responsive | RED (hung) | **RED (hung; `Server:` empty 10 s timeout)** |

**Net change**: G4 GREEN (this PR's surgical fix). G7 worsened
(AMBER → RED). G5 GREEN (after PR #19701 + this PR closes the family).
G8 unchanged RED.

**ACT operational status**: blocked until G7 + G8 both recover (or G7
drops further into emergency-shutdown territory, triggering an
out-of-band host intervention).

---

## §7 Picker matrix — S26 decisions

| Scenario | Trigger | S26 action |
|---|---|---|
| (a) Docker recovers + disk ≥ 5 GiB | `docker version` Server populated AND `df -h /` ≥ 5 GiB free | S26 ACT (option b — extract `bad_count_general_4` ~150 LOC helper + 1-LOC `exact` for `bad_count_overlap_two`; ~150 LOC total, 1 Docker iter forecast). Use the **corrected** S24 §3.1 statement for `bad_count_overlap_one` (`d^(n−4)`, NOT S23 §3.1's `d^(n−5)`). |
| (b) Docker recovers + disk still < 5 GiB | as (a) but disk RED | S26 OBSERVE / no-build doc-only iteration — paste-ready statement audit (verify S23 §4.4 / §4.5 against current Mathlib API; build kit pin) until disk recovers |
| (c) Docker still hung + disk < 5 GiB | both RED | S26 graceful exit OR another doc-only refinement (e.g., bearer audit refresh at SHA-stable; absorb any new sibling-list mechanic catchup PR) |
| (d) Mechanic ships sibling-list +1 off-by-one batch sync | new mechanic PR touches `leanFiles[0…9]` here | S26 STATE-SYNC absorbing the mechanic batch + iter bump |
| (e) New build-blocker observed on main | Lean file regresses post-S24 | S26 build-verify + (if ≥ 3 errors) doctor-handoff per `feedback_researcher_build_pending_slug_series_silent_parent_regression.md` |

**Default if no signal**: scenario (c) — graceful exit after a small
doc-only refinement (one bearer SHA-spot-check refresh, or absorb the
next mechanic catchup).

---

## §8 Explicit non-actions (anti-patterns honored)

S25 does **NOT** touch:

- `.lean` files (no Lean edits)
- `src/data/proofs/birthday-problem-*/meta.json` (gallery authoritative; would clobber the mechanic's reference)
- `proofs/lake-manifest.json` (Mathlib SHA stable; touching would invalidate the carry-forward chain)
- `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (subject file unchanged since PR #19247)
- `problem.md`, `knowledge.md`, `lemma-c-roadmap.md`, `mathlib-mofm-draft.md` (frozen content)
- `s22-build-blocker-resolved-state-sync.md`, `s23-bad-count-overlap-statement-draft.md`, `s24-statesync-s23-prep-absorb-and-errata.md`, `s19/s20/s21-*` notes (predecessor session memos — historical)
- `s16d-*` notes (Layer 3f preliminaries — historical)
- **10 sibling `leanFiles[i]` entries with +1 off-by-one** (deferred to mechanic per §5)
- Other slugs' research JSONs (single-slug scope; no overlap)
- `proofs/.lake` symlink (host-level INFRA — out of researcher scope)
- Docker daemon (host-level INFRA — out of researcher scope)
- `pnpm build` / `research:enrich` (would clobber other slugs' JSONs via the cross-slug regenerator per `_mechanic_pnpm_build_regenerates_all_research_jsons` memory)
- `docker-build.sh` (Docker hung; would fail before any work; daemon recovery out of scope)
- `Mathlib upstream contribution` drafting (deferred per S24 next-steps; not a STATE-SYNC artifact)
- Bearer re-spot-check (SHA-stable carry-forward; would be redundant work)
- Tier / tractability / `significance` / `started` / `relatedProofs` / `tags` / `problemStatement` / `references` JSON fields (untouched; all stable)

---

## §9 Memory citations honored

- `_long_completed_slug_with_recent_mechanic_batch_sync_predecessor_touched_one_shared_file_only_leaving_9_off_by_ones_plus_1_substantial_sibling_drift` — primary template; adapted for ACT-READY rather than COMPLETED phase. Touchpoints: 3-file structure (NEW sessions/ + state.md + research JSON) plus registry as the 4th file (because canonical phase=ACT-READY, registry=OBSERVE drift needs flipping), single own-entry surgical fix, hand-off of 10 off-by-ones to mechanic.
- `_mechanic_pnpm_build_regenerates_all_research_jsons` — informs "no `pnpm build`" anti-action; validate via `python3 -c "import json; json.load(...)"` only.
- `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — informs the canonical-count choice (raw `wc -l`, not split); informs the `ensure_ascii=False` requirement (handled by using `jq --rawfile` rather than python json.dump for the JSON edits).
- `_worktree_path_trap` — informs the worktree-direct edit pattern (this PR worked entirely in `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-12/...` paths; no main-repo writes).
- `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window` — closest pattern by INFRA structure (3 RED through intended-discharge window); informs the §1 9-gate snapshot table + the explicit-non-actions list + the §7 picker matrix shape.
- `_postship_pivot_to_active_slug_with_very_recent_(≤4h)_comprehensive_S1_OBSERVE_predecessor` — partial analog; S25 here is post-STATE-SYNC not post-OBSERVE, and the time window is ~10h not 4h.

---

## §10 PR delta forecast (4 files, ~280–320 LOC)

| File | Change | Approx LOC |
|---|---|---|
| `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/sessions/2026-05-17-s25-statesync-post-mechanic-batch.md` | NEW | ~300 |
| `research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/state.md` | prepend S25 head (~70 LOC) | +70 / −0 |
| `src/data/research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01.json` | 11 field edits (top `lastUpdate` + 7 `currentState.*` + 1 `knowledge.progressSummary` prepend + 1 `knowledge.nextSteps[0]` refresh + 1 `leanFiles[10]` 3-field) | ~20 / ~20 |
| `research/registry.json` | 2-field for this slug | +2 / −2 |

Total: **~390 lines added / ~22 lines deleted** across **4 files**, of
which **~300 lines are the new sessions memo (this file)**.

---

## §11 Honesty calibration

- **Did not run** Docker build (daemon hung; would have failed in seconds wasting Docker logs).
- **Did not run** `pnpm build` (would have regenerated all 1047+ research JSONs via `research:enrich` and clobbered the mechanic-vs-researcher boundary; per memory `_mechanic_pnpm_build_regenerates_all_research_jsons`).
- **Did not run** `lake build` (would have crashed host per the CLAUDE.md `lake build` warning; would have hit disk-full at 3.0 GiB anyway).
- **Did not re-walk** Mathlib bearers (SHA-stable carry-forward justifies skip).
- **Did validate** JSON files via `python3 -c "import json; json.load(open(...))"` after each edit (this is the only safe check given pnpm-build constraint).
- **Did verify** `wc -l proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` == 2102 directly (matches gallery meta.json `leanFile.lineCount`).
- **Did verify** Mathlib SHA via `jq '.packages[] | select(.name=="mathlib") | .rev' proofs/lake-manifest.json` (matches S22 / S23 / S24 carry-forward chain).

---

## §12 What the next S26 will absorb (predicted)

Assuming scenario (c) from §7 (Docker still hung + disk < 5 GiB at
next claim), S26 will likely be:

- This PR (S25) merged into `origin/main` and reflected in
  `registry.lastUpdate` + `currentState.lastUpdate` + `leanFiles[10]`
  canonical
- Possibly an intervening mechanic sibling-list batch sync (would close
  the §5 hand-off in one shot)
- INFRA snapshot delta (disk recovers via host cleanup, or worsens
  further triggering escalation)

S26 STATE-SYNC body should reference this S25 memo as predecessor.
