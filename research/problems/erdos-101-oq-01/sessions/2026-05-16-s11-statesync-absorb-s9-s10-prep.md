# Session 11 STATE-SYNC — Absorb S9 PREP (#19403) + S10 PREP (#19421) corrections into state.md / JSON (doc-only)

- **Date**: 2026-05-16
- **Session**: 11
- **Phase**: STATE-SYNC (doc-only — catches `state.md` and `<slug>.json` up to S9 + S10 PREP merges on origin/main)
- **Researcher**: researcher-6
- **Status**: doc-only, conflict-free with all merged PRs and #19476 (mechanic meta drift fix, separate file scope)

## 1. TL;DR

S8 STATE-SYNC (#19360, MERGED 2026-05-16T03:53:49Z) shipped a Path-A ACT recipe in `state.md` Active Approach §1-§3. **Two sibling-audit PREPs landed afterward but did NOT update state.md / JSON** (both touched only `sessions/`):

- **S9 PREP (#19403, researcher-12, MERGED 2026-05-16T03:51:53Z)**: sibling-audit of S8 STATE-SYNC artifact (iii) + (i) per-P corollary; surfaces 2 soundness bugs (**F**, **G**) + corrected §5.1/§5.2 sketches.
- **S10 PREP (#19421, researcher-4, MERGED 2026-05-16T04:33:55Z)**: sibling-audit of S9's corrected sketches; surfaces 2 ACT-blocking elaboration bugs (**H**, **I**) + an informational sequencing observation (**J**); ships paste-ready ~78-LOC three-artifact §5.1-§5.3 recipe.

After both merges, **`state.md` is drifted by 5 bugs**: F + G (from S9) + H + I + J (from S10). Any ACT picker reading `state.md` Active Approach §1-§3 verbatim would land:
- (F) an unsound `IsLittleO` form (`maxFourPointLines n / n² → 1/12 ≠ 0`),
- (G) an unsound per-P corollary (no `NoFiveCollinear P` hypothesis ⇒ 9 collinear points refute the bound),
- (H) an `unknown identifier 'isLittleOh_n_squared_iff_isLittleO'` error (the bridge lemma was always-deferred),
- (I) a `show` failure on `|(n : ℝ)^2|` (the `IsBigO.of_norm_le` hypothesis has only ONE norm),
- (J) the sequencing trap (artifact (ii) MUST appear before artifact (iii) in file source order).

This S11 STATE-SYNC ships **the doc-only catch-up** so the next ACT picker reads a state.md that names S10 PREP's §5.1-§5.3 as authoritative (not S8's §5). It does NOT ship Lean code; the ACT-readiness gate (now 8/8 GREEN per S10 §8) is preserved verbatim from S10 PREP.

## 2. Pre-claim probe (2026-05-16T05:00–05:05Z, after both #19403 + #19421 merged)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'erdos-101-oq-01 in:title' --json number,title,createdAt,mergeStateStatus
[
  {"number":19476, "title":"fix(meta): erdos-101-oq-01 lineCount 383→471, theoremCount 8→9", ...}
]
```

One open PR on slug at S11 claim: **#19476** (mechanic meta drift fix; touches `src/data/proofs/erdos-101-oq01/meta.json` ONLY — `lineCount`/`theoremCount` aggregate counts). **Strictly disjoint** from this S11 STATE-SYNC's file scope (sessions/ + state.md + research JSON).

Last merged research PR on slug: **#19421** (S10 PREP, doc-only) at 2026-05-16T04:33:55Z. Drain wave for slug in the past 1h2m: 0 merges (deployer paused on this slug post-S10).

```
$ ps -ef | grep docker-build | grep -v grep
(no output)
```

No sibling Docker processes touching `Erdos101OQ01.lean` / `Erdos101Problem.lean`. Race-free.

## 3. Mathlib lake-pin recheck

```
$ grep -A2 "leanprover-community/mathlib4" proofs/lake-manifest.json | grep '"rev":'
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
```

**Unchanged** since S8 STATE-SYNC §4 + S9 PREP §6 + S10 PREP §7 (all 2026-05-16). **ZERO drift across ~5h.** Mathlib still pinned to v4.26.0.

All bearer pins from S10 PREP §7 (10 bearers, line-numbered) remain valid. No re-verification needed for this STATE-SYNC.

## 4. Drift catalogue: what state.md / JSON need to reflect post-#19403 + #19421

### 4.1 state.md head block (Phase, Since, Iteration, Last Updated)

| Field | Current value | Drift | Correct value |
|---|---|---|---|
| Phase | `PREP` | (S9 PREP + S10 PREP both PREP; no state change) | `PREP` (unchanged) |
| Since | `2026-05-16 (S8 STATE-SYNC)` | Drift: ~1.5h | `2026-05-16 (S11 STATE-SYNC absorbing S9 + S10 PREP)` |
| Iteration | `8` | Drift: S9 + S10 are iterations 9 + 10; S11 STATE-SYNC is iteration 11 | `11` |
| Last Updated | `2026-05-16 (researcher-12)` | Drift: S9 = researcher-12, S10 = researcher-4 | `2026-05-16 (researcher-6, S11 STATE-SYNC)` |

### 4.2 state.md "Current Focus" + "Previous Focus" sections

S8's Current Focus describes the now-superseded S8 ACT plan. It needs to be:
- Pushed to "Previous Focus" preserving the S6 + S7 + S8 historical sequence
- Replaced with an S11 STATE-SYNC focus block describing: this is doc-only refresh absorbing S9 + S10 corrections; ACT-readiness gate now 8/8 GREEN per S10 PREP §8; recipe lives in `sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md` §5.1-§5.3 + §6 sequencing notes.

### 4.3 state.md "Active Approach" section (Bugs F, G, H, I corrections)

This section is the most-drifted. Current §1-§3 describes S8's artifact (i)/(ii)/(iii) plan **with Bugs F + G live in the text** (artifact (iii) signature on `maxFourPointLines` directly; artifact (i) per-P corollary missing `NoFiveCollinear P`). The corrections from S9 (F, G) + S10 (H, I, J) need to be inlined or — better — the section should be rewritten to defer to S10 PREP §5.1-§5.3 verbatim as the authoritative recipe.

### 4.4 state.md "Iteration history" — add S9, S10 rows

S8 STATE-SYNC's iteration history did not anticipate S9 + S10. Two new rows needed:

| Iter | Researcher | Date | Mode | Deliverable | PR | Status |
|---:|---|---|---|---|---|---|
| 9 | researcher-12 | 2026-05-16 | PREP | Sibling-audit of S8 STATE-SYNC artifact (iii) + (i) per-P corollary; finds Bugs F (unsound `IsLittleO` on `maxFourPointLines`) + G (per-P corollary missing `NoFiveCollinear`); corrected §5.1 + §5.2 sketches | #19403 | MERGED 2026-05-16T03:51:53Z |
| 10 | researcher-4 | 2026-05-16 | PREP | Sibling-audit of S9 PREP §5.1 + §5.2; finds Bugs H (undefined `isLittleOh_n_squared_iff_isLittleO`) + I (`IsBigO.of_norm_le` hypothesis-shape mismatch) + J (state.md/JSON sequencing trap); corrected §5.1 + §5.2 + §5.3 paste-ready ~78-LOC recipe | #19421 | MERGED 2026-05-16T04:33:55Z |
| 11 | researcher-6 | 2026-05-16 | STATE-SYNC | this PR — doc-only refresh absorbing S9 + S10 corrections; refreshes state.md head + Active Approach + Iteration history + Next Action; refreshes JSON `currentState`; flags Bugs F-J in Active Approach narrative | (this PR) | OPEN |

### 4.5 state.md "Next Action" section

Current state.md Next Action describes "S8 ACT" with 6-step recipe pointing at S7 PREP §9 + S8 STATE-SYNC §5. Both are now superseded by S10 PREP §5.1-§5.3 + §6 sequencing.

The Next Action should be rewritten to:
1. **Rename** the next step from "S8 ACT" to "S11 ACT" (since S8 STATE-SYNC + S9 PREP + S10 PREP each bumped iteration without changing the ACT identity).
2. **Authoritative source**: defer to `sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md` §5.1-§5.3 + §6 sequencing.
3. **Bug-checklist** for the ACT picker: F, G, H, I, J — each with a one-line fix.
4. **Sequencing constraint** (Bug J): artifact (ii) `isLittleOh_n_squared_iff_isLittleO` MUST appear before artifact (iii)'s iff theorem.
5. **LOC budget** revised: ~78 LOC across artifacts (i)+(ii)+(iii) per S10 §5.4 (within S7's ~105-125 envelope; +18 LOC over S9's claimed ~60 because S9 implicitly assumed artifact (ii) was already shipped).
6. **Docker iters forecast**: ≤ 2 per S10 §8 gate 7.

### 4.6 state.md "Attempt Counts"

| Field | Current | Drift | Correct |
|---|---|---|---|
| Total attempts | 7 | +2 (S9 PREP, S10 PREP) +1 (this S11 STATE-SYNC) | 10 |
| Current approach attempts | 0 | unchanged (no ACT attempted yet) | 0 |
| Approaches tried | 4 | +1 (S9+S10 audit chain refining S6+S7's bridge plan) | 5 |

### 4.7 state.md "Open files"

Two new session files added by S9 + S10; one new session file added by this S11:

- `sessions/2026-05-16-s9-prep-sibling-audit-of-s8-artifact-iii.md` — S9 PREP (705 LOC)
- `sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md` — S10 PREP (610 LOC)
- `sessions/2026-05-16-s11-statesync-absorb-s9-s10-prep.md` — this STATE-SYNC

### 4.8 state.md "Blockers"

Current blockers table lists "None for S8 ACT — all blocking dependencies merged on main". Still accurate. Add a row for **S10 PREP #19421** as a blocking dependency now-merged. Re-name the table heading "None for S11 ACT" (the ACT identity travels forward through S8 → S11 via three STATE-SYNCs/audits).

### 4.9 state.md "Build Status"

S4 + mechanic baseline still GREEN. No new Docker builds since #19255 mechanic child PR. The honesty note "Worktree build: not attempted" remains accurate; this S11 is still doc-only.

## 5. JSON `currentState` drift table

| JSON field | Current value | Correct value (post-S11) |
|---|---|---|
| `phase` | `PREP` | `PREP` (unchanged) |
| `since` | `2026-05-16T01:12:00Z` (S8 STATE-SYNC merge) | `2026-05-16T05:05:00Z` (S11 STATE-SYNC) |
| `iteration` | `8` | `11` |
| `focus` | S8 STATE-SYNC narrative | S11 STATE-SYNC narrative absorbing S9 + S10 (refer to S10 §5.1-§5.3 + §6 sequencing) |
| `blockers` | (carries S8 head note) | refreshed to acknowledge S9 + S10 merged on main |
| `nextAction` | S8 ACT pointing at S7 §9 + S8 §5 | S11 ACT pointing at S10 §5.1-§5.3 + §6 sequencing |
| `attemptCounts.total` | (whatever current) | bumped +3 (S9 PREP + S10 PREP + S11 STATE-SYNC) |
| top-level `lastUpdate` | `2026-05-16T01:12:00Z` | `2026-05-16T05:05:00Z` |

## 6. What this S11 STATE-SYNC does NOT do

- **No Lean edits.** `Erdos101OQ01.lean` (471 LOC) and `Erdos101Problem.lean` (758 LOC) untouched.
- **No `meta.json` edit.** Aggregate counts are mechanic territory (and #19476 is the open mechanic fix for `lineCount`/`theoremCount`). This PR is path-disjoint from #19476.
- **No new bearer pins.** S10 PREP §7's pinning table is authoritative and unchanged at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **No Docker build.** Worktree's `proofs/.lake` is a self-symlink (per S8 STATE-SYNC §"Build/verification claims" honesty note); the build claim continues to inherit from mechanic PR #19099 + #19255.
- **No re-derivation of Bugs F-J.** S9 + S10 already document them with goal-state walks and counterexamples. This STATE-SYNC merely *surfaces* them in `state.md` Active Approach + Next Action.
- **No selection between Path A (`maxFourPointLines : ℕ → ℕ` surrogate) and Path B (per-P aggregator).** S10 PREP §5.1 adopts Path A as the recommended ACT route; this STATE-SYNC defers to that recommendation.

## 7. File scope (3 files, strictly orthogonal to all merged + open PRs)

| File | Action | Disjointness verification |
|---|---|---|
| `research/problems/erdos-101-oq-01/sessions/2026-05-16-s11-statesync-absorb-s9-s10-prep.md` | NEW | No prior file by this name |
| `research/problems/erdos-101-oq-01/state.md` | MODIFY (head block + Current/Previous Focus + Active Approach + Iteration history + Next Action + Attempt Counts + Open files + Blockers) | Last touched by #19360 (S8 STATE-SYNC); subsequent S9 #19403 + S10 #19421 explicitly did NOT touch (paths-disjoint guarantee). #19476 (open, mechanic) touches `meta.json` ONLY. ✓ disjoint |
| `src/data/research/problems/erdos-101-oq-01.json` | MODIFY (`currentState.{phase, since, iteration, focus, blockers, nextAction, attemptCounts.{total, approachesTried}}` + top-level `lastUpdate`) | Last touched by #19360. Subsequent S9 + S10 did NOT touch. #19476 doesn't touch this file. ✓ disjoint |

## 8. Memory pattern composition

This STATE-SYNC fires the **`_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift`** pattern almost verbatim — but the "partial inline STATE-SYNC" is here played by S9 + S10 PREPs (which deliberately respected file-disjointness with the still-open S8 STATE-SYNC, then with each other), leaving `state.md` + JSON the same after their merges as it was post-S8.

It also composes with:
- `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer` — partial analog; here S9 + S10 are merged peers, no peer needs closure (the audited recipe in S8 §5 is superseded by S10 §5 but lives in MERGED state.md, not in an open PR; closure happens by virtue of the next ACT reading state.md and choosing to follow S10's §5.1-§5.3).
- `_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks` — for the §"Bug-checklist for the ACT picker" inline note in the rewritten Next Action.

This STATE-SYNC does NOT fire:
- `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep` — would require materializing the §5.1-§5.3 Lean code; this STATE-SYNC defers to S10's existing recipe.
- `_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready` — would require upgrading S10's recipe to fully-discharged code; out of scope for STATE-SYNC.

## 9. Honesty notes

- **No Docker build attempted.** Same constraint as S8/S9/S10 PREPs (worktree symlink trap).
- **No re-verification of Bugs F-J.** Counterexamples for F (numerical) and G (geometric — 9 collinear points) are documented in S9 PREP §3.4 + §4.4 with explicit small-`n` evaluations. Bugs H + I are documented in S10 PREP §3 + §4 with `gh api` SHA-pinned signature pulls.
- **No re-verification of the bearer pin table.** S10 PREP §7 was authoritative ~30 min ago; the lake-manifest SHA is unchanged (§3 above).
- **No claim about S11 ACT's actual Docker behavior.** S10 PREP §8 gate 7 forecasts ≤ 2 Docker iters; this STATE-SYNC inherits that forecast without re-deriving it.

## 10. Iteration counter justification

The Lean Genius / Loom iteration-counting convention (per S8 STATE-SYNC §"Iteration counter justification"): STATE-SYNCs that introduce visibility for ≥1 merged-since-last-update ACT/PREP/BUILD-VERIFY count as iterations themselves. This S11 STATE-SYNC absorbs 2 merged PREPs (S9 #19403 + S10 #19421) — both came after S8 STATE-SYNC #19360 merge.

| Iter | What | When |
|---:|---|---|
| 8 | S8 STATE-SYNC (#19360, MERGED 2026-05-16T03:53:49Z) | last state.md update |
| 9 | S9 PREP (#19403, MERGED 2026-05-16T03:51:53Z, no state.md edit) | first un-synced merge |
| 10 | S10 PREP (#19421, MERGED 2026-05-16T04:33:55Z, no state.md edit) | second un-synced merge |
| 11 | this STATE-SYNC (sync iterations 9 + 10 into state.md + JSON) | THIS PR |

Increment 8 → 11 (jumping 3 steps) reflects the two intermediate un-synced PREPs + this STATE-SYNC.

## 11. Cross-references

- **S6 PREP (#19221, MERGED 2026-05-15T18:05:30Z)** — IsBigO/IsLittleO bridge bearer audit.
- **S7 PREP (#19287, MERGED 2026-05-15T18:01:30Z)** — sibling-audit of S6, surfacing Bugs A-E.
- **S8 STATE-SYNC (#19360, MERGED 2026-05-16T03:53:49Z)** — post-drain state.md + JSON refresh.
- **S9 PREP (#19403, MERGED 2026-05-16T03:51:53Z)** — sibling-audit of S8 Active Approach, surfacing Bugs F + G.
- **S10 PREP (#19421, MERGED 2026-05-16T04:33:55Z)** — sibling-audit of S9 §5.1 + §5.2, surfacing Bugs H + I + J; ships paste-ready ~78-LOC three-artifact §5.1-§5.3 recipe + §6 sequencing notes.
- **S11 STATE-SYNC (this PR)** — absorb S9 + S10 into state.md + JSON; defer to S10 §5.1-§5.3 as authoritative recipe.
- **#19476 (OPEN, mechanic, meta drift)** — fixes `lineCount 383→471, theoremCount 8→9` in `meta.json`; strictly disjoint file scope from this STATE-SYNC.

---

**Researcher**: researcher-6 (worktree `.loom/worktrees/researcher-6/`).
**Branch**: `research/erdos-101-oq-01-s11-statesync-postdrain-1778910117` (based on `origin/main @ 2451a52d69e`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; verified at branch base; unchanged since S8 STATE-SYNC).
