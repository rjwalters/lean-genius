# S4 STATE-SYNC — post-#19378 + #19365 drain-wave absorption (doc-only)

**Date.** 2026-05-15 (UTC ~22:21)
**Researcher.** researcher-10
**Phase.** ACT-STATE-SYNC (iteration 8 → 9; status unchanged, Phase
description refreshed)
**Mode.** doc-only (state.md head edits + JSON `currentState` + this
new session memo); **zero** Lean / lake / lakefile / problem.md /
knowledge.md / `Proofs/FodorPressingDown.lean` edits.

## §1 TL;DR

Closes the **5-item partial-sync drift** left after the same-drain-wave
merges of:

* **#19378** (S2-β-α ACT, researcher-8, merged 2026-05-15T20:53:04Z,
  +3 Solovay Step 2 companions: `IsClubBelow.inter` +
  `IsStationaryBelow.inter_isClubBelow` +
  `IsStationaryBelow.inter_isLimitOrdinals`, +115 LOC, 0 sorries, 0
  axioms, build-verified at 3062 jobs in 7.2s).
* **#19365** (S3c PREP, researcher-11, merged 2026-05-15T20:53:36Z, 32s
  later — post-merge bearer drift recheck w/ Mathlib C9/C10 line
  corrections + gallery L1'–L6 lock-in + C1 binder transcription fix +
  Part VII section anchor cataloguing for the Part VIII insert).

These two PRs landed in the same drain wave but neither author
performed a full STATE-SYNC of state.md / JSON head. The drift items
are catalogued in §2 below.

This S4 STATE-SYNC matches the established pattern
`_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift`
(researcher-10 memory). Bumps iteration **8 → 9** (one step per
STATE-SYNC, not per absorbed PR).

## §2 Drift inventory (5 items)

| # | File | Location | Pre-S4 state | Post-S4 state |
|---|---|---|---|---|
| (a) | `state.md` | head L3 `## Phase: …` | "S2 ACT (Step I complete — limit ordinals form a club)" — silent on Step II foundations landed via #19378 | "S2 ACT (Step I + Step II foundations complete — limit-ordinal club + binary club intersection + stationary ∩ club preservation)" + new Iteration/Last-Updated block |
| (b) | `state.md` | L104 inside §Post-S2-α planning landed | `#TBD` placeholder for the S3c PREP entry | `#19365` (with merge timestamp + cross-reference to #19378 landing between #19251's merge and this entry) |
| (c) | `state.md` | L161 header `## Post-S2-α companions landed (S2-β-α ACT, 2026-05-16)` | Silent on PR number for #19378; date stamp incorrect (was 2026-05-16, actual merge 2026-05-15T20:53:04Z UTC) | Annotated with `merged #19378 2026-05-15T20:53:04Z` |
| (d) | `*.json` | `currentState.focus` | Mentioned S2-β-α ACT but **not** S3c PREP merge | Refreshed to mention both drain-wave merges + the 5 drift items closed |
| (e) | `*.json` | `lastUpdate` + `currentState.since` | `2026-05-16T02:00:00Z` (incorrect — written at S2-β-α ACT timestamp but in future; suggests the JSON was written with a clock-drift fudge factor) | `2026-05-15T22:21:00Z` (this session's actual ship time) |

**Iteration bump:** 8 → 9. JSON `currentState.iteration` was 8 (set by
S2-β-α ACT); S3c PREP was doc-only post-merge recheck which does NOT
bump iteration per repository convention (consistent with peer slugs).
This S4 STATE-SYNC bumps to 9.

**attemptCounts:** total 8 → 9, currentApproach unchanged (still 1
since we remain in the Solovay-splitting approach), approachesTried
unchanged (1).

## §3 Conflict-free guarantee

This PR touches ONLY:

| Path | Change |
|---|---|
| `research/problems/fodor-pressing-down-oq-04/state.md` | 4 in-place edits (head Phase + iteration block + L104 + L161); no new sections added (so the next ACT's chronological-append convention isn't disrupted) |
| `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-15-s4-state-sync-post-drain.md` | NEW (this file, ~110 LOC) |
| `src/data/research/problems/fodor-pressing-down-oq-04.json` | `currentState.{since,iteration,focus,nextAction,attemptCounts}` + `lastUpdate` (5 small edits) |

Files NOT touched:

* `proofs/Proofs/FodorPressingDown.lean` (no Lean changes)
* `proofs/lakefile.toml`, `proofs/lean-toolchain`, `proofs/lake-manifest.json`
* `research/problems/fodor-pressing-down-oq-04/problem.md`
* `research/problems/fodor-pressing-down-oq-04/knowledge.md`
* `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-16-s2b-alpha-act-club-inter-companions.md`
* `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-16-s3c-prep-post-merge-drift-recheck.md`
* Any sibling-slug files
* Any open / merged PR's branch state

Therefore: **zero merge-conflict possible** with the next S2-β ACT
(Part IX) regardless of who picks it up. The state.md in-place edits
add no new section, so an S2-β ACT just appends a
`## Post-S2-β-α + S3c append landed (S2-β ACT, …)` per the existing
chronological-append convention used at L88 and L161.

## §4 0-drift bearer recheck (spot-check, conflict-free with #19365 §2)

Sampling check at S4 STATE-SYNC ship time:

* **Mathlib pin** (`proofs/lake-manifest.json`):
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — **unchanged** since
  S3c PREP's audit at 2026-05-15T20:53Z.
* **`proofs/Proofs/FodorPressingDown.lean`** — **unchanged** since
  S2-β-α ACT at 2026-05-15T20:53Z (no commits to this file post-#19378
  per `git log origin/main -- proofs/Proofs/FodorPressingDown.lean`).
* **6 in-gallery bearers** locked by S3c §2 at lines
  L1'@53 / L2@59 / L3@343 / L4@259 / L5@366 / L6@408 — remain valid
  (file unchanged).
* **11 Mathlib bearers C1–C11** at corrected lines per S3c §2.2 —
  remain valid (Mathlib pin unchanged).

**No re-verification needed beyond #19365's table.** The S2-β ACT
picker can consume the S3c PREP table verbatim.

## §5 Why this is the right shape now (vs alternatives)

**Alternative A: Skip + claim another slug.** Rejected — the drift is
genuinely worth catching (the `#TBD` placeholder + stale Phase line +
JSON focus mismatch will confuse any future agent claiming this slug),
and the work fits a doc-only-≤25min budget cleanly.

**Alternative B: Pre-flight Docker build of `Proofs.FodorPressingDown`
to add a "build still verified" line to the JSON.** Rejected — the
Docker daemon on the host is hung at S4 ship time (`docker ps` times
out at 10s; `df -h /System/Volumes/Data` reports 100% capacity / 6.9 Gi
available; multiple concurrent `docker info` pile-up from peer
researchers; Docker Desktop in `error-dialog` process state). A
build attempt would block for ≥10min on container-never-reaches-build
state before timing out. The last verified build was at #19378
~2.5h ago at 3062 jobs in 7.2s; file unchanged + pin unchanged ⇒
build state should be unchanged.

**Alternative C: Pivot to S2-β ACT directly.** Rejected — S2-β ACT
requires Docker build (substantive Lean changes, ~150-180 LOC of new
theorem). Same Docker-daemon-blocked situation that motivated
shipping erdos-1151-oq-04 S32 ACT as `(build pending)` (PR #19482,
this researcher session prior iteration) applies here too. Better to
take the conflict-free doc-only win now and let the next ACT picker
attempt S2-β when Docker recovers.

**Alternative D: Wait for Docker recovery, then try S2-β ACT.**
Rejected — Docker daemon recovery time is unpredictable under 100%
disk pressure; my 90min claim TTL is the budget. Cheaper to ship the
STATE-SYNC and release the claim.

**Chosen: ship S4 STATE-SYNC.** ~12min cycle, conflict-free, no Docker
dependency, leaves the slug in a cleaner state for the next ACT
picker.

## §6 Pattern in memory

* **Primary match:** `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift`
  (researcher-12 2026-05-16T04:38-04:50Z frobenius-number-oq-03 PR
  #19458 prototype). This S4 STATE-SYNC matches the recipe almost
  verbatim — 5 drift items closed, iteration +1, no Lean / no meta /
  no build, ~12min cycle.

* **Distinct from `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer`** —
  no closures-as-superseded here (both drain-wave PRs are clean
  additive; no obsolete sibling PRs to retire).

* **Distinct from `_postship_pivot_lands_on_own_recent_act_merge_with_named_deferred_bearer_pencilwork`** —
  no deferred bearer pencilwork by this researcher (S2-β-α was shipped
  by researcher-8, S3c PREP by researcher-11; my pivot lands purely on
  housekeeping).

* **Distinct from `_sibling_act_shipped_between_statesync_and_claim_pivot_to_next_named_work_item`** —
  no STATE-SYNC named a specific paste-ready ACT body that's now
  been shipped; the prior `nextAction` (S2-β ACT) remains in place,
  unchanged by this PR.

## §7 Status

**Outcome:** PROGRESS (housekeeping; 5 drift items closed; iteration
8 → 9; FodorPressingDown.lean unchanged at 568 LOC / 21 declarations /
0 sorries / 0 axioms).

**Next:** S2-β ACT remains the named work item — append `§ Part IX`
to `FodorPressingDown.lean` with cofinal-sequence picking +
`fodor_anti_constant` + `stationary_splits_binary`, ~150-180 LOC,
0 new axioms. ACT-readiness gate per S3c PREP §-bearer-recap remains
GREEN with this STATE-SYNC's spot-check confirming no drift since
2026-05-15T20:53Z.

## §8 Provenance

* **Branch:** `research/fodor-pressing-down-oq-04-s4-state-sync-1778907700`
* **Base:** `origin/main` HEAD at claim time
* **Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged 9d)
* **Toolchain:** `leanprover/lean4:v4.26.0`
* **Researcher:** researcher-10
* **Cycle:** ~12 min (claim → push), of which ~3 min on Docker-daemon-pivot decision-making before settling on STATE-SYNC vs ACT path.

🤖 Generated by researcher-10 (S4 STATE-SYNC, post-#19378+#19365 drain-wave catchup)
