# Research State: szemeredi-full-oq-01

## Current State
**Phase**: ACT (un-BLOCKED post Session 7 / PR #14878 — 1 sorry remaining)
**Path**: full
**Since**: 2026-05-17T00:50:00Z (S8 STATE-SYNC absorbs Session 7 ~14 d catchup)
**Iteration**: 8 (last update: 2026-05-17 — Sessions 1, 2, 5, 6, 7, plus this S8)

## S8 STATE-SYNC (researcher-3, 2026-05-17T00:50Z, doc-only)

**Why S8 fires**: knowledge.md "Session 7" (2026-05-02) reported PROGRESS:
6 Mathlib API drift root errors fixed via PR #14878 (merged 2026-05-02T21:18:35Z).
But state.md head + JSON `currentState.phase` / `iteration` / `lastUpdate` /
`focus` / `nextAction` / `blockers` + registry `phase` / `lastUpdate` were
NEVER updated post-Session 7. The slug carried `Phase: BLOCKED` for 14 days
past its un-blocking, mis-signaling to the pool / claim-rotation / Judge /
Auditor that the slug was still pre-Mathlib-fix.

Additionally, the pool entry `status: "available"` was set by some operator
(not Session 7's author) between 2026-04-27 and 2026-05-17, putting the slug
back into the claim rotation despite state.md still flagged BLOCKED. The
re-claim cycle that Session 6 explicitly wanted to stop has resumed.

**Pre-S8 drift inventory** (8 items):

| # | Surface | Pre-S8 | Should be | Severity |
|---|---|---|---|---|
| 1 | `state.md` Phase | `BLOCKED` | `ACT` (post-Session 7) | **HIGH** |
| 2 | `state.md` Iteration | `4 (last update: 2026-04-27 Session 6)` | `8` | HIGH |
| 3 | `state.md` Current Focus | `BLOCKED on Mathlib API drift ... 35 errors` | post-fix narrative | HIGH |
| 4 | `state.md` Active Approach | `None. File cannot build` | `limit_invariant_on_cylinder` proof | HIGH |
| 5 | `state.md` Blockers | `35 Mathlib API drift errors` | discharged via PR #14878 | HIGH |
| 6 | JSON `currentState.phase` | `BLOCKED` | `ACT` | HIGH |
| 7 | JSON `currentState.{focus, nextAction, iteration, blockers, attemptCounts}` | pre-Session-7 | Session-7-aware | HIGH |
| 8 | JSON `lastUpdate` + registry `phase` / `lastUpdate` | 2026-04-27 / OBSERVE / 2026-04-24 | 2026-05-17 / ACT / 2026-05-17 | MED |
| (bonus) | `sessions/` dir | ABSENT | bootstrap with S8 memo | LOW |

**S8 closes all drifts in a 4-file doc-only motion**:

1. `state.md` head — Phase BLOCKED → ACT; Iteration 4 → 8; Since refresh;
   prepend this S8 block above the historical sections (preserved verbatim
   below as "Current Focus (HISTORICAL — pre-Session 7)"); rewrite
   "Current Focus" / "Active Approach" / "Blockers" / "Next Action" to
   post-Session-7 state.
2. `src/data/research/problems/szemeredi-full-oq-01.json` — 7 edits:
   - `currentState.phase` BLOCKED → ACT
   - `currentState.focus` rewrite (Session 7 fixes + 1 sorry remaining)
   - `currentState.nextAction` rewrite (limit_invariant_on_cylinder next)
   - `currentState.iteration` 4 → 8
   - `currentState.attemptCounts` { total: 0, 0, 0 } → { 7, 1, 3 } (schema
     was zero'd; corrected per session history)
   - `currentState.blockers` 2-entry → [] (Mathlib drift discharged)
   - `lastUpdate` 2026-04-27 → 2026-05-17T00:50:00Z
3. `research/registry.json` — `phase` OBSERVE → ACT (Session 7 fixed errors,
   active development resumed); `lastUpdate` 2026-04-24 → 2026-05-17T00:50:00Z.
4. NEW `sessions/2026-05-17-s8-statesync-post-session7-mathlib-fixed-bootstrap.md`
   (~200 LOC, 9 sections).

**Explicit non-actions** (out of scope for S8 STATE-SYNC):
- No `.lean` edits. (Session 7 already shipped PR #14878 with the fixes;
  next Lean work is `limit_invariant_on_cylinder` activation at line 779,
  which is S9 ACT — needs Docker recovery + careful Prokhorov ingredient
  audit per knowledge.md Session 7 Next Steps.)
- No build verification. (Docker `info` hangs in 5 s; Session 7's "file
  should now be buildable" assertion is unverified by S8 — flagged in
  honesty calibration §7 of the S8 sessions memo.)
- No `knowledge.md` body edits. (Session 7 epilogue is the canonical
  Session 7 record; S8 is a state-syncing wrapper, not a new substantive
  session.)
- No `meta.json` edits. (Slug `szemeredi-full-oq-01` has gallery dir
  `src/data/proofs/szemeredi-full-oq-01/` but the numerics are mechanic
  territory; this S8 doesn't refresh them.)
- No `problem.md` / sibling slug / `lake-manifest.json` edits.
- No pool status change. (Pool was `available` pre-claim; was `in-progress`
  during my claim; will be `in-progress` post-this-PR-merge until Session 9
  validates the build; S8 author chooses NOT to invoke
  `FORCE_COMPLETE=1 update`. Per knowledge.md Session 7 step 4 the intended
  transition is "→ available once build confirmed", which S8 cannot
  perform without Docker.)

## Current Focus (POST Session 7 + S8 STATE-SYNC)
PR #14878 (merged 2026-05-02) fixed 6 Mathlib API drift root errors
(cascading to ~35 build failures) in `FurstenbergCorrespondenceOQ01.lean`.
File is presumed buildable at pin `2df2f0150c…` (v4.26.0) per Session 7's
assertion, but NOT yet Docker-verified in S8 (Docker `info` hangs;
host-cron territory).

**Remaining work** (1 real sorry):
- `limit_invariant_on_cylinder` at line 779 of
  `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`. The 60-line proof
  structure is documented in the file comment at line ~760. Once Docker
  recovers, S9 ACT can paste the proof and verify build.

## Active Approach (POST Session 7)
T-invariance limit proof via Prokhorov ingredients in Mathlib v4.26.
Cesàro infrastructure (Session 2) and `shift_iterate` / `cylinder_isClopen`
/ indicator / Boolean compact-space repairs (Session 7) all GREEN.

## Attempt Count (POST Session 7)
- Total attempts: 7 sessions (1 survey, 1 Cesàro, 1 proof-write blocked,
  1 documentation, 1 Mathlib API repair via PR #14878, 2 documentation).
  Plus S8 this STATE-SYNC.
- Current approach attempts: 1 (Session 7's Mathlib repair, merged)
- Approaches tried: Cesàro / T-invariance limit / Mathlib API repair

## Blockers (POST Session 7 + S8)
- None at the slug level. Slug is in an ACT-ready state for `limit_invariant_on_cylinder`.
- Host-side: Docker `info` hangs (5 s no Server: section) and disk 3.4 Gi
  avail (< 30 Gi cascade-safety floor). These are HOST blockers, not
  slug-content blockers. S9 ACT requires host recovery.

## Next Action (POST Session 7 + S8)
**S9 ACT** (Lean edit, host-recovery-gated):
1. Recover Docker daemon + free ≥ 30 Gi host disk.
2. `docker info` returns < 5 s + `df -h /` shows ≥ 30 Gi avail.
3. Build-verify current `main` HEAD compiles: `./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01`.
4. If build clean: paste the 60-line `limit_invariant_on_cylinder` proof at
   line 779 (structure documented in file comment line ~760).
5. Rebuild + ship S9 ACT PR.

After S9 ACT: S10 ACT for `seqCompact_probabilityMeasure_cantor`
(~150-200 lines via Prokhorov ingredients in Mathlib v4.26).

## Current Focus (HISTORICAL — pre-Session 7, frozen)
BLOCKED on Mathlib API drift in `FurstenbergCorrespondenceOQ01.lean`
(35 errors). Pool status set to `blocked` to stop the re-claim cycle.

## Active Approach (HISTORICAL — pre-Session 7)
None. File cannot build at current Mathlib pin (v4.26.0,
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67).

## Attempt Count (HISTORICAL — pre-Session 7)
- Total attempts: 4 sessions (1 survey, 1 build, 2 documentation/blocker)
- Current approach attempts: 0 (paused pending upgrade)
- Approaches tried: Cesàro infrastructure (success), T-invariance limit (proof
  written but unvalidated due to file-wide build blocker)

## Blockers (HISTORICAL — pre-Session 7)
- 35 Mathlib API drift errors in `FurstenbergCorrespondenceOQ01.lean`.
- No Lean build CI workflow to detect upstream rot on PRs.

## Next Action (HISTORICAL — pre-Session 7)
Operator must:
1. Upgrade `proofs/lake-manifest.json` Mathlib pin to a recent version, then
2. Repair the 35 errors (categories: renamed lemma, removed instance, tactic
   semantics, simp reduction — see knowledge.md Session 6 inventory), then
3. Update pool entry status from `blocked` back to `available` so the problem
   re-enters the depth-first claim rotation.

**Note**: items 1+2 were DISCHARGED by Session 7 / PR #14878 (2026-05-02).
Item 3 was performed by an unidentified operator some time between
2026-04-27 and 2026-05-17. S8 STATE-SYNC absorbs all three transitions
into the canonical surfaces.
