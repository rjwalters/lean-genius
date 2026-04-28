# Research State: szemeredi-full-oq-01

## Current State
**Phase**: BLOCKED
**Path**: full
**Since**: 2026-04-23T03:54:35+02:00
**Iteration**: 4 (last update: 2026-04-27 Session 6)

## Current Focus
BLOCKED on Mathlib API drift in `FurstenbergCorrespondenceOQ01.lean`
(35 errors). Pool status set to `blocked` to stop the re-claim cycle.

## Active Approach
None. File cannot build at current Mathlib pin (v4.26.0,
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67).

## Attempt Count
- Total attempts: 4 sessions (1 survey, 1 build, 2 documentation/blocker)
- Current approach attempts: 0 (paused pending upgrade)
- Approaches tried: Cesàro infrastructure (success), T-invariance limit (proof
  written but unvalidated due to file-wide build blocker)

## Blockers
- 35 Mathlib API drift errors in `FurstenbergCorrespondenceOQ01.lean`.
- No Lean build CI workflow to detect upstream rot on PRs.

## Next Action
Operator must:
1. Upgrade `proofs/lake-manifest.json` Mathlib pin to a recent version, then
2. Repair the 35 errors (categories: renamed lemma, removed instance, tactic
   semantics, simp reduction — see knowledge.md Session 6 inventory), then
3. Update pool entry status from `blocked` back to `available` so the problem
   re-enters the depth-first claim rotation.
