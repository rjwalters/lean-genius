# Research State: sperner-ndim-oq-05

## Current State
**Phase**: BLOCKED
**Path**: full
**Since**: 2026-04-21T07:30:34-07:00
**Last Updated**: 2026-04-27T18:58:00Z
**Iteration**: 13 (estimated from knowledge.md session log)

## Current Focus
All formalization work is **COMPLETE**. Both Mathlib-targeted files
(`SpernerMathlib4.lean` Part 1, `SpernerSimplicialInstance.lean` Part 2)
have **0 sorries**, run at the Mathlib-default `maxHeartbeats 200000`,
and use granular imports — they are PR-ready as of session 11
(2026-04-26). Mathlib issue #25231 remains OPEN (last activity
2026-04-24, 16 comments) and still asks for a Part 2 contributor.

## Active Approach
None — current state is awaiting external action.

## Attempt Count
- Total attempts: 12+ documented sessions across
  heartbeat optimization, granular imports, boundary-flip proofs,
  mathlib audit, and SpernerGrid corrections.

## Blockers

**[USER ACTION REQUIRED]** This problem cannot make further forward
progress from a research agent. Two human-only steps remain:

1. **Refresh** the `rjwalters/mathlib4:sperner-abstract-parity` branch
   with the current `SpernerMathlib4.lean` (Part 1) — the gallery file
   is already PR-ready.
2. **Submit** a Mathlib PR pointing at Part 1, and **comment** on
   mathlib4#25231 referencing `SpernerSimplicialInstance.lean` (Part 2)
   so reviewers can see the full chain.

Optional follow-up research problem (separable from this OQ):
- Fix `SpernerGrid.lean`'s 4 remaining sorries (chiefly
  `boundary_doors_odd`, which needs a canonical-orientation
  redesign + induction on `d`, ~300–500 lines). This is independent
  of the Mathlib contribution and tracked as a separate concern.

## Next Action

**For the agent loop**: release the claim and skip — there is no
research progress to be made until a human submits the Mathlib PR.

**For the human reviewer**: see `knowledge.md` Session 11 (2026-04-26)
for the precise PR-submission checklist; both files are at
`proofs/Proofs/SpernerMathlib4.lean` and
`proofs/Proofs/SpernerSimplicialInstance.lean`.
