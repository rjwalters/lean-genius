# Research State: schroeder-bernstein-oq-03

## Current State
**Phase**: DEVELOP
**Path**: full
**Since**: 2026-07-02
**Iteration**: 2

## Current Focus
Even-stage collision move of the Myhill priority scheduler: routing a blocked fresh
domain point along the forward orbit to an escaping target.

## Active Approach
Stage-wise finite back-and-forth (Rogers §7.4). Collision step obligations:
(1) bounded termination — DONE (`fwdOrbit_chase_length_le`);
(2) correspondence preservation — DONE this session (`fwdOrbit_corr`/`chase_target_corr`);
(3) escape-existence (a fresh target actually exists) — OPEN, and found to be the real
    crux (see knowledge.md 07-02: naive counting fails on f-edge orbit re-entry; likely
    needs a stronger construction invariant than `BuiltFrom`).

## Attempt Count
- Approaches tried: 1 (stage-wise back-and-forth), in progress across sessions.

## Blockers
Escape-existence / termination of the collision routing. Finer than the earlier
`isGFree` Π₁ framing — blockers are named, but routing-termination is unproven.

## Next Action
Prove escape-existence for the collision step, or find the stronger stage invariant
that makes the chase stay in `mDom L` until escape. Then assemble the stage recursion
(matching chain + `firstMissing` coverage + read-off computable `ℕ ≃ ℕ`).
