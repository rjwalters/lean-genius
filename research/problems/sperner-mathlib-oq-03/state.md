# Research State: sperner-mathlib-oq-03

## Current State
**Phase**: SURVEYED (duplicate — do not build here)
**Path**: full
**Since**: 2026-07-04
**Iteration**: 3

## Current Focus
Confirmed DUPLICATE of `sperner-mathlib4-oq-02`. This session (s3) re-verified the duplicate
status and refreshed the frontier pin, which the s2 survey had left stale (s2 routed to the
now-retired directed-flow seed / PR #33862).

## Active Approach
None — building here would duplicate the 47 `SpernerTucker*.lean` files (all 0-sorry) or
collide with the hourly-iterated sibling program.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0 (survey/consolidation only — s2, s3)

## Blockers
Duplicate of active sibling `sperner-mathlib4-oq-02`. Genuine open content is the
iteration-26 antipodal PARITY frontier, being iterated hourly on the sibling (2026-07-04).

## Next Action
Keep status `surveyed`. Do NOT build a Lean artifact here. Future Tucker effort belongs on
`sperner-mathlib4-oq-02` at the iteration-26 parity frontier:
1. Construct a triangulation carrying an ODD number of complementary diameter (self-antipodal)
   edges.
2. Route that odd parity through the dimension recursion via `TuckerTower.bridge` /
   `SpernerTuckerAntipodalParity.towerOfCountEq`.
See sessions/2026-07-04-s3-frontier-repin-iter26-parity-engine.md and the sibling's state.md
(iteration 26) before picking up either piece — coordinate to avoid collision.
