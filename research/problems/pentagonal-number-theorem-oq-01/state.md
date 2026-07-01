# Research State: pentagonal-number-theorem-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-30T14:50:55-07:00
**Iteration**: 1

## Current Focus
Part 12 VERIFIED: Franklin's Move B + the two moves are mutually inverse
(`franklinMoveB_franklinMoveA` / `franklinMoveA_franklinMoveB`), completing the
involution skeleton on non-fixed distinct-part partitions. 0-axiom.

## Active Approach
Franklin's combinatorial involution. Next: glue the Move A/B headlines into a single
`franklinInvolution` dispatching on staircase length, then the cancellation sum.

## Attempt Count
- Total attempts: 12
- Current approach attempts: 12
- Approaches tried: 1

## Blockers
None. (Docker daemon down this session — verified via host `lake env lean` fallback.)

## Next Action
Part 13: a staircase-length `ℓ` definition so Move A/B dispatch on `s ≤ ℓ` vs `s > ℓ`
directly, then assemble `franklinInvolution` toward
`∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n`.
