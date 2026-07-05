# Research State: ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 2

## Current Focus
Scaffolded the `Measure.map` pushforward identity and its `uniformOn` corollary,
reducing both to the verified parent lemma `uniform_fiber_count`. File written but
NOT machine-checked (dual-tool blackout).

## Active Approach
Approach B (evaluate on measurable sets via `Measure.map_apply`), with the key
correction that the clean hypothesis is `MapsTo f A T` (not `SurjOn`). Bridge
`count ↔ ncard` on finite sets to reuse the combinatorial parent lemma verbatim.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Approach B)

## Blockers
Build verification blocked: Docker build wrapper (containerd blob I/O error) and
Aristotle proof service (404) both unavailable this session. File is build-pending.

## Next Action
Build `Proofs.BallotProblemOQ01OQ02OQ01OQ02OQ01` when Docker recovers; fix any
coercion/argument mismatches (likely spots: `ENNReal.mul_inv` args in
`uniformOn_map_eq`; `push_cast`/`nsmul_eq_mul` in `count_restrict_map_eq`). Then
create the gallery entry and mark verified.
