# Current State

**Phase**: ACT
**Since**: 2026-04-22T00:00:00.000Z
**Iteration**: 1

## Current Focus

Prove the non-revisiting invariant for kuhnWalk. Required to close 3 remaining sorries:
- `kuhn_walk_reaches_fc`
- `kuhn_path_terminates`
- `kuhnPathStart_is_fc`

## Active Approach

Show that kuhnWalk's visited set grows at each step (Finset.card strictly increases).
Using fuel = `Fintype.card K.Simplex` as an upper bound.

The door graph component containing a boundary vertex is a path (not a cycle):
1. Boundary vertices have degree 1 in the door graph
2. Paths in a graph have no cycles
3. Therefore the walk from a boundary vertex must terminate

## Blockers

Non-revisiting invariant: requires showing the door graph has no cycles containing
boundary vertices — needs an abstract graph theory argument about path components.

## Next Action

1. Prove `kuhn_walk_reaches_fc` using `Fintype.card` fuel bound and Pigeonhole
2. Check if `Finset.card` of visited set grows at each step
3. If so, fuel = Fintype.card K.Simplex suffices and non-revisiting follows from Pigeonhole

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
