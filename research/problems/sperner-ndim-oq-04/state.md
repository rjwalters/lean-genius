# Current State

**Phase**: ACT
**Since**: 2026-04-22T00:00:00.000Z
**Iteration**: 1

## Current Focus

Prove the non-revisiting invariant for kuhnWalk (that the algorithm never revisits a simplex). This is required to prove `kuhn_walk_reaches_fc` and `kuhnPathStart_is_fc`.

## Active Approach

The door graph component containing a boundary vertex is a path (not a cycle). This follows from:
1. Boundary vertices have degree 1 in the door graph
2. Paths in a graph have no cycles
3. The walk from a boundary vertex in a path-structured component must terminate

## Blockers

Non-revisiting invariant: requires showing that the door graph has no cycles containing boundary vertices. This needs an abstract graph theory argument about path components.

## Next Action

1. Try to prove `kuhn_walk_reaches_fc` using `Fintype.card` fuel bound
2. Check if `Finset.card` of visited set grows at each step
3. If so, fuel = Fintype.card K.Simplex is sufficient and non-revisiting follows from Pigeonhole

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
