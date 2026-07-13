# Research State: randomized-maxcut-oq-03

## Current State
**Phase**: ACT (complete)
**Path**: fast
**Since**: 2026-06-11
**Iteration**: 2

## Current Focus
S2 ACT shipped: `proofs/Proofs/RandomizedMaxCutOQ03.lean` (Docker-verified, 0
sorries, 0 axioms). Bipartite tightness witness for the parent's 1/2-approximation
guarantee. Also repaired the parent file's Mathlib v4.26.0 build break.

## Active Approach
Full-cut / proper-2-colouring characterisation of tightness; concrete `K_{m,n}`
witness via a self-contained `completeBipartite` graph.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Next Action
Problem essentially complete. Optional S3: upstream-style generalisation or
linking to Mathlib's `SimpleGraph.IsBipartite`. Otherwise mark completed.
