# Research State: erdos-98-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-21
**Iteration**: (see knowledge.md session log)

## Current Focus
Lower bound `h 5 ≥ 3` ⟺ no general-position `PointConfig 5` is a two-distance set.
Reduction proved on the combinatorial side; parity obstruction gives one degree-2 vertex.

## Active Approach
Short-distance-graph structure: degree bounds (1–3) + handshake parity ⟹ some vertex
has exactly 2 short neighbours. Pushing toward full 2-regularity ⟹ C₅ ⟹ regular
pentagon ⟹ concyclic ⟹ contradiction with NoFourConcyclic.

## Attempt Count
- See knowledge.md session log.

## Blockers
Full 2-regularity requires the geometric step (rule out short-degree 3); pure graph
theory does not force C₅.

## Next Action
Prove `∀ i, d_a(i) = 2` (rule out degree 3, equiv. degree 1 by a↔b symmetry) using
no-3-collinear / no-4-concyclic on the three short-neighbours around a vertex.
