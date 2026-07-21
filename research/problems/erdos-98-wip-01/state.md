# Research State: erdos-98-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-21
**Iteration**: (see knowledge.md session log)

## Current Focus
Lower bound `h 5 ≥ 3` ⟺ no general-position `PointConfig 5` is a two-distance set.
Reduction + degree structure + degree-3 exclusion + **2-regularity all proved**. Only the
`C₅` endgame (2-regular ⟹ regular pentagon ⟹ concyclic contradiction) remains.

## Active Approach
Short-distance-graph structure. Degree bounds (1–3) + handshake parity + degree-3 exclusion
now yield **full 2-regularity** (`two_distance_two_regular`, this session): every vertex has
exactly two short neighbours. Degree-3 exclusion assembled from the four sub-cases
(`no_short_degree_three`, this session). Remaining: 2-regular ⟹ C₅ ⟹ regular pentagon ⟹
concyclic ⟹ contradiction with NoFourConcyclic.

## Attempt Count
- See knowledge.md session log.

## Blockers
`h 5 ≥ 3` now reduces to the **C₅ endgame** (pure): from `two_distance_two_regular`, force a
single 5-cycle, then a regular pentagon, then concyclicity, contradicting `NoFourConcyclic`.
No known obstruction — it is a (nontrivial) Lean formalization effort. Hardest piece:
2-regular graph on 5 vertices is a single 5-cycle (not triangle+edge) — a pure graph fact.

## Next Action — C₅ ENDGAME (see knowledge.md "Next Steps" for full detail)
1. **Cyclic order.** From `two_distance_two_regular`, build a 5-cycle permutation `σ` of
   `Fin 5` with each vertex's two `a`-neighbours `= σ i, σ⁻¹ i`. Need the graph fact
   "2-regular on 5 vertices ⟹ connected single cycle" (rules out triangle+disjoint-edge;
   note the mono-triangle is already killed by `no_four_equidistant_indices`, but a general
   K₃-component needs the pure count/connectivity argument). Consider `SimpleGraph.IsCycle`
   API or a direct `Fin 5` case analysis on the ≤ (5−1)!/2 = 12 cyclic orders.
2. **Regular pentagon ⟹ concyclic.** All five `a`-edges equal + cyclic ⟹ regular pentagon;
   its 5 vertices lie on one circle (circumcircle of 3 consecutive vertices + law-of-cosines,
   or an explicit order-5 rotation `ρ`).
3. **Contradiction.** Feed 4 of the concyclic points to `NoFourConcyclic`. Closes `h 5 ≥ 3`.
