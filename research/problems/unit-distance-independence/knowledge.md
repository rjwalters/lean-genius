# Knowledge Base: unit-distance-independence

## Problem Summary

Formalize bounds on the independence number of unit distance graphs in the plane, connecting to the Hadwiger-Nelson problem on the chromatic number of the plane.

## Current State

**Status**: SURVEYED

### What Was Built (2026-02-04)

**New file**: `proofs/Proofs/UnitDistanceIndependence.lean` (~268 lines)

#### Definitions
- `IsIndepSet`: Independent set in a simple graph (set version)
- `IsIndepFinset`: Independent set in a simple graph (finset version)
- `IsProperColoring`: Proper graph coloring definition
- `Plane`: The Euclidean plane R^2

#### Proved Theorems (17, 0 sorries)
1. `isIndepFinset_empty`: Empty set is independent
2. `isIndepFinset_singleton`: Singleton sets are independent
3. `isIndepFinset_subset`: Subsets of independent sets are independent
4. `isIndepFinset_iff`: Characterization of independence
5. `color_class_independent`: Color classes in proper colorings are independent
6. `hadwiger_nelson_bounds`: Combined Hadwiger-Nelson bounds (5 ≤ χ ≤ 7)
7. `isIndepFinset_insert`: Growing independent sets by adding non-adjacent vertex
8. `edge_leaves_indep`: Edges force at least one endpoint out of independent sets
9. `exists_nonempty_indep`: Nonempty graphs have nonempty independent sets
10. `indep_card_le_univ`: Independent set cardinality bounded by |V|
11. `not_unit_dist_independent`: Non-unit-distance points are compatible
12. `all_diff_dist_independent`: Sets avoiding unit distance are independent
13. `indep_compl_clique`: Independence/clique duality (trivial direction)
14. `isIndepFinset_of_bot`: Empty graph has all sets independent
15. `indep_top_singleton`: Complete graph has independence number 1
16. `color_class_partition`: Each vertex in exactly one color class
17. `proper_coloring_gives_independent_partition`: Proper colorings give independent partitions

#### Axioms (2)
1. `hadwiger_nelson_lower_bound`: De Grey's 5-chromatic lower bound (2018)
2. `hadwiger_nelson_upper_bound`: 7-coloring upper bound

### Key Insights
- Independent sets can be developed abstractly for SimpleGraph, then specialized to unit distance
- The Hadwiger-Nelson bounds are naturally axioms since the lower bound requires constructing a specific 1581-vertex graph
- Color class → independence is a clean formal argument
- Growing independent sets by inserting non-adjacent vertices is useful infrastructure

### What Would Be Needed for Full Independence Number Theory
1. Formal definition of independence number as supremum
2. Constructive Lovász theta bound
3. Fractional chromatic number (requires LP duality)
4. Ramsey-type bounds relating independence and clique numbers

### Related Work
- `Erdos668Problem.lean` - Unit distance configurations (defines `isUnitPair`, `unitDistanceEdges`)
- `Erdos90Problem.lean` - Maximum unit distances among n points
- `Erdos922Problem.lean` - Uses SimpleGraph.Coloring

## Session Log

### Research Session (2026-02-04)
**Mode**: FRESH (researcher-1)
**Decision**: BUILD - Create formalization from scratch
**Outcome**: Created comprehensive file with 17 proved theorems, 2 axioms, 0 sorries
**Status**: NEW -> SURVEYED (meaningful infrastructure built)
