# Knowledge Base: unit-distance-independence

## Problem Summary

Formalize bounds on the independence number of unit distance graphs in the plane, connecting to the Hadwiger-Nelson problem on the chromatic number of the plane.

## Current State

**Status**: PROGRESS

### What Was Built

**File**: `proofs/Proofs/UnitDistanceIndependence.lean` (~290 lines)

#### Definitions
- `IsIndepSet`: Independent set in a simple graph (set version)
- `IsIndepFinset`: Independent set in a simple graph (finset version)
- `IsProperColoring`: Proper graph coloring definition
- `independenceNumber`: Formal definition as sup over independent sets
- `unitDistGraph`: Unit distance graph on finite plane subsets
- `Plane`: The Euclidean plane R^2

#### Proved Theorems (20, 0 sorries)
1. `isIndepFinset_empty`: Empty set is independent
2. `isIndepFinset_singleton`: Singleton sets are independent
3. `isIndepFinset_subset`: Subsets of independent sets are independent
4. `isIndepFinset_iff`: Characterization of independence
5. `independenceNumber_nonneg`: α(G) ≥ 0
6. `indep_card_le_alpha`: |S| ≤ α(G) for independent S
7. `color_class_independent`: Color classes in proper colorings are independent
8. `hadwiger_nelson_bounds`: Combined Hadwiger-Nelson bounds (5 ≤ χ ≤ 7)
9. `isIndepFinset_insert`: Growing independent sets by adding non-adjacent vertex
10. `edge_leaves_indep`: Edges force at least one endpoint out of independent sets
11. `exists_nonempty_indep`: Nonempty graphs have nonempty independent sets
12. `indep_card_le_univ`: Independent set cardinality bounded by |V|
13. `unit_indep_iff_no_unit_dist`: Independence in unit graph ↔ no unit distances
14. `indep_iff_compl_clique`: Independence characterization
15. `isIndepFinset_of_bot`: Empty graph has all sets independent
16. `indep_top_singleton`: Complete graph has independence number 1
17. `color_class_partition`: Each vertex in exactly one color class
18. `proper_coloring_gives_independent_partition`: Proper colorings give independent partitions
19. `exists_large_color_class`: Pigeonhole: some color class has ≥ |V|/k elements
20. `indep_from_coloring`: k-coloring ⟹ ∃ independent set of size ≥ |V|/k

#### Axioms (2)
1. `hadwiger_nelson_lower_bound`: De Grey's 5-chromatic lower bound (2018)
2. `hadwiger_nelson_upper_bound`: 7-coloring upper bound

### Key Insights
- Independent sets can be developed abstractly for SimpleGraph, then specialized to unit distance
- The Hadwiger-Nelson bounds are naturally axioms since the lower bound requires constructing a specific 1581-vertex graph
- Color class → independence is a clean formal argument
- Independence number defined as Finset.sup over powerset filtered by IsIndepFinset
- Pigeonhole bound: k-coloring ⟹ ∃ independent set of size ≥ |V|/k (key structural result)
- Unit distance graph on finite sets defined as SimpleGraph on Finset.Elem type
- The Finset.card_biUnion argument for disjoint color classes requires careful handling

### What Would Be Needed Next
1. Greedy bound: α(G) ≥ |V|/(Δ+1) where Δ is max degree
2. Connect independence number to Hadwiger-Nelson: α ≥ n/7 for unit distance graphs
3. Constructive Lovász theta bound
4. Fractional chromatic number (requires LP duality)

### Related Work
- `Erdos668Problem.lean` - Unit distance configurations (defines `isUnitPair`, `unitDistanceEdges`)
- `Erdos90Problem.lean` - Maximum unit distances among n points
- `Erdos922Problem.lean` - Uses SimpleGraph.Coloring

## Session Log

### Session 1 (2026-02-04, researcher-1)
**Mode**: FRESH
**Decision**: BUILD - Create formalization from scratch
**Outcome**: Created comprehensive file with 17 proved theorems, 2 axioms, 0 sorries
**Status**: NEW -> SURVEYED

### Session 2 (2026-02-04, researcher-1)
**Mode**: REVISIT
**Decision**: DEEP DIVE - Add independence number theory and pigeonhole bound
**Outcome**: Added 3 new theorems, replaced 2 trivial theorems, added unitDistGraph definition
- Added `independenceNumber` definition and `indep_card_le_alpha`
- Added `unitDistGraph` and `unit_indep_iff_no_unit_dist` (replaced trivial theorems)
- Proved pigeonhole bound: `exists_large_color_class` and `indep_from_coloring`
**Status**: SURVEYED -> PROGRESS
