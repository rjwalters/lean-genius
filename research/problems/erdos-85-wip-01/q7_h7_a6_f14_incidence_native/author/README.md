# Native necessary singleton–pair projection API

This implements the family cover of reviews 2712/2713 and its exact incidence-choice model. It does not enumerate complete residual rows, add missing pair–pair edges, or run ARC. The API is intended for the already-reviewed a6 singleton-complete host inputs; its validator additionally checks symmetry, loop/range safety, high degrees/support multiplicities, singleton E/S degree patterns and mixed classes, pair degrees/no existing active edges, exact total demand/capacity 39, empty degrees/high common-neighbour coverage, and C4-freeness.

## Interface

`check_projection(uint64_t graph[49], int max_nodes, double deadline)` returns thread-local JSON through `const char *`. Copy the bytes before the next call on that thread. `projection_now()` returns the same monotonic clock used for deadlines. Nonfinite deadlines, malformed graphs and node caps outside 0..1000000 return INVALID. Research use remains capped at 10000 choice nodes per graph.

- EMPTY_FAMILY: a cited pair vertex has no necessary singleton family. The verifier must independently regenerate that family's eligibility and support matchings.
- INFEASIBLE_PROJECTION: complete families, capacities, variable order and a complete choice tree. Every alternative is represented by a capacity/C4 rejection or a child.
- FEASIBLE_PROJECTION: necessary singleton families and a full incidence assignment. This omits new pair–pair edges and is not a full graph witness.
- UNKNOWN: deadline or choice-node limit; no exclusion.

Family generation checks the deadline between pair vertices. Choice search checks it at every node. The node cap counts choice-tree nodes only; family generation is finite (at most 364 singleton triples per pair) and is subject to the shared deadline. Negative trees can be verified without native search. Allocation failure or invalid input never becomes an exclusion.

## Qualification

151 valid host fixtures comprise all 23 final F12 cases and 128 uniformly spaced cases from F14's already-reviewed negative prefix. The native results match the reviewed Python family and choice models: 91 empty families and 60 complete negative trees, with exact family/order/branch/node equality. These fixture runs do not revisit the capped F14 suffix and confer no new case exclusions.

Controls cover expired deadlines, zero and exact-boundary node caps, negative caps, null/zero/asymmetric/self-loop/out-of-range graphs and nonfinite deadlines. The sampled valid graphs are all negative. The positive serialization/search path is instead exercised by an explicitly synthetic internal choice-engine fixture (nine linear triples and twelve singleton choices, exact capacity 39), plus negative/CAP/support-matching controls under AddressSanitizer and UndefinedBehaviorSanitizer. That unit fixture is not represented as a valid H7 graph.

This packet qualifies an implementation of an already-reviewed necessary model. No new F14 remaining-domain pass or full F14/H7/kernel/global theorem is asserted here.
