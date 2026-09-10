# H3 independent-pair profile: exhaustive completion

Status: primary standalone regeneration PASS; independent review #1679 PASS. The unchanged-source independent replay reproduced every case record exactly and audited reduction and traversal completeness.

Under the universal H3 pair-profile reduction, the branch in which the three pair-support vertices are independent has no completion. This is a computer-assisted conclusion using a paper reduction and a standard-library Python enumeration, not a Lean theorem. It does not address the adjacent-pair branch or the global Erdős 85 problem. No triangle count or residual spectral polynomial is imposed.

The input reduction is `Q7_H3_PAIR_B0_CORE_REDUCTION_20260910.md` (independently reviewed as squad review 1674). The accompanying verifier regenerates all 320 normalized nonempty cores and retains 36 by exact common-neighbor checks. It does not load a saved core list. These are configurations covering the domain, not claimed isomorphism classes.

For each core, choose the two distinct singleton hosts of the two empty neighbors of each pair vertex. There are three possible hosts per pair vertex, giving 3 cubed = 27 choices, or 972 cases. The two empty vertices within each such pair are interchangeable, so unordered host choices cover all assignments. The six marked empty vertices have residual empty degree 5. The other 19 empty vertices have residual empty degree 4 and each has one singleton neighbor of each high color.

## Exhausting the singleton incidences

Generate every transversal singleton triple whose pairs have no common neighbor in the known core. Assign residual demands 4 to special singletons and 3 to ordinary singletons, then subtract the six marked-host incidences. Their sum is 57. An unmarked empty vertex contributes one eligible triple. No singleton pair may occur twice, since that would form a C4.

At each recursion node choose a singleton with positive demand. Enumerate every subset of eligible incident triples of size equal to that demand. Reject subsets with repeated pairs or negative residual demand. Subtract the demands and recur. Choosing the most constrained singleton changes only traversal order: every completion must supply exactly its remaining demand from this list. Previously exhausted singleton demands cannot receive further incidences. Positive demands strictly decrease, so the search terminates. A zero-demand leaf has exactly 19 triples, which may be assigned arbitrary distinct labels to the 19 interchangeable empty vertices.

At each leaf build the entire 49-vertex partial graph. Assert every nonempty vertex has its final required degree (7 for low vertices, 8 for high vertices) and every pair has at most one common neighbor. Only empty-empty edges remain absent.

## Exhausting the empty edges

A missing edge u-v can be added exactly when there is no existing length-three path from u to v. The verifier checks this by testing the intersection of N(v) with N(w) for each w in N(u). Since u and v are distinct and nonadjacent in a simple graph, such a walk has four distinct vertices and closes a C4. Existing edges are disallowed.

Two necessary gates first reject an empty vertex with fewer admissible neighbors than its residual degree, or without a subset of that size whose members have pairwise disjoint current neighborhoods. The second gate is necessary because two chosen neighbors sharing a neighbor would close a C4 through the root. Neither gate assumes any later edge is already present.

The full empty-edge recursion chooses an active vertex u and enumerates every subset of active admissible neighbors of size equal to its residual degree. Each edge is checked again after earlier edges in the subset are inserted. Neighbor residual degrees decrease by one; the root's demand becomes zero. A vertex with zero demand cannot receive later edges. Thus every completion is represented by a branch; future insertions cannot repair a C4 or a degree deficit. There is no timeout, node limit, triangle cutoff, or optimizer.

A completed leaf would assert all 49 degrees and all common-neighbor bounds and retain the full graph. No such leaf occurs.

## Reproduction and exact result

Run `python3 verify_q7_h3_pair_b0_full_exclusion.py`. It regenerates the cores and writes `q7_h3_pair_b0_full_exclusion.json`, with exact per-case counters. The script asserts all 972 cases were processed and none produced a graph.

The primary standalone run completed with 11,940,130 incidence recursion nodes, 249,526 incidence leaves, 390 empty-edge recursion nodes, and zero completed empty-edge leaves. Every retained per-case field agrees exactly with an earlier separate diagnostic run; that run also reported zero timeouts. The retained source differs from the completed standalone only in its description, output filename, scope string, and the final explicit no-graph assertion. Independent review #1679 completed both replay and reduction/traversal audit with PASS.
