# H3 triple profile: combined computational exclusion

All branches of the universal H3 triple profile have been excluded by independently replayed finite computations. The conclusion depends on the explicit paper graph-to-partition reductions and exhaustive Python searches. It is not a Lean kernel theorem, does not address the H3 pair profile, and does not solve Erdős 85 as a whole.

The input reductions are `Q7_H3_SUPPORT_EDGE_LEDGER_20260910.md`, `Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md`, `Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md`, and `Q7_H3_SINGLETON_RESOLUTION_LEDGER_20260910.md`. They apply without fixing a triangle count or residual spectrum.

The six neighbors N of the distinguished empty vertex induce a matching with m in {1,2,3}. The secondary edge count r is in {3,4}. If epsilon denotes the edge between the other two secondary vertices and k1,k2 their numbers of N-neighbors, then epsilon,k1,k2 are in {0,1}, each ki+epsilon is at least 1, and r=m+epsilon+k1+k2. For m=3, epsilon=0 would force both ki=1 and r=5, while epsilon=1 forces both ki=0 and r=4. Hence exactly the five parameter pairs below remain.

| Branch | U/R cases | Candidate extensions | Completed E graphs | Independent review |
| --- | ---: | ---: | ---: | --- |
| m=3, r=4 | 29 | 346,243,632 | 83,616 | 1664 PASS |
| m=1, r=4 | 116 | 201,886,536 | 48,788 | 1666 PASS |
| m=2, r=3 or 4 | 602 | 1,694,708,736 | 403,760 | 1668 PASS |
| m=1, r=3 | 2,590 | 1,430,102,272 | 327,252 | 1673 PASS |
| Total | 3,337 | 3,672,941,176 | 863,416 | All PASS |

The source, case JSON, and detailed proof for each row are the corresponding `Q7_H3_TRIPLE_M3_SINGLETON_EXCLUSION_20260910.md`, `Q7_H3_TRIPLE_M1_R4_SINGLETON_EXCLUSION_20260910.md`, `Q7_H3_TRIPLE_M2_SINGLETON_EXCLUSION_20260910.md`, and `Q7_H3_TRIPLE_M1_R3_SINGLETON_EXCLUSION_20260910.md` packages. Each independent unchanged-source run had no deadline and reproduced the entire retained case JSON. The totals above were recomputed from those four JSON files.

Every case is rejected. The searches regenerate all normalized induced domains, enumerate all exact degree completions, and enumerate all eligible singleton-neighborhood exact covers. Their final necessary condition requires every ordinary singleton to have an eligible ordinary singleton neighbor of each high color. An empty-empty edge between two assigned neighborhoods forbids that singleton edge by C4-freeness. No simultaneous realization of candidate singleton edges is presumed: absence of any required candidate already rules out the graph.

The branch domains cover every parameter pair furnished by the universal reduction. Since each branch has no surviving completion, no graph satisfying that H3 triple partition exists. Earlier triangle-count-specific exclusions are unnecessary for this final union; all four searches retain every triangle count. The pair-profile computations are combined with this result in `Q7_H3_PROFILE_EXCLUSION_20260910.md`. The Lean status of this triple-profile reduction is recorded below.


## Lean structural reduction status (2026-09-10)

The following actual-graph consequences now compile without `sorry`, using only `propext`, `Classical.choice`, and `Quot.sound`, and have passed independent squad source review:

- `Erdos85OrderFortyNineThreeHighTripleSecondaryPartition.lean` derives the actual partition with U15, R8, N6 and T2 (review1693).
- `Erdos85OrderFortyNineThreeHighTripleSecondaryMatching.lean` derives that the induced N graph is a matching with one to three edges (review1697).
- `Erdos85OrderFortyNineThreeHighTripleFarVertex.lean` derives that each vertex of T has an R-neighbor and the far-parameter lower bound (review1699).
- `Erdos85OrderFortyNineThreeHighTripleEdgeLedger.lean` derives e(U)=17+e(R) and q+2e(R)=26 from the actual degree masses60 and32, where q counts U-to-R edges (review1705).
- `Erdos85OrderFortyNineThreeHighTripleBlockTwoEdges.lean`, `TripleUnionEdges.lean`, and `TripleCrossCounts.lean` (with the same full prefix) derive two internal edges per special block, e(U)=20 or21, and the labeled555/455 cross-count patterns (reviews1701,1702,1704).
- `Erdos85OrderFortyNineThreeHighTripleSecondaryEdgeCases.lean` combines these results to derive r=3 or4, q=20 or18 respectively, m<r, and exactly the five (m,r) cases listed above (review1706).
- `Erdos85OrderFortyNineThreeHighTripleOrdinaryColorNeighbor.lean` derives that each ordinary singleton has an ordinary singleton neighbor of each high color, with an empty neighborhood of size3 and no empty edge crossing the two neighborhoods (review1707).

These theorems derive their numeric conclusions from the actual order49 C4-free graph with minimum degree7 and three high vertices, together with the triple profile and specified actual roots where needed. They do not take the partition sizes, edge counts, or candidate-compatibility conclusions as assumptions.

The finite branch exclusions above are still Python computations. The Lean structural results do not yet certify the normal-form enumeration or the exhaustive rejection of all completions. In particular, no unconditional Lean H3 exclusion follows from this progress.
