# H3 triple m=2: unrestricted singleton-neighborhood exclusion

All602 diagnostic cases finished before their deadlines with no survivor. The primary standalone no-deadline replay completed and reproduced every case count and the complete case JSON. Independent review #1668 passed: its unchanged-source replay reproduced all counts and the complete JSON, and the domain and graph implications were audited.

The finite argument excludes m=2 within the universal H3 triple partition at every triangle count, by the completed exhaustive checks. It covers both r=3 and r=4 without selecting a residual spectrum. Combined with the reviewed m=3 and m=1,r=4 exclusions, it leaves only m=1,r=3. It is not a Lean theorem or an exclusion of the full H3 profile.

## Exhaustive U and R domains

Use the reviewed support, secondary, matching-capacity and singleton-resolution ledgers. E={u} union N union T2 union U0 union U1 union U2 has sizes1,6,2,5,5,5. The vertex u neighbors N; C[N] is a two-edge matching. Each Ui is a two-edge matching, all other E vertices have E-degree4, and u has E-degree6. The secondary parameter r is3 or4.

At r=4 all three Ui-Uj cross graphs are perfect matchings. Normalize two to identity and enumerate the third among120 permutations, together with all15 internal matchings in each block. Explicit block/common-label relabelings cover all10050 C4-free normalized U graphs in29 disjoint orbits. No U-triangle count is discarded.

At r=3 the cross sizes are4,5,5. Put the deficient matching between blocks1 and2, normalize the two full matchings from block0 to identity, and enumerate all600 partial permutations and internal matchings. Common-label permutations and interchange of the two deficient-endpoint blocks give370 disjoint orbits covering all79650 normalized C4-free U graphs. They contain65/102/131/45/27 representatives with0/1/2/3/4 triangles; all are retained. The orbit verifier explicitly checks disjoint coverage, and uses no isomorphism library.

Fix the two N matching edges by relabeling. Enumerate the T edge epsilon and the zero-or-one N-neighbor of each T vertex, retaining r=m+epsilon+k1+k2 in{3,4}, ki+epsilon>=1 and C4-freeness on R union{u}. Explicit N permutations preserving the matching and interchange of T vertices give eight r4 representatives and one r3 representative. For r3, epsilon=1 and k1=k2=0, so R consists of the two N matching edges and the T edge. U and R relabel independently before any U-R edge is chosen. Thus the full product domain has8*29+1*370=602 cases.

## Degree completion

For each U/R pair, compute required remaining degrees as4 minus the fixed degree. Each R vertex has at most one neighbor in any Ui, by C4-freeness through si. Enumerate disjoint R subsets for the five Ui vertices, with each subset of the required size. No subset contains two N vertices, which would give a C4 through u. Every R vertex requiring three U-neighbors must appear in every block.

Combine block options while enforcing exact R demands. Reject negative demands or demands larger than the number of blocks left, and require precisely the remaining incidence mask in the final block. New edges are rejected exactly when an existing length-three path joins their endpoints. There is no triangle budget or triangle-coverage pruning.

## Singleton feasibility

For color i, the six ordinary singletons have three-element E-neighborhoods partitioning E minus({u} union Ui). Enumerate all eligible triples: no pair may have a common E-neighbor, and each triple has at most one vertex in each Uj. The latter accounts for the special singleton sj. Enumerate every exact cover by branching over every available triple containing a chosen uncovered vertex. Across colors, reject repeated empty pairs, which would create a C4 through two ordinary singletons.

For each joint cover, every ordinary singleton x must have a possible distinct ordinary singleton neighbor of each of the three high colors. This follows from BC=J; z and the special singletons cannot supply such a neighbor. If an E edge joins the E-neighborhood triple of x to that of y, xy would close a C4 along x-e-f-y. Thus reject a joint cover whenever some x has no candidate y of a required color with no E edge between their triples. This necessary test does not assume simultaneous realizability of the remaining candidate edges.

These completion and singleton tests are the same unrestricted engine as the independently reviewed m3 and m1r4 exclusions, now applied to the full m2 domain.

## Reproduction and limits

The standalone standard-library verifier regenerates the normalized domains, orbits, U-R completions and singleton partitions with exact integer operations and no timeout. It asserts602 completed cases and no survivor, then writes the adjacent JSON. The completed diagnostic recorded 1694708736 candidate extensions and 403760 completed E graphs, all rejected. Each diagnostic case ended before its15-second deadline, so its timeout branch was never reached; the standalone version removes that branch entirely.

The result depends on the universal H3 triple partition and the exhaustive finite domains described above. It does not eliminate the H3 pair partition, the remaining m1r3 triple branch, or any other high-count sector, and it does not solve Erdős85. It is not a Lean kernel certificate.
