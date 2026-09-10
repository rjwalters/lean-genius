# H3 triple m=1,r=3: unrestricted singleton-neighborhood exclusion

All2590 diagnostic cases finished before their deadlines with no survivor. The primary standalone no-deadline replay passed and exactly reproduced all2590 case records. Independent review #1673 passed: its unchanged-source no-deadline replay exactly reproduced the complete JSON and audited the domain and graph implications. The adjacent JSON records the verified counts; the standalone verifier regenerates it.

The argument targets the entire m=1,r=3 branch of the universal H3 triple partition, without a triangle-count or spectral assumption. It combines with the other independently reviewed unrestricted branch exclusions to exclude the triple profile computationally. It does not exclude the H3 pair profile or solve Erdős85, and it is not a Lean theorem.

## Complete finite domain

Use the reviewed support, secondary, matching-capacity and singleton-resolution ledgers. E={u} union N union T2 union U0 union U1 union U2 has sizes1,6,2,5,5,5. The vertex u neighbors N, which induces one matching edge. Each Ui induces a two-edge matching. Every E vertex except u has E-degree4; u has E-degree6.

At r=3 the Ui-Uj cross matching sizes are4,5,5. Permute blocks so the deficient matching is between blocks1 and2; normalize the full matchings from block0 to identity. Enumerate all600 partial permutations (missing domain, missing image, remaining four-label bijection) and all15 internal matchings independently in each block. With no triangle cutoff,79650 C4-free normalized U configurations remain. Explicit common-label permutations and interchange of blocks1 and2 yield370 disjoint orbits covering all79650 configurations. Triangle counts0,1,2,3,4 have65,102,131,45,27 representatives respectively, all retained.

Fix the single N matching edge. Enumerate epsilon and the zero-or-one N-neighbor of each T vertex, retaining r=1+epsilon+k1+k2=3, ki+epsilon>=1 and C4-freeness on R union{u}. Explicit N permutations preserving the matching and interchange of the T vertices yield seven representatives. This is the same R classification as the reviewed m1r3 equality verifier. U and R relabel independently before adding U-R edges, giving7*370=2590 representative pairs.

## Exhaustive completion and singleton tests

The unrestricted completion engine is shared with the reviewed m3 and m1r4 singleton exclusions. Compute each required remaining degree as4 minus the fixed degree. Each R vertex has at most one neighbor in each Ui, by C4-freeness through si. Enumerate disjoint R subsets of the required sizes for the five vertices of each Ui; no subset contains two N vertices, by C4-freeness through u. R vertices requiring three U-neighbors must occur in every block. Enforce exact remaining demands and the exact final-block mask.

Adding an edge rejects precisely an existing length-three path between its endpoints. No E-triangle budget or triangle-coverage pruning is used.

For each completed E graph and color i, six ordinary singleton E-neighborhood triples must partition E minus({u} union Ui). Candidate triples have no common E-neighbor pair and at most one vertex in each Uj, accounting for the special singletons. Enumerate every exact cover by choosing an uncovered vertex and branching over every available triple containing it. Across colors, reject repeated empty pairs, which would create a C4 through two ordinary singletons.

For every joint cover, each ordinary singleton x must admit a distinct ordinary singleton neighbor y of each high color, by BC=J. The special singletons have no remaining low degree and x does not neighbor z, so neither can satisfy these obligations. An E edge between the E-neighborhood triples of x and y would make xy close a C4 along x-e-f-y. Reject any joint cover with no candidate y of a required color. This is only a necessary condition; it does not presume that all remaining candidate edges can coexist.

## Result and verification requirements

The completed diagnostic exhausted 1430102272 candidate extensions and 327252 completed E graphs across2590 cases, all rejected. Every case finished before its15-second deadline, so no deadline branch executed. The standalone standard-library verifier removes the deadline entirely, regenerates all input domains, asserts2590 cases and no survivor, and writes the adjacent JSON.

Both the primary and independent no-deadline replays agree casewise with these counts. The retained source adds only a docstring, output filename/scope and final no-survivor assertion to the completed private regeneration.

## Combined scope

The universal triple partition has m in{1,2,3} and r in{3,4}, with m3 forcing r4. Reviewed unrestricted results exclude m3 and m1r4. The separate m2 package covers both r values; this package covers m1r3. Independent reviews #1664, #1666, #1668 and #1673 have all passed; these cases exhaust the universal triple partition. The graph-to-partition reductions and finite enumerations remain mathematical/computational inputs, not a Lean kernel certificate. No statement about the remaining H3 pair profile follows.
