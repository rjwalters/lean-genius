# H3 triple equality: exclude m=1,r=3 using matching coverage

Within the reviewed universal H3 triple partition, m=1,r=3,T=11 is excluded by exact induced-graph enumeration. Together with the separately reviewed m=1,r=4 and m=3 results, this leaves m=2 as the only possible T=11 matching size. It does not exclude m=2 or the full H3 profile, and does not prove existence at T=12. The universal lower bound remains T>=11.

This is a finite computational lemma, not a Lean theorem. The standalone standard-library verifier regenerates the entire normalized domain and every completion, uses exact integer arithmetic, and has no optimizer or timeout. Its accompanying JSON records every representative case. The graph-to-partition reductions remain those in the reviewed secondary, matching-capacity, and triangle-lower-bound notes.

## Normalization and completeness

Use E={u} union N union T2 union U1 union U2 union U3, with sizes 1,6,2,5,5,5, and R=N union T2. Every E vertex except u has E-degree4; u neighbors exactly N. Each Ui internal graph is a two-edge matching. At r=3, the three Ui-Uj matchings have sizes4,5,5. Permute blocks so the deficient matching is between blocks1 and2, and normalize the two full matchings from block0 to identity.

At m=1,T=11, the six special-singleton triangles and the single u-triangle leave only four additional triangles. The four unmatched N vertices are independent and belong to none of the seven known triangles. Empty-support triangle existence requires four distinct additional triangles through them. Consequently no triangle lies entirely in U.

Enumerate the third cross matching by choosing its missing domain and missing image (five choices each), then a bijection of the other four labels (24 choices), giving600 partial permutations. For each, enumerate the15 internal two-edge matchings independently in all three blocks. Exact C4 checks leave12720 triangle-free normalized configurations. The verifier also retains24360 one-triangle configurations to reproduce the broader saved domain; these are not used in m=1 completion.

Explicit relabelings consist of common permutations of the five labels and interchange of blocks1 and2, with the deficient matching inverted on interchange. Block0 remains distinguished by its two full cross matchings. The verifier asserts that its orbits are disjoint and cover the entire retained set. The triangle-free configurations have65 representatives. Restricting to these explicit graph relabelings is sufficient: a finer-than-isomorphism partition merely repeats cases.

Fix the single N matching edge. Enumerate epsilon (the T edge) and the possible zero-or-one N-neighbor of each T vertex, retaining r=3, ki+epsilon>=1 and C4-freeness on R union {u}. Explicit permutations preserving the N matching and interchange of the T vertices give seven representatives. The R relabeling is independent of the U relabeling before any U-R edge is selected. Their Cartesian product gives455 cases.

## Completion constraints

For each fixed U/R pair, set every required degree to4 minus the fixed degree. Each R vertex has at most one neighbor per Ui because all Ui vertices neighbor si. Thus enumerate disjoint subsets of R for the Ui vertices, with each subset size equal to that vertex's required R-degree. No subset contains two N vertices, which would create a C4 through u. An R vertex requiring three U-neighbors must occur in every block. At r=3 the required R-degrees of U vertices need not be1,1,1,1,2; the verifier computes them from the partial cross matching.

Combine the block options while enforcing exact R demands. Reject negative demand or demand larger than the number of blocks left; in the last block require exactly the remaining incidence mask. Adding an edge rejects precisely when an existing length-three path connects its endpoints, and adds its number of common neighbors to the E-triangle count e. Reject e>5, since six special-singleton triangles already consume six of the eleven triangles.

At a completed E graph, let S be the empty vertices not covered by an E-triangle or one of the six special-singleton triangles. There are Y=5-e remaining low triangles, each containing at least one nonempty vertex, hence at most two empty vertices. These two must be adjacent. Assign each vertex of S to one remaining triangle containing it. Triangles with two assigned vertices give disjoint edges, a matching in C[S]. If there are p pairs and q single assignments, |S|=2p+q and p+q<=Y. Therefore

    |S| - nu(C[S]) <= Y.

No disjointness of the original triangles is assumed; only the assigned vertex sets are disjoint. The verifier computes the maximum matching exactly by choosing a vertex v and taking the maximum of leaving v unmatched or pairing it with each available neighbor. This recursion strictly reduces the vertex set and memoizes integer masks. It also checks the weaker scalar empty/unmatched-N coverage inequalities.

## Result and limits

Every one of the455 cases exhausts its completion domain with no survivor under these necessary conditions. The earlier scalar-only diagnostic had surviving configurations, so the matching inequality is essential to this result; rejecting only the first saved configuration in a case would have been insufficient. This verifier continues through all completions in each case.

The result is conditional on the explicit universal H3 triple structure and on the finite enumeration's completeness. It uses no selected residual spectrum, no full order49 search, and no SAT certificate. It leaves the m=2,T=11 branch open.
