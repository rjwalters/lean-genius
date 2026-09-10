# H3 triple m=1,r=4: unrestricted singleton-neighborhood exclusion

Standalone verification and independent review #1666 passed. The unchanged-source independent replay reproduced every case count and the complete JSON; domain and graph implications were audited.

This finite result excludes m=1,r=4 in the universal H3 triple partition, without a triangle-count or spectral assumption. It leaves m=1,r=3 open, and makes no conclusion about the m=2 branch or the whole H3 profile. It is a computational argument, not a Lean theorem.

## Complete induced domain

Use the reviewed universal support, secondary, matching-capacity and singleton-resolution ledgers. E={u} union N union T2 union U0 union U1 union U2 has sizes1,6,2,5,5,5. The vertex u neighbors all six N vertices. C[N] has one matching edge; each Ui has two internal matching edges. All other empty vertices have E-degree4, while u has E-degree6.

At r=4, all three cross graphs Ui-Uj are perfect matchings. Normalize two to identity, enumerate the remaining permutation and all15 internal matchings in each block. With no U-triangle cutoff,10050 normalized C4-free U graphs remain. Explicit block/common-label permutations followed by renormalization give29 disjoint orbits covering all10050 configurations. This is the unrestricted domain used in the m3 singleton-exclusion verifier; triangle counts are descriptive and no value is discarded.

The secondary relation r=m+epsilon+k1+k2, with each ki and epsilon in {0,1}, forces epsilon=k1=k2=1 here. Enumerate every possible N-neighbor of each T vertex, retaining C4-freeness on R=N union T2 together with u. Quotient only by explicit N permutations preserving the single matching edge and interchange of T vertices. The same complete R enumeration as the reviewed m1r4 equality verifier yields four r4 representatives. U and R relabel independently before U-R edges are added, giving4*29=116 representative pairs.

## Completion and singleton conditions

The completion engine computes every U and R vertex's required remaining degree as4 minus its fixed degree. Each R vertex has at most one neighbor in any Ui, since all Ui vertices share the special singleton si. Enumerate disjoint subsets of R for the five Ui vertices with the required sizes. No subset contains two N vertices, by C4-freeness through u. An R vertex needing three U-neighbors must occur in every block. Enforce exact remaining R demands, reject demands exceeding the number of blocks left, and require the exact final incidence mask.

New edges are rejected precisely when an existing length-three path joins their endpoints. There is no E-triangle budget and no triangle-coverage pruning. Thus every C4-free induced E completion with the required degrees is considered.

For each completed E graph, each high color needs a partition of E minus ({u} union Ui) into six ordinary-singleton neighborhood triples. Enumerate all candidate triples with no common E-neighbor pair and at most one vertex in each Uj, then all exact covers by choosing an uncovered vertex and branching on every available triple containing it. Across colors, reject a repeated empty pair, which would create a C4 through two ordinary singletons.

For every joint cover and every ordinary singleton x, each of the three colors must have a distinct ordinary singleton y that could neighbor x. This follows from BC=J; special singletons have their low degrees exhausted, and ordinary singletons do not neighbor z. If an E edge joins the neighborhood triple of x to that of y, xy would create a C4 via x-e-f-y. Therefore a joint cover is rejected when x has no candidate y of some required color with no E edge between the two triples. This necessary condition does not assume simultaneous realizability of candidate singleton edges.

## Scope

The standalone standard-library verifier regenerates both normalized domains and all116 completion cases, without an optimizer or timeout. Exhaustion with no survivor excludes the entire m=1,r=4 branch, rather than just T=11. It does not classify possible m=1,r=3 completions. The result remains dependent on the explicit universal triple partition and finite enumeration; it does not supply a Lean kernel proof or solve Erdős85.

The standalone run exhausted all116 cases, 201886536 candidate extensions and 48788 completed E graphs, with no survivor. Every case count agrees with the earlier bounded diagnostic, whose116 cases all finished without timeout. The retained source differs only in output filename/scope, docstring and final no-survivor assertion.
