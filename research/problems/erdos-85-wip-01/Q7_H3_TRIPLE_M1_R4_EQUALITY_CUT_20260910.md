# H3 triple equality: exclude m=1, r=4 at T=11

Conditional on the reviewed universal H3 triple partition, m=1 and r=4 imply at least 12 all-low triangles. This exact finite induced-graph computation does not exclude m=1,r=3, either m=2 branch, or the whole H3 profile. The universal bound remains T>=11. The m=3 equality branch was excluded separately.

The verifier uses only Python standard-library integer arithmetic and exhaustive finite loops, with no optimizer or timeout. Run `python3 verify_q7_h3_triple_m1_r4_equality_cut.py` to regenerate the adjacent JSON. This is a computational lemma with explicit reductions, not a Lean theorem.

## Partition and equality reduction

Use Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md, Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md and Q7_H3_TRIPLE_TRIANGLE_LOWER_BOUND_20260910.md. The empty vertices partition as E={u} union N union T2 union U1 union U2 union U3, with sizes 1,6,2,5,5,5. Write R=N union T2. The vertex u neighbors exactly N inside E. C[N] is a matching with m edges. Each other empty vertex has E-degree 4.

There are six distinct known triangles involving special singleton vertices si, one for each internal Ui matching edge, and m distinct triangles through u. The 6-2m unmatched N vertices are independent and belong to none of these known triangles. Each must lie in some additional low triangle, and no such triangle contains two of them. At T=11 there are only 5-m additional triangles. Thus at most (5-m)-(6-2m)=m-1 additional triangles avoid unmatched N. In particular C[U] has at most m-1 triangles. For m=1, C[U] is triangle-free.

At r=4, every Ui-Uj cross graph is a perfect matching, and each C[Ui] is a two-edge matching. Normalize two cross matchings to the identity; enumerate the third permutation and all 15 internal matchings in each block. The verifier regenerates the same explicit relabeling orbits as the reviewed m=3 verifier. Its 480 triangle-free U configurations form two orbits. It checks disjoint coverage by explicit block permutations and common label permutations; no graph-isomorphism library is used.

Fix the single matching edge in N. For the two T vertices, enumerate their possible N-neighbor (none or one) and their mutual edge epsilon. Retain r=m+epsilon+k1+k2=4, ki+epsilon>=1, and C4-freeness on R union {u}. The ki+epsilon condition is the reviewed fact that each T vertex has at most three U-neighbors. Quotient only by explicitly enumerated permutations preserving the N matching and interchange of T vertices. There are four r=4 representatives. U and R relabel independently before choosing any U-R edges, so their Cartesian product covers all eight cases.

## Complete U-R completion domain

For a fixed case, the required U-degree of each R vertex is 4 minus its already fixed degree in R union {u}. The required R-degree of each U vertex is 4 minus its U-degree, hence 1,1,1,1,2 in every block. Each R vertex has at most one neighbor per Ui, since two would form a C4 through si. Thus enumerate disjoint subsets of R of these required sizes for the five Ui vertices. A subset cannot contain two N vertices, since these would form a C4 through u. Every R vertex needing three U-neighbors must appear in every block.

Block options are combined while tracking the remaining required degree of every R vertex. Negative demands, or demands larger than the number of blocks left, are rejected. The final block must have exactly the remaining incidence mask. Every edge is checked for an existing length-three path between its endpoints, which is precisely the condition that adding this new edge creates a C4. All added edges are new and join distinct vertices.

The exact number e of E-triangles is tracked by common-neighbor counts on edge insertion. The six known si triangles imply e<=5 at T=11, so exceeding five rejects a branch. At a completed E graph, mark all vertices covered by E-triangles or known si triangles. If c empty vertices remain uncovered, and b of those are unmatched N vertices, the remaining 5-e low triangles require

    c <= 2(5-e),    b <= 5-e.

The first holds because each remaining triangle contains a nonempty vertex and hence at most two empty vertices. The second uses independence of unmatched N. Empty-support triangle existence supplies the coverage requirement. These are necessary conditions only; a passing induced graph would not establish a full order49 graph.

## Result

All eight cases finish with no completion passing the necessary coverage conditions. In (R index,U index) order, the candidate-extension counts are 286080, 424320, 1093440, 2004096, 1360416, 1945632, 2433192, and 4567528. The verifier asserts absence of a survivor in each case and completion of all eight cases. It has no time-limit exit.

This excludes precisely m=1,r=4,T=11 within the universal triple partition. The remaining T=11 cases are m=1,r=3 and m=2,r in {3,4}. No full-profile exclusion follows.
