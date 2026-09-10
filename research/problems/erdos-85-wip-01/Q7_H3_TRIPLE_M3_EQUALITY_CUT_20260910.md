# H3 triple equality: exclude m=3 at T=11 by finite induced enumeration

Conditional on the universal H3 triple structure, **m=3 implies at least12 all-low triangles**. Here m is the number of matching edges among the six empty neighbors of the distinguished empty vertex u. The universal bound remains T>=11, because equality for m=1 or2 is not addressed.

The result uses an exact finite enumeration of necessary induced-empty configurations. It is not a Lean theorem, does not choose a residual spectrum, and does not enumerate or exclude the entire order49 profile. Run `python3 verify_q7_h3_triple_m3_equality_cut.py`; it uses only the standard library, has no optimizer or time limit, and regenerates its adjacent JSON. A run takes roughly90 seconds on the development host.

## Reduction when m=3

Use the reviewed triple secondary and matching-capacity ledgers. E={u} union N union T2 union U1 union U2 union U3, with sizes1,6,2,5,5,5. The secondary parameters satisfy

    r=m+epsilon+k1+k2,    3<=r<=4,
    epsilon,ki in {0,1},  ki+epsilon>=1.

Thus m=3 forces r=4, epsilon=1 and k1=k2=0. The induced graph on R=N union T2 consists of a perfect matching on N and the edge joining the two T vertices. The vertex u neighbors all six N vertices and no Ui or T vertex.

Each C[Ui] is a two-edge matching. Every Ui-Uj cross graph is a perfect matching. Consequently each Ui has four vertices of U-degree3 and one unmatched vertex of U-degree2. As all Ui vertices have E-degree4, their required R-degrees are1,1,1,1,2.

Each T vertex has R-degree1 and E-degree4, hence three U-neighbors, one in every Ui. Each N vertex has E-neighbors u and its matching partner, hence two U-neighbors in distinct Ui. Each Ui therefore neighbors four of the six N vertices, with two omitted. The omitted N-pairs for the three Ui partition N. The doubled R-neighbor vertex in Ui cannot neighbor two N vertices, since those would form a C4 with u.

## Necessary triangle coverage at T=11

There are exactly six known all-low triangles involving the special singleton vertices si and the internal Ui matching edges. These cover four vertices of each Ui. Let e be the number of triangles entirely inside E. Three of these are the u/N matching triangles. If the full low graph has T=11, then e<=5, and its other5-e triangles contain at least one nonempty vertex, so each covers at most two empty vertices.

Let c be the number of empty vertices not covered by an E-triangle or by a known si triangle. Every empty vertex lies in some all-low triangle, by the existing empty-support positivity lemma. Therefore

    c<=2(5-e).

The enumeration checks this necessary coverage inequality; it does not assume that a configuration passing it extends to the ordinary singleton vertices.

## Complete induced search domain

First normalize two of the three Ui-Uj perfect matchings to the identity by relabeling vertices inside the blocks. The third is one of120 permutations. Each internal two-edge matching on five vertices has15 possibilities. Exhausting these choices and checking C4-freeness gives4680 configurations with at most two U-triangles:480 with zero,3480 with one,720 with two. More U-triangles would exceed the E budget5 after adding the three u triangles.

The verifier constructs explicit relabeling orbits using every permutation of the three blocks and every common permutation of their five labels, renormalizing the two cross matchings after a block permutation. It checks that the resulting disjoint orbits cover all4680 configurations. There are14 representatives, with triangle counts distributed2/10/2 for zero/one/two. Only equivalences supplied by explicit relabelings are used.

Fix the three N matching edges and the T edge by relabeling R. For each representative and each Ui:

1. Choose the two omitted N vertices.
2. Its six incident R vertices are the other four N vertices and both T vertices.
3. Choose the two R-neighbors of the unique U-degree2 vertex, excluding a pair of N vertices.
4. Bijection the four remaining R vertices to the other four Ui vertices.

These choices exhaust the required R-degree pattern. The three omitted N-pairs must be disjoint, ensuring each N vertex has its required two U-neighbors. Edges are added incrementally, rejecting an edge exactly when an existing length-three path would close a C4. Triangle counts increase by the number of common neighbors of its endpoints; branches exceeding five E-triangles are rejected. At a completed assignment the coverage inequality is checked.

No representative has a completion satisfying all these necessary conditions. Therefore T=11 is impossible when m=3. The verifier asserts that all14 representatives finished and that none produced a completion; it has no timeout path that could be mistaken for an exclusion.

## Limits

This finite result depends on the preceding graph-to-partition lemmas and on the completeness of the normalization and completion domain just described. The output is not a SAT/DRAT certificate or a full graph classification. It supplies no verdict for m=1 or2, no existence claim at T=12, and no whole H3 exclusion.
