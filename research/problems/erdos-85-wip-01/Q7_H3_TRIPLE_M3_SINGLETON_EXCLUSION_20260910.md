# H3 triple m=3: unrestricted singleton-neighborhood exclusion

Standalone verification and independent review #1664 passed. The independent unchanged-source replay reproduced every count and the complete JSON; the domain and graph implications were audited.

The finite result excludes m=3 in the universal H3 triple partition without assuming an all-low triangle count or a residual spectrum. It leaves m in {1,2}; neither the H3 triple profile nor Erdős85 as a whole is excluded. This is an exact computational argument, not a Lean theorem.

## Exhaustive induced domain

Use the reviewed universal support, secondary and matching-capacity ledgers. Empty vertices E partition into {u}, N, T2, U0,U1,U2 of sizes1,6,2,5,5,5. The six N vertices neighbor u, and their induced graph is a matching with m edges. Each Ui induces a two-edge matching, and the secondary edge count r lies in {3,4}.

At m=3 the identity r=m+epsilon+k1+k2, together with ki+epsilon>=1, forces r=4, epsilon=1 and k1=k2=0. Thus R=N union T2 consists of three matching edges on N and the edge joining the T vertices. Each Ui-Uj graph is a perfect matching. Every E vertex except u has E-degree4, while u has E-degree6.

Normalize two cross matchings to identity and enumerate the third among120 permutations. Each internal two-edge matching on five vertices has15 possibilities. Reject C4s by incremental edge insertion. With no triangle cutoff,10050 normalized U graphs remain. Explicit block permutations and common permutations of five labels, followed by renormalization, give29 disjoint orbits covering all10050 graphs. The triangle counts0,1,2,3,5 have respectively2,10,2,11,4 representatives. Triangle counts are recorded only to describe the domain; none is excluded for having too many triangles.

Fix the R matching edges by relabeling. Complete U-R edges by assigning disjoint subsets of R to the five vertices of each Ui, with subset sizes given by4 minus the fixed U-degree. Disjointness follows because an R vertex cannot have two neighbors in Ui without a C4 through si. A subset cannot contain two N vertices, which would give a C4 through u. R vertices need two U-neighbors when in N and three when in T2; those with demand3 must appear in every block. Track remaining demands exactly, reject impossible demands, and require the exact remaining mask in the last block.

Each new edge is rejected precisely when an existing length-three path joins its endpoints. Edges are new, endpoints distinct, and all checks are integer operations. Completed E graphs have all required degrees and are C4-free. There is no E-triangle budget or triangle-coverage pruning in this verifier.

## Joint singleton resolution

The reviewed singleton-resolution ledger supplies six ordinary singleton vertices of each high color. Their three-element E-neighborhoods partition E minus ({u} union Ui) for color i. Candidate triples have no pair with a common E-neighbor and at most one vertex in each Uj. The latter condition accounts for the known special singleton sj. Across colors, no empty pair may repeat in two triples, which would give a C4 through their ordinary singleton vertices.

For each completed E graph, enumerate all triples satisfying these restrictions and all exact covers for each color. The recursion chooses an uncovered vertex and branches over every available triple containing it. Every exact cover occurs because it contains exactly one such triple. All triples of per-color covers are then tested for pair-disjointness. Labels of the six ordinary singletons in a color are irrelevant; each partition represents every relabeling of those singleton vertices.

## Required ordinary-singleton neighbors

Passing joint resolution is still insufficient. Each ordinary singleton x must have one singleton neighbor of each high color, by BC=J. It has no z-neighbor, and each special si has its low degree exhausted by z and Ui, so all these required neighbors are ordinary singletons.

Let Qx and Qy be the E-neighborhood triples assigned to two distinct ordinary singletons. If an E edge joins a vertex of Qx to a vertex of Qy, the edge xy would close a C4 along x-e-f-y. Therefore xy can be present only if there are no E edges between Qx and Qy.

For every joint cover, the verifier checks every ordinary singleton x and each of the three colors j for at least one distinct ordinary singleton y of that color with no E edge between Qx and Qy. If any required color lacks such a candidate, reject the cover. This is only a necessary condition; it does not assume that all candidate edges can be selected simultaneously or that the resulting singleton graph is C4-free. A survivor would require further work.

## Verification and scope

The standalone standard-library verifier regenerates the entire U domain, all29 orbits, every U-R completion, and all joint singleton partitions. It has no optimizer or time limit. A completed run with no survivor excludes exactly the m=3 branch under the stated universal triple partition. It does not exclude m=1 or2, a prescribed residual polynomial, or any other high-count profile.

The earlier m=3,T=11 exclusion is weaker and remains independently valid. This argument removes the triangle-count assumption by adding singleton-neighborhood feasibility. The two explicit resolution fixtures in the earlier ledger are illustrative only and are not substituted for exhaustive completion here.

The complete run exhausted all29 cases, with 346243632 candidate extensions and 83616 completed E graphs, and no survivor. Per-case completion counts agree with the prior unrestricted resolution run except U26, where the stronger color-degree test continues beyond its former first survivor; that case independently exhausted 14136816 extensions and 4800 leaves. The retained source differs from the successful standalone run only in its output filename/scope, top docstring and final no-survivor assertion.
