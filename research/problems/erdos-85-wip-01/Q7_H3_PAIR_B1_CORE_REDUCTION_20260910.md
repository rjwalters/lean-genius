# H3 adjacent-pair profile: 75 normalized nonempty cores

Status: exact primary regeneration PASS; independent review #1680 PASS. The unchanged-source replay reproduced the complete JSON; the independent audit also checked normalization coverage using all eight O2 automorphisms and rechecked every core, host set, and transversal triple. This is a paper and computational reduction, not a Lean theorem or a full profile exclusion.

Use the universal H3 pair-profile ledger, with pair vertex P_a missing high color a, six singleton vertices of each color, and 25 empty vertices. The identities are C1=7-t, Ct=3, and BC=J. A pair vertex cannot have two pair neighbors, since their support weight would already exceed 3. Thus a nonempty graph on the three pair vertices is a single edge, which we label P0-P1; P2 is isolated. This branch imposes no triangle count or spectral polynomial.

## Forced singleton structure

P0 has one singleton neighbor A of color 1; P1 has one singleton neighbor B of color 0. P2 has three singleton neighbors C,D,F of colors 0,1,2. These five special singletons are distinct, since a vertex with two pair neighbors would violate Ct=3. The remaining ordinary singleton classes O0,O1,O2 have sizes 4,4,5.

A special singleton has one singleton neighbor and four empty neighbors. Its singleton neighbor has the color missing from its pair neighbor. Thus A requires color 0, B requires color 1, and C,D,F require color 2. The only possible special-special edge is A-B, but P0-A-B-P1-P0 would be a C4. Consequently all five special neighbors are ordinary: A meets O0, B meets O1, and C,D,F meet O2.

Every ordinary singleton has exactly one singleton neighbor of each color and three empty neighbors. Its possible special neighbors all share one pair vertex, so it has at most one special neighbor. In particular the three targets of C,D,F in O2 are distinct.

The induced O0 and O1 graphs are perfect matchings on four vertices. The induced O2 graph is a two-edge matching with one unmatched vertex, which neighbors F. The O0-O1 graph is a matching of size 3; its two missing endpoints neighbor A and B respectively. The O0-O2 and O1-O2 graphs are matchings of size 4 covering O0 and O1. Their missing O2 endpoints neighbor C and D respectively. These endpoints are distinct from each other and from the internally unmatched O2 vertex. Every statement follows by subtracting the prescribed special incidences from the one-neighbor-per-color requirement.

## Complete normalization

Label O2 by 0 through 4, with unmatched vertex 0 and internal edges 1-2 and 3-4. Its two ordered missing cross endpoints lie either on the same internal edge or on different edges. The automorphisms of this two-edge matching send them respectively to (1,2) or (1,3), covering both types without exchanging their roles.

Label O0 by its bijection to the four O2 vertices other than the first missing endpoint, in increasing O2-label order. Label O1 in the same way using the second missing endpoint. Each of O0 and O1 can then have any of the three perfect matchings on four labels. Its O0-O1 matching has any missing endpoint in each class and any bijection of the remaining three labels: 4*4*6 = 96 possibilities. Therefore each type has 3*3*96 = 864 choices, totaling 1,728.

For an additional check the verifier enumerates the forbidden A-B alternative, in which O0-O1 is a perfect matching. This adds 216 choices per type; all are rejected by the C4 test. The full enumerated control domain has 2,160 choices. These extra controls are not needed for coverage of the valid branch.

The known nonempty graph has 24 vertices and 52 edges. Test C4-freeness by requiring every pair to have at most one common neighbor. The same-edge type retains 36 cores; the different-edge type retains 39. The known degrees are 4,4,5 on P0,P1,P2, 3 on the five special singletons, 4 on the thirteen ordinary singletons, and 8 on the three high vertices. All counts and degrees are asserted. The 75 retained objects are configurations covering the domain, not claimed isomorphism classes.

## Remaining empty incidences

P0 and P1 each require three empty neighbors; P2 requires two. These eight empty vertices are distinct by Ct=3. Each empty neighbor of P_a needs one singleton host of color a. An eligible host has no common neighbor with P_a in the known core; distinct empty neighbors of the same P_a must have distinct hosts, or they would share two neighbors.

For P0 the eligible hosts are C and the three cubic ordinary vertices of O0; for P1 they are D and the three cubic ordinary vertices of O1. For P2 they are F and the two cubic ordinary vertices of O2. The verifier checks host-set sizes 4,4,3 in every core. Selecting unordered subsets of sizes 3,3,2 covers all assignments up to relabeling the eight marked empty vertices, yielding 4*4*3 = 48 choices per core, or 3,600 cases.

The other 17 empty vertices have no pair neighbor and require a singleton neighbor of each color. Enumerate every transversal triple whose pairs have no known common neighbor. A selection cannot reuse a singleton pair. Special singleton demands are 4 and ordinary singleton demands are 3; subtracting the eight marked-host incidences leaves 5*4+13*3-8 = 51 incidences, or 17 triples. The eight marked empty vertices require five empty neighbors each, and the other seventeen require four each.

Run `python3 verify_q7_h3_pair_b1_core_reduction.py` to regenerate `q7_h3_pair_b1_core_reduction.json`. Its entire output agrees exactly with the independently reconstructed primary core data used for the initial diagnostic. This package only establishes the core and incidence domain; a full completion exclusion requires separate search and review.
