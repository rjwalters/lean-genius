# A center-graph counting restriction for residual-matching D5/s5

Assume the cubic-fixed N80 branch with residual matching, five311 groups and five111 groups. Write X for the five311 centers, Y for the five111 centers. Every low vertex has at most one high neighbor (endpoint budget2, high cost2). A low involution pair is active when it has high neighbors, otherwise inactive.

Every low vertex has seven W-neighbors. At most one can belong to any fixed-center group, and none can belong to a group whose center is adjacent to its own center, since that creates a C4 through the center edge. The seven permissible groups are therefore each met exactly once.

For y in Y, let A_y be the set of centers in X whose high pair is adjacent to a low pair in B_y. Distinct active pairs in B_y give distinct X centers: otherwise a high vertex and y have two common low neighbors. Thus |A_y| counts the active low pairs among its three low pairs.

For x in X, xy is a center edge if and only if x is not in A_y. One direction is the forbidden cross-group W-edge C4. For the converse, if xy is absent, each of the six lows in B_y has one W-neighbor in B_x. These neighbors are all distinct (otherwise y and that vertex have two common neighbors), so this is a perfect matching between the two six-vertex groups. In particular both high vertices in B_x have neighbors in B_y, giving its active low pair.

Since y has total center degree3 and has5-|A_y| neighbors in X, it has |A_y|-2 neighbors in Y. Hence |A_y| is2 or3 and each111 group contains at most one inactive low pair. Let z be the number of these inactive pairs among the five111 groups. Exactly5-z vertices of Y have internal degree1; the others have degree0. Thus5-z is even, so z is odd.

If two Y vertices have |A_y|=2, their X-neighbor triples must intersect in at most one vertex by C4-freeness. Equivalently their two-element A sets are disjoint. At most two pairwise disjoint two-subsets fit inside X of size5. Therefore z<=2. Combined with oddness, z=1.

Consequently H[Y] is2K2 plus an isolate, the X-Y edge count is3+4*2=11, and H[X] has(15-11)/2=2 edges. There are exactly14 active low pairs among111 groups and exactly one inactive pair.

If m is the number of high-high edges, the ten highs have50 total W incidences, so there are50-2m high-low incidences. With50 lows each incident to at most one high, exactly2m lows are inactive, or m low involution pairs. Hence m>=1. This independently supplies a paper exclusion of the empty-high subcase, without any finite joint-row enumeration.

## Complete small normalized center cover

Normalize the unique Y vertex with three X-neighbors to label5 and its X-neighbor triple to{0,1,2}. The four other Y vertices have distinct two-element X-neighbor sets, none contained in that triple. Choose four of the seven permitted pairs and label them lexicographically. Enumerate all two-edge graphs on X and all three matchings of the other four Y vertices, keeping cubic C4-free graphs. Every possible center graph has such a labeling; uniqueness up to isomorphism is not claimed.

The original30-second integer enumeration completes in0.002768 seconds. It tests171 degree-compatible normalized graphs and retains93. In45 the two X edges share an endpoint, and in48 they are disjoint. This is a necessary center-graph cover only; attachment compatibility and full N80/Erdős85 remain unresolved. No Lean theorem or cap retry is claimed.
