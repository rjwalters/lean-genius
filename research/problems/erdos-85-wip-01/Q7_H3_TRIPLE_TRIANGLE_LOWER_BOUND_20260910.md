# Universal H3 triple profile: at least eleven all-low triangles

Every H3 triple-profile graph has **at least11 all-low triangles**. This uses the universal matching-capacity structure and the established fact that every empty-support vertex lies in an all-low triangle. No residual spectrum is assumed. It strengthens the previous lower bound9 for this profile; it does not exclude the profile.

Use the notation of `Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md` and the reviewed refinement `Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md`. The empty set E has24 vertices and splits as {u}, U1,U2,U3,R; each Ui has5 vertices. The triple-support vertex z has neighbors u,s1,s2,s3, and N_C(si)={z} union Ui. The six empty neighbors N of u induce a matching of size m, with1<=m<=3.

## Known triangles

Each C[Ui] is a two-edge matching. Since si neighbors every vertex in Ui, these edges give exactly two all-low triangles through si. There are therefore six such triangles, using12 distinct empty vertices (four in each Ui). They are distinct across i because the Ui are disjoint.

Every low triangle through u corresponds to an edge in C[N]. There are exactly m such triangles: z has no other common C-neighbor with u, so z cannot participate. These m triangles cover u and2m distinct vertices of N. They are disjoint from the six si triangles as triangles and have no empty vertices in common with them.

Let X be the number of all-low triangles other than these6+m known triangles. If T is the total number of all-low triangles, then

    T=6+m+X.

## Two independent coverage inequalities

The known triangles cover12+(1+2m)=13+2m distinct empty vertices. Each of the remaining11-2m empty vertices must occur in some other all-low triangle. Each additional triangle covers at most three of those vertices, so

    3X>=11-2m.

The6-2m vertices of N unmatched by C[N] are independent: all edges of C[N] are its matching edges. None occurs in a known triangle. Every one of these empty vertices must occur in another all-low triangle, and any such triangle contains at most one of them. Thus

    X>=6-2m.

The required empty-vertex triangle property is the same actual-graph fact used by `orderFortyNine_lowLowLocalEdgeCount_pos_of_no_high` in `Erdos85OrderFortyNineLocalEdgePartition.lean`; equivalently their low local triangle incidence is positive.

## Integer conclusion

| m | Forced lower bound on X | Lower bound on T=6+m+X |
| --- | --- | --- |
|1|4, from unmatched N|11|
|2|3, from seven uncovered empties|11|
|3|2, from five uncovered empties|11|

The standalone arithmetic verifier checks these inequalities and the sharp scalar minima exactly. It does not construct graphs attaining the minima. The graph-to-coverage argument above is a paper derivation, not a newly supplied Lean graph theorem. The bound concerns all-low triangles; triangles involving high vertices are not included in T.
