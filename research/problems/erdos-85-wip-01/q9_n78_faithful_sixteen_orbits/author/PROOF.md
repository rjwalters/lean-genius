# Further necessary structure in the faithful order16 branch

Assume the faithful branch of accepted2422, under2419's matching normal form. Thus A=C2 x D8 has order16; write z for the C2 factor swapping the size2 orbit in S, and H=D8 for the factor fixing it. S has size6 with orbit sizes2+4, W has size48, and R has size24. H is free outsideS. Every outside A-orbit has size8 or16. Use2257's involution fixed-count bound6.

## Exactly one outside orbit has size8

A central involution cannot fix an outside vertex: its fixed set is A-invariant, hence would contain that vertex's entire A-orbit of size at least8, exceeding the bound6.

An outside orbit of size8 has an order2 point stabilizer intersectingH trivially, so its generator is z*h for an element h ofH with h^2=1. The choices h=1 and the central involution ofD8 make z*h central and are impossible by the preceding paragraph. Thus h is one of the four reflections. These give exactly two conjugacy classes of possible stabilizer generators inA, each of size2, and each generator has centralizer order8.

For an orbit A/<g> with such a stabilizer, g fixes |C_A(g)|/2=4 cosets. Every conjugate stabilizer from the same class has the same fixed character, so a fixed g in that class fixes4 vertices in each outside8-orbit of that type. Two such orbits would already give8 fixed vertices. There is therefore at most one8-orbit per reflection class, and at most two outside8-orbits in total.

If a is the number of outside8-orbits and b of outside16-orbits, then8a+16b=72, or a+2b=9. Thus a is odd. With a<=2, it follows that a=1 and b=4. Since R has size24 and is A-invariant, it must consist of the unique8-orbit and one16-orbit. W consequently consists of three16-orbits, all regular.

Each W vertex has a unique S-neighbor. Its orbit maps equivariantly onto one of the S-orbits. A regular16-orbit attached to S2 contributes8 neighbors at each target vertex; one attached to S4 contributes4. Every S vertex requires8 W neighbors. Therefore exactly one W16-orbit attaches to S2 and the other two to S4.

## The residual eight-orbit is a matching

Write R=X unionY with |X|=8 and Y regular of size16. Geometry2419 makes R cubic. The order2 stabilizer at x inX acts freely onY, so its Y-neighbor count is even and at most3, hence0 or2. Consequently its internal X degree is3 or1.

There is no simple C4-free cubic graph on8 vertices. To prove this, for any vertex v count its six nonreturning length-two paths. Their endpoints are distinct by C4-freeness. If t_v is the number of triangles throughv, exactly2t_v of those endpoints lie in N(v). Thus the union ofv, its3 neighbors and these6 endpoints has size10-2t_v<=8, giving t_v>=1. Meanwhile N(v) contains at most one edge: two edges in a three-vertex neighbor set form a length-two path and hence a C4 withv. Thus t_v=1 at every vertex. The graph would be partitioned into disjoint triangles, impossible on8 vertices.

It follows that X has internal degree1 and exactly2 Y neighbors per vertex. Balance gives eachY vertex exactly1 X neighbor and therefore internal degree2. Thus G[X] is a matching.

## The regular sixteen-orbit is two8-cycles

Since A acts regularly onY, its invariant degree2 graph is a Cayley graph for an inverse-closed two-element subset of A minus identity. The exponent of C2 x D8 is4. If the connection set is an inverse pair of order4 elements, the graph consists of4-cycles, forbidden. Otherwise the connection set consists of two distinct involutions a,b. If ab has order2, their Cayley components are4-cycles, also forbidden. The product cannot have order1 since a!=b, and its only other possible order is4. Then <a,b> is dihedral of order8 and the alternating Cayley components have length8. Hence G[Y] is exactly two disjoint8-cycles.

These constraints leave a matchingX8, two8-cyclesY16, and cross degrees2/1 inside the cubic residual graph. No claim is made that these or the W incidences can be completed to a candidate G. This is a necessary restriction only on the faithful order16 branch; the central-six-fixed branch is separate. No finite search, capped retry or Lean formalization is used. Independent review is requested.
