# Exclusion of residual orbit degrees (1,1,2,3,3)

Assume the N80/F10 cubic-fixed branch with displayed residual degrees. Use the two-cubic high-independence restriction submitted as2310, conditionally until accepted, and the deficit identities of accepted2297. Let C be the four cubic residual vertices, L the six other residual vertices, and D the two degree-two vertices within L. The four vertices of L minus D are leaves.

## The residual graph has only two initial shapes

The graph induced on C has maximum degree two and at most three edges, by the two-free-orbit bound and C4-freeness. The degree sum in L is eight, so e(C,L)=8-2e(L), and the degree sum in C gives

 e(C)=2+e(L).

Thus either e(L)=0,e(C)=2 or e(L)=1,e(C)=3. A free-involution-invariant graph on four vertices with two edges and maximum degree two must be2K2: the alternative P3 plus an isolated vertex has unique vertices that would be fixed. With three edges it must be P4, since a triangle plus an isolated vertex likewise cannot have a free involution.

Let x count degree-three attached involution orbits with no cubic residual neighbor and y count those with a cubic residual neighbor. The exact two-step budget rules out two cubic neighbors and forces the other two neighbors in the second kind to be leaves. In the first kind the support consists of both leaf orbits and D. Each such high orbit partitions all six vertices of L into two triples. Two such partitions would share a pair in some intersection and give a C4. Hence x<=1. We have x+y=n_311. Put t=n_211+2n_221.

By2310 high vertices have only degree-one W-neighbors. A degree-two attached vertex meets only noncubic residual vertices, from distinct involution orbits, so its support degrees are1+1 or1+2 and its residual defect degree is at least one. A high vertex of the first degree-three kind has support degrees1+1+2 and defect degree one. The accepted identities give

 t+2x+2y=5,
 e_E(R,W)=4(x+y)-2.

If y=0, the contributions just described give4x-2>=2t+2x, so t<=x-1. But t=5-2x and x<=1 contradict this. Thus y>0.

## A cubic-supported high orbit forces the unique residual configuration

For a high vertex v with residual support r,l,m where r is cubic and l,m are leaves, its five W-neighbors give five distinct endpoints in L. The R-middle walks give five other endpoints. All ten are distinct, so the latter comprise all four vertices of C and one vertex of L. In particular r has two neighbors in C and the leaf neighbors l,m supply the other two C endpoints.

Therefore C must be P4 and r a middle vertex. Its own label r is not among its C-neighbors, so one of l,m is its unique leaf neighbor. In particular both middle P4 vertices have a leaf neighbor, by involution symmetry. Every high orbit of this kind contains a vertex sharing r and its unique leaf; two such high orbits would make a C4. Hence y<=1.

Now e(L)=1, and its unique edge is invariant. It must join involution partners: it cannot join vertices from different involution orbits, since then its involution image would be a distinct edge. If this edge joined a leaf pair, one of the two leaf orbits would have no cubic neighbor. This is incompatible with the cubic-supported high orbit, which uses both leaf orbits and whose two leaves both have cubic neighbors. Hence the unique L-edge joins the two vertices of D.

Each vertex in D has one further neighbor, in C. These neighbors must be distinct: otherwise the common neighbor would be fixed by the involution. They form one C orbit. They cannot be the middle orbit, whose remaining degree is already used by its leaf neighbors. Thus they are the two P4 endpoints. The remaining four leaf incidences then attach one leaf to each C vertex.

In this configuration no degree-two attached vertex can meet D, since2310 requires every residual neighbor of such a vertex to have all of its residual neighbors in C, while each D vertex neighbors its partner in L. Thus all degree-two attached vertices meet two leaves and have residual defect degree two.

## All residual defect is used by the high vertices

The high contributions now give

 4(x+y)-2 >= 4t+2x.

Substitution of t=5-2x-2y gives22<=10x+12y. Since x<=1 and y<=1, equality is forced: x=y=1 and t=1. Thus there is exactly one211 group, two311 groups, and no221 group. Equality also means every degree-one attached vertex has zero residual defect degree.

There are exactly two attached vertices of residual degree two, namely the high orbit of the211 group. The two vertices of D each have seven neighbors in W, hence fourteen attached incidences in total. Only the high orbit counted by x meets D among all high vertices, contributing two incidences. Thus exactly twelve degree-one attached vertices have their unique residual neighbor in D.

For any such low vertex u, its seven W-neighbors contribute seven plus their excess residual degrees as two-step endpoints in R. Its residual neighbor contributes two endpoints and its fixed neighbor none. Its zero residual defect therefore says

 10 = 7 + sum over w in N(u) intersect W of (k(w)-1) + 2.

The sum is one. Hence u has exactly one W-neighbor of residual degree two and no W-neighbor of residual degree three. There must be twelve edges from these twelve low vertices to the two degree-two attached vertices.

But each degree-two attached vertex has at most two W-neighbors whose residual support lies in D. Indeed their singleton supports must be disjoint by C4-freeness, and |D|=2. The two degree-two vertices therefore support at most four such edges, contradicting twelve.

This excludes residual orbit degrees (1,1,2,3,3), conditional only on independent acceptance of2310 and the already accepted2297 premises. No finite enumeration, graph solver, capped search or Lean formalization is used. Other residual patterns remain outside this proof.
