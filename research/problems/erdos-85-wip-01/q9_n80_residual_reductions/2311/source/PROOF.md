# Exclusion of residual orbit degrees (1,1,1,3,3)

Assume the N80/F10 cubic-fixed branch with three residual leaf orbits and two cubic residual orbits. Let C be the four cubic vertices and L the six leaves. Use the high-independence and exact defect formula submitted as2310, conditionally until accepted. The deficit identities are accepted2297.

## The cubic vertices induce a path on four vertices

In a graph invariant under a free involution, a vertex in two involution orbits has at most two neighbors within those orbits: its partner and at most one member of the other orbit. Both members of the other orbit would give it and its partner two common neighbors. Thus C induces maximum degree two and at most four edges; four edges would be a C4. Hence e(C)<=3.

Writing e(L) for the number of leaf-leaf edges, the degree sums give e(C,L)=6-2e(L) and12=2e(C)+e(C,L). Consequently e(C)=3+e(L). Therefore e(L)=0, e(C)=3 and all leaves attach to C. A simple graph on four vertices with three edges and maximum degree two is either P4 or a triangle plus an isolated vertex. The latter is impossible under a free involution, since the unique isolated vertex would be fixed. Thus C induces P4.

Its involution reverses the path. Its middle vertices form one orbit and each has exactly one leaf neighbor; its endpoints form the other orbit and each has two leaf neighbors.

## At most one orbit of each kind of degree-three attachment

Every attached vertex of residual degree two has only leaf residual neighbors by2310. Its residual defect degree is4-2=2.

An attached vertex v of residual degree three either meets three leaves, or one cubic vertex and two leaves. Two cubic neighbors violate the exact two-step budget from2297. Let x count high attached involution orbits of the first kind, and y those of the second kind; thus x+y=n_311.

For the first kind, the two vertices of its orbit partition L into two triples. Indeed residual neighbors lie in distinct involution orbits. Two such partitions of six points have four intersections with total size six, so some intersection has size at least two. The corresponding attached vertices would have two common residual neighbors. Hence x<=1. By2310 each of these high vertices has residual defect degree5-3=2.

For the second kind, let v meet a cubic vertex r and leaves l,m. Its five W-neighbors all have residual degree one by2310 and give five distinct endpoints in L. Its R-middle walks give d(r)+d(l)+d(m)=5 further endpoints, all distinct and disjoint from the first five. Therefore the latter endpoints comprise all four vertices of C and exactly one vertex of L.

The endpoints contributed by l,m are in C, and r has at most two C-neighbors. In order to cover all four vertices of C, r must have exactly two C-neighbors. It is consequently a middle vertex of the P4. Of the four C endpoints, r itself is not contributed by r, so one of l,m must be the unique leaf adjacent to r. Thus every such attached vertex contains in its residual support the pair consisting of a middle vertex r and its unique leaf neighbor.

An entire high involution orbit of this kind uses both middle vertices, one per high vertex. Two different high orbits of this kind would therefore contain two distinct vertices sharing r and its leaf, a C4. Hence y<=1. Each high vertex of this kind has residual defect degree5-(3+1+1)=0.

## Contradiction from the total defect

Put t=n_211+2n_221, the number of high attached orbits of residual degree two. The accepted2297 identities for a=3,b=0,c=2 are

 t+2x+2y=6,
 e_E(R,W)=4(x+y).

The degree-two high vertices contribute4t residual defect edges; the degree-three high vertices meeting only leaves contribute4x. All other contributions are nonnegative. Hence

 4(x+y)>=4t+4x, so t<=y.

Substituting into the deficit equation yields

 6=t+2x+2y <=2x+3y <=5,

a contradiction. Thus residual orbit degrees (1,1,1,3,3) are impossible.

The proof depends on2310 and2297 and does not assume E(R,W) is empty. No finite enumeration, graph solver, capped-search result or Lean formalization is used. The pattern11233 and other residual patterns remain outside this exclusion.
