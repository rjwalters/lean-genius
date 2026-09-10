# Universal H7 singleton-degree-distribution bound

Let a be the number of empty-empty edges. In the14vertex singleton-induced graph, let z,l,h count degrees1,3,5. A singleton with e empty neighbours has singleton degree5−2e, so z counts double-empty hosts. The incidence ledger gives l+2z=49−4a and h+l+z=14.

In any C4-free14vertex graph, for a vertex v the number of length-two walks ending away from v is sum(deg(w)−1,w adjacent v)<=13: two such walks to the same endpoint would form a C4. For degree5 v, with r1,r3,r5 neighbours of the indicated degrees, this gives4r5+2r3<=13, hence2r5+r3<=6. Since r1+r3+r5=5, r5<=r1+1.

Sum over the h degree5 vertices. If m is their internal edge count,2m<=h+e(H,Z)<=h+z. Also m<=choose(h,2). Thus their edges to degree3 vertices are at least x=max(0,5h−2min(choose(h,2),floor((h+z)/2))−z). Necessarily x<=3l. Further, the degree3 vertices cannot supply more than choose(h,2) distinct common-neighbour pairs in H. If x=ql+r, convexity gives at least(l−r)choose(q,2)+r choose(q+1,2) such pairs. Exceeding choose(h,2) is impossible.

The exact small integer census excludes (a,z)=(8,8),(9,4),(9,5),(9,6). Therefore all surviving a=8 classes require z<=7 and all a=9 classes require z<=3. These are universal restrictions on all incidence assignments, not fixed-witness failures, but no whole empty-graph class is excluded. No search, timeout or capped retry is involved. Initial exploration of a=10 was dropped because the earlier surviving inventory already has no such classes. Independent review pending.
