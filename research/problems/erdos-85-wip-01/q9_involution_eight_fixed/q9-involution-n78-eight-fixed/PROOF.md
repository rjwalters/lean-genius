# Excluding eight involution-fixed vertices at N=78

Assume a simple C4-free graph G on 78 vertices has minimum degree nine and a nonidentity involution fixing exactly eight vertices. Use the accepted involution boundary and attached-set capacity argument of review 2220. G is nine-regular. Its fixed graph H has eight vertices and odd degrees r in {1,3,5,7}. Write S for the sum of fixed degrees and R for the number of unattached moved vertices. Then R=78-10*8+S=S-2. The accepted capacity inequality specializes to

    r(9-r) <= S-2

for every fixed degree r. C4-freeness inside H also gives the cherry bound

    sum_v r_v(r_v-1) <= 8*7 = 56.

The complete list of multisets satisfying these elementary constraints is:

* six degree-three vertices and two leaves;
* seven degree-three vertices and one leaf;
* eight degree-three vertices;
* one degree-five vertex, five degree-three vertices, and two leaves;
* one degree-five vertex, six degree-three vertices, and one leaf.

For completeness, degree seven contributes 42 to the cherry sum. It cannot coexist with degree five, and it permits at most two degree-three vertices. With no degree-three vertex, S=14 and its capacity 14 exceeds S-2=12. With one or two degree-three vertices, S<=18 and the degree-three capacity 18 exceeds S-2. Thus degree seven is impossible. At most two degree-five vertices satisfy the cherry bound, but two would permit at most two degree-three vertices, giving S<=20, below the degree-five requirement S>=22. With one degree-five vertex, the same capacity requires at least five degree-three vertices; the cherry bound permits at most six. With no degree-five vertex, the all-leaf case fails capacity, and the degree-three capacity requires at least six degree-three vertices. This proves the list without relying on enumeration.

## The two degree-five profiles are impossible

Let v have degree five. Every other degree is one or three. All nonreturning length-two walks from v have distinct endpoints other than v, so there are at most seven of them. If v has at most one leaf neighbor, its other four or more neighbors have degree three, giving at least eight such walks. Therefore both available leaves must be neighbors of v; this already excludes the one-leaf profile.

In the two-leaf profile, the other three neighbors of v have degree three, giving six nonreturning two-step walks. There are only two vertices outside the closed neighborhood of v, accounting for at most two endpoints. Inside its neighborhood, leaves support no internal edges, and the three remaining vertices induce at most a matching: any two incident edges inside a neighborhood would create a C4 with v. At most one internal edge therefore supplies two more endpoints. There are at most four walks in total, contradicting six.

## A local triangle rule for the three subcubic profiles

In a C4-free graph on eight vertices, a degree-three vertex whose neighbors all have degree three lies in a triangle. Indeed it has six nonreturning two-step walks. Only four vertices lie outside its closed neighborhood. Its neighborhood induces at most a matching, so the remaining two endpoints require an internal neighborhood edge, yielding a triangle.

In a subcubic C4-free graph, distinct triangles are vertex-disjoint. Sharing just one vertex would require degree at least four; sharing an edge would create a four-cycle. Consequently every degree-three vertex with no leaf neighbor belongs to exactly one of these disjoint triangles.

If all eight vertices have degree three, the triangles would partition eight vertices, impossible.

If six vertices have degree three and two are leaves, at least four of the six degree-three vertices have no leaf neighbor. Thus there must be at least two disjoint triangles. These exhaust the six degree-three vertices. Every triangle vertex has exactly one remaining external edge. The leaves consume at most two of these six stubs, so at least four stubs form at least two edges between the triangles. These edges form a matching, and any two of them together with the corresponding edge within each triangle form a C4. This is impossible. This argument also covers adjacent leaves: then none of the six stubs is consumed by a leaf.

If seven vertices have degree three and one is a leaf, at least six degree-three vertices have no leaf neighbor. They therefore form exactly two disjoint triangles. Let v be the remaining degree-three vertex. Since v is outside the triangles, the local rule forces it to be the unique neighbor of the leaf. Its two other edges join the triangles. They cannot both join one triangle: v and two triangle vertices would have a C4 through the third triangle vertex. Thus v joins one vertex in each triangle. Each triangle now has exactly two remaining external stubs, and they must join the other triangle. These two matching edges again form a C4 with internal triangle edges.

All five profiles are impossible. Therefore an involution of a hypothetical N78 graph cannot fix exactly eight vertices. Combined with accepted 2220, the remaining fixed counts are 0,2,4,6,10; if the separate ten-fixed-vertex exclusion is accepted, they reduce to 0,2,4,6. No N80 case, smaller fixed-count case, or full N78 graph is excluded here, and Erdős 85 remains unresolved.

## Independent finite-check target and scope

check.py separately enumerates all 165 odd degree multisets on eight vertices, retaining exactly the five profiles above. It then enumerates simple graphs of each fixed labelled degree sequence by assigning all future neighbors of successive vertices, rejecting any partial C4 or impossible remaining degree. Sorting the degree sequence loses no graph up to relabelling. All five searches completed under the original aggregate 60-second and one-million-node-per-profile caps, in about 0.102 seconds, with zero C4-free realizations and no UNKNOWN. The node counts are 1078,173,3210,229,7424 in the recorded profile order. This is an eight-vertex fixed-subgraph check only; no full graph solver, new positive control, or extension of an earlier capped search was used. The paper argument above does not depend on the DFS result.
