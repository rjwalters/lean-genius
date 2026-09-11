# Eight fixed vertices at order 80: a matching normal form

Assume a simple C4-free graph G on 80 vertices has minimum degree nine and a nonidentity involution with exactly eight fixed vertices. Accepted review 2220 gives nine-regularity, odd fixed degrees, disjoint attached sets B_v of size 9-r_v, and an unattached residual set R. If H is the fixed graph and S its degree sum, then |R|=S and

    r_v(9-r_v) <= S,     sum_v r_v(r_v-1) <= 56.

We prove H is a perfect matching, then derive necessary matching structure. No existence or full F8 exclusion is asserted.

## 1. The fixed graph is either a perfect matching or a star

The elementary degree constraints have eleven multiset solutions, recorded in results.json. They can also be described without enumeration. A degree-seven vertex cannot coexist with degree five, and permits at most two degree-three vertices by the cherry bound; capacity permits either zero or two. If there is no degree seven, at most two degree-five vertices occur. Two require exactly two degree-three vertices (capacity gives at least two, cherry at most two); one requires four, five, or six degree-three vertices. With neither, there are either zero or five through eight degree-three vertices. These are precisely the eleven profiles.

A degree-seven vertex is adjacent to every other fixed vertex. Its neighborhood induces at most a matching, by C4-freeness. Every other fixed degree is consequently at most two, and odd, hence one. Thus H is K1,7.

Suppose there are two degree-five vertices, two degree-three vertices, and four leaves. Each degree-five vertex must have at least three leaf neighbors. If the two high vertices are not adjacent, it must choose five neighbors among the two degree-three vertices and four leaves. If they are adjacent, having at most two leaf neighbors gives at least eight nonreturning two-step walks (four through the other high vertex and four through two degree-three neighbors), exceeding the seven possible endpoints. The two high vertices would therefore require at least six leaf incidences, but only four leaves exist. This is impossible.

For one degree-five vertex v, all others have degree one or three. If at most two leaves occur, the degree-five exclusion in the following local count applies: v needs at least two leaf neighbors, otherwise it has at least eight nonreturning two-step walks. With exactly two leaf neighbors it has six walks, but at most two endpoints outside its closed neighborhood and two inside its neighborhood, because its three nonleaf neighbors induce at most one edge. This is impossible. This also rules out the one-leaf profile.

In the remaining degree-five profile there are three leaves and four degree-three vertices. If v has at most one leaf neighbor it again has at least eight walks. If it has two, the same six-versus-four argument applies. If it has all three, its other two neighbors have degree three, and the two vertices outside its closed neighborhood also have degree three. Each outside vertex has at most one neighbor in N(v), and at most one outside neighbor other than itself. It is not adjacent to v, so its degree is at most two, a contradiction.

It remains to consider subcubic profiles. A degree-three vertex with no leaf neighbor has six nonreturning two-step walks but only four endpoints outside its closed neighborhood, so it lies in a triangle. Distinct triangles in a subcubic C4-free graph are vertex-disjoint: sharing one vertex requires degree four and sharing an edge creates C4.

Eight degree-three vertices would be partitioned into triangles, impossible. Six degree-three vertices and two leaves force two triangles, since at least four degree-three vertices have no leaf neighbor. These triangles have six external stubs, at most two consumed by leaves. At least two edges therefore join the triangles, forming a matching and hence a C4 with their internal edges. Seven degree-three vertices and one leaf force two triangles plus a degree-three vertex v attached to the leaf. The two remaining neighbors of v must lie one in each triangle (two in one triangle would create C4). The two leftover stubs in each triangle then join across, again making C4.

For five degree-three vertices and three leaves, at least two degree-three vertices have no leaf neighbor. Thus one triangle exists; a second cannot, so the other two degree-three vertices u,v lie outside it and each has a leaf neighbor. Each can have at most one neighbor in the triangle. If u,v are nonadjacent, each needs two leaf neighbors, requiring four leaves. If they are adjacent, let t be the number of edges from {u,v} to the triangle. Then u,v need 4-t leaf incidences, while the triangle needs 3-t. Thus 7-2t<=3, forcing t>=2; each can meet the triangle at most once, so both do. They meet different triangle vertices because each triangle vertex has only one external stub. The edge uv and the edge between their triangle neighbors form a C4. Thus this profile is impossible.

If no degree-three vertex occurs, every fixed degree is one and H is four disjoint edges. This completes the classification.

## 2. Excluding the star

Suppose H=K1,7 with center c. Its attached set B_c has two vertices b,b', while each of the seven leaf attached sets has eight vertices. Here S=14 and |R|=14. There are no edges from B_c to any leaf attached set because their fixed centers are adjacent.

Each of b,b' has eight moved neighbors and at most one in B_c, hence at least seven in R. Each residual vertex meets B_c at most once. Equality is forced: b,b' are adjacent and their R-neighbor sets partition R into two sets of seven.

An edge between these two residual sets would form a C4 through b,b'. Inside either set, every vertex has at most one residual neighbor because the set lies in a neighborhood. On the other hand, every residual vertex has at most one neighbor in each of the eight attached sets and no fixed neighbor. Nine-regularity forces its residual degree to be at least one. Thus both seven-vertex sets must be one-regular, impossible by parity. The star is excluded.

## 3. Saturated matching structure

Therefore H=4K2. Each attached set B_v has eight vertices, and |R|=8. For x in B_v, there is at most one neighbor inside B_v, no neighbor in the attached set of v's fixed partner, and at most one in each of the six other attached sets. Its eight moved neighbors therefore require at least one in R. The eight vertices of B_v and the at-most-one incidence from each residual vertex force equality everywhere.

Consequently:

* each B_v induces a perfect matching;
* between B_v and the attached set of its fixed partner there are no edges;
* between any other two attached sets there is a perfect matching;
* between every B_v and R there is a perfect matching;
* R induces a perfect matching, since every residual vertex has exactly eight attached neighbors and total degree nine.

## 4. Two isolated components in the zero-codegree graph

Let M be the adjacency matrix of G and E=8I+J-M². This is a simple seven-regular graph joining distinct vertices with no common G-neighbor, and ME=EM.

Any two distinct fixed vertices have no common G-neighbor: H is a matching and a moved vertex has at most one fixed neighbor. Thus E on the fixed set is K8. Its vertices already have all seven E-neighbors there, so there are no E-edges to moved vertices.

Any two distinct residual vertices also have no common G-neighbor: R is a matching, each attached vertex has exactly one R-neighbor, and fixed vertices have no R-neighbor. Hence E on R is another K8 component, with no E-edges outside it.

Within any B_v, E has no edges, since every pair shares fixed neighbor v in G. For x in B_w, commutation at (x,v), where v is fixed, gives

    |N_E(x) intersect B_v| = 1 if v != w, and 0 if v=w.

Indeed (ME)_(x,v) counts x's unique fixed G-neighbor w in the fixed K8, and (EM)_(x,v) counts E-neighbors of x among the G-neighbors B_v of v; the fixed partner contributes zero. Therefore E between every two distinct attached sets is a perfect matching. No assertion about the number of components of E on the 64 attached vertices is made.

Equivalently those 64 vertices form a grid indexed by fixed and residual vertices: each pair (v,r) labels the unique vertex of B_v adjacent to r. The matching normal form is necessary only and still leaves phase/edge choices and the C4 constraints to be solved.

## Finite verification and scope

check.py checks all 165 odd-degree multisets and all labelled simple graphs for each of the eleven retained degree sequences. All searches completed in about 0.105 seconds under the original aggregate 60-second and one-million-node-per-profile caps, with no UNKNOWN. They return exactly 105 perfect matchings for the all-degree-one sequence and one star for the degree-seven sequence, and no others. This is a finite check of H on eight vertices only. The star exclusion and matching/deficiency deductions are paper arguments; no full graph solver was used. This does not exclude the remaining N80/F8 case or solve Erdős 85.
