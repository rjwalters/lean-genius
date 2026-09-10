# H3 pair b=0: reduction to36 normalized nonempty cores

In the universal H3 pair profile, assume the three pair-support vertices are independent (b=0). Their high-colored singleton core has320 normalized possibilities; exact C4 checks retain36. These are normalized configurations, not asserted isomorphism classes. Each gives a small explicit domain for the missing empty-vertex incidences. None is claimed to extend to a full graph, and this does not exclude the pair profile or address b=1.

The argument uses the reviewed universal H3 support ledger and identities C1=7-t, Ct=3, BC=J. No triangle count or residual polynomial is fixed. The standalone standard-library verifier exhausts the finite core, with no optimizer or timeout; this is not a Lean theorem.

## Special and ordinary singletons

Index high colors by0,1,2. Let P_a be the pair vertex missing high color a. Each high vertex neighbors two P vertices and six singleton vertices of its own color. Since the P vertices are independent and have low degree5, Ct=3 and BC=J give each P_a three singleton neighbors, one of every color, and two empty neighbors.

Write x_(i,a) for the singleton of color i neighboring P_a. These nine special singletons are distinct: a vertex cannot neighbor two pair vertices because Ct=3. Three ordinary singleton vertices O_i remain in each color.

A special x_(i,a) has its support-weighted neighbor count2 supplied by P_a. It therefore has exactly one singleton neighbor, necessarily of color a by BC=J, and four empty neighbors. An ordinary singleton has no P-neighbor and has exactly one singleton neighbor of each color, hence three singleton neighbors and three empty neighbors.

If x_(i,a) neighbors another special vertex, that vertex must be x_(a,i). Thus the special-induced graph is a subset epsilon of the three possible transpose edges x_(i,a)--x_(a,i), i<a. The diagonal x_(i,i) cannot neighbor itself and must neighbor O_i. High-color permutations reduce epsilon to four possibilities, according to its edge count k=0,1,2,3.

## The nine ordinary vertices

Every special neighbor of an ordinary vertex of color i is some x_(j,i), and hence neighbors P_i. An ordinary vertex cannot have two such special neighbors, since they would make a C4 through P_i. Therefore its degree in O is2 or3.

In the six singleton vertices of color i, BC=J leaves a matching with two internal edges: exactly two special vertices have their P-neighbor containing color i, and the other four vertices require one same-color singleton neighbor. One internal edge joins x_(i,i) to an ordinary vertex; the other lies within O_i. Consequently O_i has one internal edge and one internally unmatched vertex.

Between colors i and j, the singleton graph is a matching of size4. If epsilon_ij=1, its one special-special edge leaves three ordinary-ordinary edges. If epsilon_ij=0, two special-ordinary edges leave two ordinary-ordinary edges. Thus O_i--O_j is a matching of size2+epsilon_ij.

When epsilon_ij=0, the vertex of O_i missing a neighbor in O_j must neighbor x_(j,i). The internally unmatched O_i vertex must neighbor x_(i,i). All these missing endpoints are distinct, by the preceding at-most-one-special-neighbor argument. In O_i exactly deg_epsilon(i) vertices have degree3 and the others have degree2. The total O edge count is9+k.

## Complete normalization

Label the internally unmatched O_i vertex0 and its internal edge1--2. For each absent epsilon_ij, assign the missing O_i--O_j endpoint a distinct label from1,2 in increasing order of j. This is attainable by relabeling O_i: if two endpoints are required they are distinct, if one is required the other endpoint is unrestricted, and if none are required labels1,2 are arbitrary. No actual graph is omitted.

For an absent epsilon edge, the cross matching is any bijection of the two remaining labels, giving2 choices. For a present epsilon edge it is any permutation of three labels, giving6 choices. The four k cases therefore have8,24,72,216 choices, totaling320.

Add the P--special edges, forced special--ordinary edges, epsilon edges, and all three high vertices with their prescribed eight neighbors. This known graph has24 vertices and51 edges. Test C4-freeness by requiring every pair of vertices to have at most one common neighbor. The retained counts are5,7,8,16, totaling36. Fixed degrees in the retained known graph are5 on P,3 on special singletons,4 on ordinary singletons, and8 on high vertices. The verifier checks all of these statements.

## Domain for the25 missing empty vertices

The six empty vertices neighboring P consist of two per P_a, with no overlap. Each such empty vertex needs exactly one singleton neighbor of color a, to supply the one high color absent from P_a. That singleton must have no existing common neighbor with P_a.

Exactly three color-a singletons are eligible: x_(a,a), the x_(a,b) with epsilon_ab=0, and the cubic vertices in O_a. Their number is1+(2-deg_epsilon(a))+deg_epsilon(a)=3. The two empty neighbors of P_a must choose distinct eligible singletons, or they would have both P_a and that singleton as common neighbors. The verifier independently checks the three-element host sets in every retained core.

The other19 empty vertices have no P-neighbor and need one singleton neighbor of each high color. Their candidate transversal triples contain no pair with a common neighbor in the known core. The verifier enumerates these triples; the36 cores have between57 and67 candidates. Chosen triples cannot repeat a singleton pair, which would create a C4 through two empty vertices.

Special singletons require four empty incidences and ordinary singletons three. After selecting the six P-adjacent empty vertices, subtract their six singleton incidences from those demands. The remaining total is9*4+9*3-6=57, exactly19 transversal triples. Satisfying these degree demands and pair restrictions is only a necessary next step: the edges among empty vertices still need to be constructed and checked.

No full empty-incidence assignment or full graph is claimed by this reduction. The b=1 pair branch and the global Erdős85 objective remain open.
