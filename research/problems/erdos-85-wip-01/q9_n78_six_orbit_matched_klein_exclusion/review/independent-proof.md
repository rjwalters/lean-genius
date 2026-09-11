# Excluding six orbits of sizes6,12,12,12,12,24

Let G be simple, C4-free and nine-regular on78 vertices with exactly six automorphism orbits of sizes6,12,12,12,12,24. Accepted2349 gives |A|=24 and leaves48 necessary quotient matrices. Write F for the six-vertex orbit. Every retained matrix has the following properties, verified in quotient-cover.json:

* F induces a matching of three edges.
* Two12-orbits B,C each supply two neighbors to every F vertex, and each B/C vertex has exactly one F neighbor.
* The regular24-orbit U supplies four neighbors to every F vertex, and each U vertex has exactly one F neighbor.
* The other two12-orbits have no F neighbors.

Fix a matching edge ff' in F. Its endpoints have the same stabilizer H=A_f=A_f', because the matching is A-invariant and each center has a unique matching partner. Accepted2349 makes H a Klein-four group; in particular it has exactly three nonidentity elements, all involutions.

At f, the two sets B_f=N(f) intersect B and C_f=N(f) intersect C each have two vertices and are transitive H-sets. To see transitivity, use transitivity of A on B or C to map any one vertex of the fiber to another. Since the attached vertex has a unique F neighbor, the mapping element must fix f and lie in H. Thus the action on each pair is a surjection H to S2, with kernel of order two.

The two kernels at f are distinct. Otherwise their common nonidentity involution would fix all four vertices of B_f union C_f, as well as the fixed neighbor f'. This contradicts accepted2257: an involution fixing a vertex has only one or three fixed neighbors. Therefore two distinct involutions of H each fix two attached neighbors of f. The third involution swaps both pairs. No nonidentity element fixes a vertex in the four-element U fiber, since U is a regular A-orbit.

The identical argument at f' gives another two-element subset of the three involutions of the same H, each member fixing two attached neighbors of f'. Any two two-element subsets of a three-element set intersect. Choose an involution t in their intersection. It fixes f and f', two attached neighbors at f and two at f'. Those four attached vertices are distinct because every attached vertex has a unique F neighbor.

Thus t fixes at least six vertices. The bound2257 says at most six, so these are exactly its fixed vertices. Both f and f' have degree three in the induced fixed graph. Yet the matching edge ff' has no common G-neighbor: within F there is only the matching, every attached vertex has at most one F neighbor, and the remaining vertices have none.

Accepted2257 classifies a six-vertex involution fixed graph as either3K2 or a triangle with one pendant leaf at each triangle vertex. The former has no cubic vertices. In the latter, an edge joining two cubic vertices is a triangle edge and has a common neighbor. Neither permits the adjacent cubic fixed centers f,f' with no common neighbor. This contradiction excludes every retained quotient.

Consequently the six-orbit pattern6,12,12,12,12,24 is impossible. This proof is independent of the separate three-six-orbit exclusion and of the at-least-six-orbits assembly. It uses no graph search, no unproved universal regularity statement for order-eight stabilizers, and no Lean formalization. Larger orbit counts and Erdős85 globally remain outside the result.
