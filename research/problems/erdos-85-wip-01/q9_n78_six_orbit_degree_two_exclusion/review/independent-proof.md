# Excluding six orbits of sizes6,6,6,12,24,24

Assume G is simple, C4-free and nine-regular on78 vertices, with exactly six automorphism orbits of sizes6,6,6,12,24,24. Accepted2349 gives |A|=24 for A=Aut(G), and accepted2346 supplies all24 possible degree quotients in this case.

Every one of the24 quotient matrices has two distinct six-vertex orbits X,Y such that G[X] has degree two and the X--Y edges have reciprocal degree one. The latter edges give an A-equivariant bijection between X and Y. The accompanying deterministic check identifies such a pair in every matrix; it enumerates no new graph domain.

Let K be the kernel of the action on X. Equivariance of the bijection means K also fixes Y pointwise. Moreover K lies in the stabilizer of a vertex of X, which has order24/6=4. Thus K is a2-group. If nontrivial it contains an involution, fixing all twelve vertices of X union Y, contradicting the accepted2257 bound of at most six fixed vertices. Hence K is trivial: A acts faithfully and transitively on G[X].

A simple two-regular graph on six vertices is either a six-cycle or two disjoint triangles. The six-cycle has automorphism group of order twelve: the image of one vertex has six possibilities and the image of one of its two neighbors has two possibilities, after which every vertex is forced. A group of order24 cannot embed in this group.

Suppose instead G[X] is two disjoint triangles. Because A is transitive on all six vertices, it exchanges the two triangles. Let J be the kernel of its action on the two components. Then J has index two in A and order twelve. It embeds into S3 times S3 by restriction to the two triangles, since the action on all of X is faithful.

Each projection of J acts transitively on its triangle: any element of A taking one vertex to another in the same triangle must preserve that component and hence both components, so lies in J. A transitive subgroup of S3 has order three or six. A projection of order three would have a kernel of order four, but that kernel injects into the other S3 factor, impossible by Lagrange's theorem. Therefore both projections are surjective onto S3.

The kernel N of the first projection now has order12/6=2. Under the second projection it injects as an order-two subgroup of S3. Since N is normal in J and the second projection is surjective, its image is normal in S3. But S3 has no normal subgroup of order two: its three transpositions are conjugate. This is a contradiction.

Neither two-regular six-vertex graph admits the required faithful transitive order24 action. Thus the orbit-size pattern6,6,6,12,24,24 is impossible. Combined with accepted2349, a six-orbit candidate can only have order24 and sizes6,12,12,12,12,24, within that packet's retained48 quotients.

This proof uses only the matched two-regular six-orbit structure, the involution fixed-point bound, and elementary permutation-group arguments. It introduces no graph search, finite-group classification, full graph solver or Lean formalization, and does not exclude the remaining pattern or Erdős85 generally.
