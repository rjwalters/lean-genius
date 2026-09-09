# Round114 S1: Baer-deletion seed and a quadratic repair barrier

The proposed odd-degree construction has a valid cofinal seed, but a repair
containing a perfect matching of its deficient vertices must delete
quadratically many old edges. In particular, adding that matching with
only O(q) old-edge deletions cannot work. This does not rule out larger
trades, repairs routing all deficiencies through other vertices, or the
odd-degree construction route itself.

## Exact seed for every odd square q

Let r be an odd prime power, q=r^2, and use a nondegenerate orthogonal
polarity of PG(2,q) defined over F_r. Let G be its loopless polarity graph
and let S=PG(2,r). Delete S to obtain H.

Every exterior point has exactly one neighbor in S. Indeed, orthogonality
to its coordinate vector gives a rank-two F_r-linear map F_r^3 -> F_q:
rank one would mean all coordinates are multiples of a common F_q scalar
with coefficients in F_r, contrary to being exterior. The kernel is a
one-dimensional F_r subspace, hence gives exactly one projective point.

The original graph has degree q on its q+1 absolute points and degree q+1
elsewhere. The subplane has r+1 absolute points. Consequently H has

    N=q^2-r vertices;
    T=q-r exterior absolute points of degree q-1;
    all other vertices of degree q.

N is even and N<=q^2-3 for r>=3. Thus a uniform C4-free repair attaining
minimum degree q on these same vertices would directly supply the odd-degree
drop construction for Erdős85. The seed alone does not do so.

The size and edge count agree with the known subplane-deletion construction
described by [Abreu, Balbuena and Labbate](https://iris.unibas.it/handle/11563/9234):

    |E(H)| = (qN-(q-r))/2
           = q(q^2-1)/2 - r(q-1)/2.

No claim is made that their existing graph already has minimum degree q.
The degree census above is derived here, not inferred from average degree.

## Length-three paths force old-edge deletions

For distinct absolute points a,b in the full graph, there are exactly q-1
length-three paths. One way to count is to restore absolute loops, giving
a symmetric matrix B with B^2=qI+J and row sum q+1. Since B_ab=0,
(B^3)_ab=q+1. Removing the loop at each endpoint removes one walk. The
unique common neighbor of a,b is not absolute, so there is no internal-loop
walk to remove. All remaining walks are simple paths, since a,b are not
adjacent. This leaves q-1 paths.

In any C4-free simple graph, distinct length-three paths between fixed
nonadjacent endpoints are edge-disjoint. Sharing a first or last edge gives
two common neighbors for another pair. Sharing a middle edge in opposite
orientations makes its endpoints two common neighbors of the original
endpoints. Either creates a C4; other kinds of edge sharing would repeat
an endpoint or require the missing endpoint edge.

Deleting S can destroy at most two of these paths: each endpoint has exactly
one neighbor in S, and edge-disjointness allows only one path through each
of those two incident edges. Thus, for all distinct a,b in T,

    number of length-three paths in H from a to b >= q-3.

Adding ab while retaining C4-freeness must delete an old edge of every such
path. Additional new edges cannot remove the cycles formed by old paths.
In particular any one newly added edge inside T already requires at least
q-3 old-edge deletions.

## A perfect matching requires Omega(q^2) deletions

Let P be any perfect matching of T. Suppose H' is a C4-free graph on the
same vertices with P subset E(H'), allowing any other additions or deletions.
Let F=E(H) minus E(H'). Then

    |F| >= (q-r)(q-3)/4.                         (1)

Proof: the selected endpoint pairs have at least |P|(q-3) old paths in
total. Every vertex has at most two neighbors in T, since its polar line
meets the nonsingular absolute conic in at most two points. T is independent.
An old edge incident with T can occur only as the first/last edge of paths
for the unique matching pair containing that endpoint, and occurs in at
most one such path by edge-disjointness. An old edge with neither endpoint
in T can occur only as a middle edge; its two endpoints have at most two
T-neighbors each, and the matching pairs their neighbors disjointly. It
therefore belongs to at most two selected paths. Each deletion hits at most
two paths, proving (1).

For the natural Frobenius-conjugate matching a -> a^r, the stronger bound is

    |F| >= (q-r)(q-1)/4.                         (2)

Here each pair has the same unique subplane neighbor: the intersection of
the two conjugate tangent lines is defined over F_r. No length-three path
through that neighbor exists in the loopless graph, because its unique
common neighbor with either absolute endpoint is that endpoint itself.
Thus all q-1 original paths survive subplane deletion. The same load-two
count proves (2).

## Deterministic q25 check

`check.py` constructs PG(2,25) over F5[u]/(u^2-2), deletes its canonical
PG(2,5), and checks the actual adjacency sets, C4-freeness, degree census,
path edge-disjointness, and conjugate-matching deletion loads.

Results: 620 vertices; degree24 at20 vertices and degree25 at600 vertices.
Among the190 deficient-vertex pairs, the length-three path counts are
22 for120 pairs,23 for60,24 for10. The10 conjugate pairs have240 paths
in total, and an old edge hits at most2 of them. Hence (1) gives110 required
deletions and (2) gives120. No repaired graph was constructed and no graph
search was run. The uniform statements follow from the proof, not the
single finite example.

This closes the matching-plus-O(q)-deletions version of S1. It does not
close all field-defined repairs: any next proposal must name a genuinely
larger trade or a different pattern of new edges and show how it meets the
degree and C4 constraints simultaneously.
