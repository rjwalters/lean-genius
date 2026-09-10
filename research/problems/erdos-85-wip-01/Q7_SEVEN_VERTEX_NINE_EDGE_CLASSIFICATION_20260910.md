# The seven-vertex nine-edge equality case — 2026-09-10

Owner: codex-sol-2. Independent review #1638: PASS (codex-sol-1).

Up to relabeling, exactly two simple C4-free graphs on seven vertices have
maximum degree at most three and nine edges. Both have degree sequence
(2,2,2,3,3,3,3). One has one triangle; the other has two.

This is an exact finite classification of the induced small graph only.
It is not a Lean theorem, a full H7 graph enumeration, or a sector exclusion.
The generic upper bound of nine edges is separately proved in
`proofs/Proofs/Erdos85SevenVertexSubcubicBound.lean`.

## Representatives and exact finite verification

Vertices are0 through6. The representatives have edges:

    A: 01,02,03,12,14,25,36,46,56
    B: 01,02,03,12,14,35,36,45,56.

A is a triangle with three subdivided spokes to a fourth central vertex.
B has triangles012 and356, joined by edge03 and path1-4-5.

The verifier enumerates all choose(21,9)=293930 nine-edge subsets. It rejects
maximum degree above three and detects C4 by two vertices having at least
two common neighbors. Exactly3360 labeled graphs remain. Separately it
constructs the two complete permutation orbits using all7! relabelings.
Their sizes are840 and2520, they are disjoint, and every accepted graph
belongs to their union. The union and accepted set have equal cardinality.
Thus the classification does not depend on an isomorphism library or a
numerical solver. The two triangle counts also distinguish the two orbits.

Run `python3 verify_q7_seven_vertex_nine_edge_classification.py`. It uses
only the standard library and regenerates the adjacent JSON summary.

## Structural explanation of the degree and triangle counts

The degree deficit from seven cubic vertices is21-18=3. A degree-zero
vertex would leave six cubic vertices; any of their roots would have only
cubic neighbors, contradicting the seven-vertex root lemma in the Lean file.
If a vertex has degree one, the remaining deficit forces one degree-two
vertex and five cubic vertices. The two noncubic vertices together have
only three incident edges. Some cubic vertex is adjacent to neither, again
contradicting that root lemma. Thus every degree is two or three, giving
exactly four cubic and three degree-two vertices.

There is a triangle. Otherwise a cubic vertex with a cubic neighbor has
three neighbors whose other incidences total at least four. Triangle- and
C4-freeness make their outside endpoints distinct, requiring at least eight
vertices. Hence the four cubic vertices would be independent, forcing all
twelve of their incidences onto the three degree-two vertices, whose total
capacity is six. This is impossible.

Two triangles cannot share an edge, since their union would contain a C4.
They cannot share just a vertex, since that vertex would have degree at
least four. Thus triangles are disjoint and there are at most two on seven
vertices. These arguments explain the degree and triangle facts; the
explicit finite orbit check supplies the complete two-shape classification.

## Consequence for the H7/T0 endpoint

In the H7/T0 support ledger, a=9 means C[L0] satisfies this classification.
Every empty-support vertex therefore has two or three empty-support
neighbors, with exactly three vertices of degree two and four of degree
three. Using n2=n0 and n1=7-2n0, their full low support-neighbor counts are

    three vertices: (n0,n1,n2)=(2,3,2),
    four vertices:  (n0,n1,n2)=(3,1,3).

This reduces that endpoint to two possible induced-empty configurations.
It does not show that either extends to a full graph, and it imposes no new
restriction on the other values a=6,7,8. No fixed residual polynomial is
assumed by this classification.
