# Universal H7 nine-edge triangle cover — 2026-09-10

Owner: codex-sol-3. Independently reviewed PASS1648.

At the H7/T0 nine-edge endpoint, empty shape A forces at least four
all-low triangles. If no two empties share an outside neighbor, it forces
at least five. These bounds use no residual polynomial. Shape B retains
the prior possibility of three all-low triangles, with a restriction on
which outside-common-neighbor pairs are present.

This is a paper graph argument with an exact finite arithmetic verifier,
not a newly supplied Lean theorem or a full-profile exclusion. Use the
two labeled shapes from
[the seven-vertex classification](Q7_SEVEN_VERTEX_NINE_EDGE_CLASSIFICATION_20260910.md)
and the pair graph X defined in
[the empty compression note](Q7_H7_EMPTY_COMPRESSION_CUTS_20260910.md).
Only the universal graph-to-X identification is needed from the latter;
none of its spectrum assumptions or positivity tests is used here.

## A general coverage inequality

Let E be the seven empty-support vertices, A=C[E], and T the number of
all-low triangles in the full graph. Every empty vertex belongs to at
least one all-low triangle, by the established actual-graph empty-support
positivity lemma.

All low triangles containing at least two empty vertices are known from
A and X:

1. Triangles wholly in E are exactly the triangles of A.
2. A triangle with exactly two empty vertices must use a singleton-support
   third vertex, since pair-support vertices have at most one empty
   neighbor. Its empty edge lies in both A and X. Conversely each edge of
   A intersect X gives one such triangle. Its outside common neighbor is
   unique by C4-freeness.

Write tA for the number of triangles of A, F=E(A) intersect E(X), and k=|F|.
Let W be the empty vertices covered by the triangles of A or by endpoints
of edges of F. These tA+k known triangles are distinct. Every other low
triangle contains at most one empty vertex. Thus each vertex of E minus W
requires a different additional triangle, giving

    T >= tA + k + 7 - |W|.

This remains a necessary inequality even if some patterns X cannot be
realized. It uses a union for W, so overlapping known triangles are not
mistakenly counted as covering distinct vertices.

## Shape A

Its unique internal triangle is012. The other four vertices3,4,5,6
induce the claw with center6 and leaves3,4,5. All six allowed X pairs are
edges of A:

    03,14,25,36,46,56.

The coverage expression is at least4 for every subset of those pairs.
There is also a direct proof: if T<=3, besides012 there could be at most
two triangles to cover the four other empties. Each could contain at most
two of them, since A has no second triangle. Covering all four would
require two disjoint edges in the claw, which is impossible. Hence T>=4.

For X empty, the only known triangle is012 and four empties remain
uncovered. Every other triangle has at most one empty vertex, so T>=5.
For the partial X=0 incidence controls, this explains why checking high
degrees, empty degrees and high-neighborhood matchings alone does not
yet establish the required empty-triangle property.

## Shape B

Its internal triangles are012 and356, leaving only empty vertex4
uncovered. Its six allowed X pairs are

    03,14,16,25,26,45,

of which03,14,45 are edges of A. Consequently

    T >= 2 + |F| + indicator(neither14 nor45 lies in F).

If T=3, necessarily

    F is empty, or F={14}, or F={45}.

In particular a selected pair03 already forces T>=4, since it adds a
known triangle without covering vertex4. Two or more edges of F also
force T>=4. Pairs16,25,26 do not themselves form triangles with their
outside singleton, because their empty endpoints are nonadjacent.

These restrictions do not assert that any T=3 configuration extends to
a graph. They leave the other empty-edge values a=6,7,8 unaddressed.

## Exact check

The standard-library verifier checks each representative, recovers its
triangles and six allowed pairs, and evaluates the coverage union on all
64 subsets. It proves the stated finite inequalities and the exact list
of F sets attaining the scalar lower bound3 in shape B. This is not a
graph enumeration or a spectrum test.

Run `python3 verify_q7_h7_empty_triangle_cover.py`.

The generic graph-counting steps are separately available in
`Erdos85IndependentTriangleCover.lean`: independent covered vertices give
distinct additional triangles, and general covered vertices require at
least one additional triangle per three vertices. Its four-triangle
corollary applies to the three independent claw leaves and the disjoint
known triangle. The source and public build pass with standard axioms;
independent review1651 passed. An actual H7 shape-map bridge is not
claimed by that generic file.

`Erdos85OrderFortyNineEmptyTriangleCover.lean` now connects those counting
lemmas to actual order49 graphs. It constructs an induced-low three-clique
through each empty-support vertex using the preexisting all-low triangle
theorem, then supplies both counting bounds without an extra triangle-cover
premise. Source and public build pass with standard axioms; review1653
passed. Constructing the shape-specific independent set and known triangle
family remains a separate step.

## Actual unique-triangle endpoint in Lean

`Erdos85OrderFortyNineSevenHighT0UniqueTriangleBound.lean` proves
`sevenHigh_t0_unique_empty_triangle_four_low_triangles`: an actual order49
C4-free minimum-degree7 graph with seven high vertices, zero triple-support
vertices, nine empty edges, and exactly one induced-empty triangle has at
least four all-low triangles. The empty census and degree bound instantiate
the generic unique-triangle structure theorem (review1655 PASS). Its three
degree2 vertices and known triangle are explicitly embedded into the low
graph, where actual empty coverage supplies the count. No shape isomorphism
or additional covering hypothesis remains. Source and public build pass with
standard axioms; review1657 passed. The result
does not exclude all H7 graphs or address the two-triangle endpoint.
