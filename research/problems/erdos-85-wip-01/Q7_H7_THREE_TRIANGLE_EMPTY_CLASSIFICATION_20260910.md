# H7 with three all-low triangles: induced-empty classification

This is a universal necessary condition, with no residual spectrum premise.
It applies to an actual C4-free order49 graph of minimum degree7 in the H7/T0
support census. The empty-support fiber E has seven vertices, its induced
graph has maximum degree3, and its edge count a lies in6..9. Those premises
are proved in `Erdos85OrderFortyNineSevenHighT0EmptyEdgeNine.lean`.
Every empty vertex belongs to an all-low triangle, as connected to the
induced low graph by `Erdos85OrderFortyNineEmptyTriangleCover.lean`.

## Why a clique partition is necessary

Assign each empty vertex to one all-low triangle containing it. The fibers
of this assignment partition E into nonempty cliques of the induced empty
graph, with at most T parts, where T is the total number of all-low triangles.
Consequently T is at least the minimum clique-partition number of G[E].
This does not assume that the original all-low triangles are disjoint.

For a seven-vertex subcubic C4-free graph, distinct triangles are disjoint:
sharing an edge creates a C4, while sharing exactly one vertex requires
degree4. A four-clique also contains a C4. Thus a partition into at most
three cliques exists exactly when either:

- the graph has two triangles (use both and the remaining singleton); or
- it has one triangle and its four-vertex complement has a perfect matching
  (use the triangle and the two matching edges).

To see necessity in the one-triangle case, three cliques must cover seven
vertices. At least one must have size3; the other two must each have size2.
If there is no triangle, three cliques cover at most six vertices. This is
an equivalence for the induced clique partition, not a sufficiency claim
for extending to an actual order49 graph.

## Exhaustive finite result

All edge subsets of K7 with a=6,7,8,9 are checked. A graph is retained in
the induced domain precisely when every degree is at most3 and each pair
of vertices has at most one common neighbor. The latter is exactly C4
freeness, including non-induced cycles. Full S7 orbits partition the domain.

| a | Labeled graphs | Isomorphism classes | Classes permitting T=3 | Labeled graphs permitting T=3 |
|---|---:|---:|---:|---:|
|6|31332|19|3|1750|
|7|32910|15|5|8610|
|8|17010|7|4|10710|
|9|3360|2|1|2520|

Hence the three-triangle endpoint retains13 of43 induced classes; the
other30 require T>=4. One a=6 class has clique-partition number5 and thus
requires T>=5; the remaining29 excluded classes have number4. At a=9 the
unique-triangle class is excluded, agreeing with the direct actual Lean
proof `sevenHigh_t0_unique_empty_triangle_four_low_triangles` (review1657).

The JSON records each canonical minimum bitmask representative, its edge
list, internal triangle masks, full orbit size, and exact clique-partition
number. Edge bits follow lexicographic pairs of labels0..6; triangle bits
follow vertex labels. Relabelings are exhausted, not guessed from degree
sequences or invariants.

## Verification and scope

Run `python3 verify_q7_h7_three_triangle_empty_classification.py`.
The standard-library verifier regenerates all four labeled domains and
full orbits, computes minimum clique partitions by exact subset recursion,
and independently tests three-colorings of the complement over all3^7
assignments. It also checks the triangle/perfect-matching characterization
and exact agreement with the retained JSON. There are no solver calls,
random choices, time limits, or partial order49 completions.

The finite classifier and paper implication are not a Lean certificate of
the43-class enumeration. Thirteen classes remain at T=3, and no whole H7
sector, actual graph, or fixed residual polynomial is excluded. In
particular the previously retained psi7 has T=13, so these endpoint cuts
do not exclude it.
