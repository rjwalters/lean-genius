# Even-polarity extensions cannot supply the next odd-degree short witness

2026-09-08, codex-sol-3. Uniform prose proof; not Lean-formalized.
Independent review: codex-sol-1, Squad review #1488 PASS, including an
independent repeat of the absolute-pair calibration.

Let q >= 4 be an even prime power, and let P be the simple orthogonal
polarity graph of PG(2,q). Start with either P or P minus its nucleus c.
Preserve every edge of this starting graph, retain all its vertices, and
add arbitrary vertices and edges. No resulting C4-free graph of order
N < (q+1)^2 has minimum degree q+1.

This excludes a complementary construction for the odd-degree parity-drop
route. It does not exclude deleting other old vertices or edges, or using
another host. In particular it is not an arbitrary-graph exclusion.

## Host facts and forbidden added old edges

Write L for the q+1 absolute points. They are independent. Each has degree
q; every nonabsolute point has degree q+1. The nucleus has neighborhood L,
and every other nonabsolute point has exactly one neighbor in L. These are
the same projective incidence facts used in
`BINARY_POST_SQUARE_INTERVAL_CONSTRUCTION.md`.

For any distinct x,y in L there are exactly q-1 simple three-edge paths
from x to y avoiding c. To see this, choose u in N_P(x) minus {c}, giving
q-1 choices. The polar lines of u and y meet in a unique point v. This
point is not c, since u is nonabsolute; it is not absolute, since u's
unique absolute neighbor is x and x is not adjacent to y. Also u is not
adjacent to y, so v is distinct from u and y; v is distinct from x because
x and y are not adjacent. Thus x,u,v,y is a simple path avoiding c.
Conversely, every such path starts with one of these u and has this forced
v. Adding xy therefore creates a C4 in either starting graph.

Put d=q+1. A C4-free graph of minimum degree d on fewer than d^2 vertices
is d-regular: if a vertex has d+1 neighbors, their pairwise disjoint
neighbor sets with that vertex removed already contain (d+1)(d-1)
vertices, forcing order at least d^2. The existing Lean theorem is
`degree_eq_of_minDegree_card_lt_nextMooreLayer` in
`Erdos85DistanceLayers.lean`.

Consequently a putative extension here is d-regular. Every surviving
nonabsolute vertex already has degree d, so it receives no new edge.
The only possible added old-old edges join two absolute points, and the
preceding path argument forbids all of them.

## Keeping the nucleus

If r vertices are added to P, the order bound gives r <= q-1. The old
absolute vertices require new edges, so r > 0. A new vertex can have at
most one absolute neighbor: two would give a C4 through c. All its other
neighbors must be new vertices, so its degree is at most 1+(r-1)=r<d.
This contradicts regularity.

## Removing the nucleus

If r vertices are added to P-c, the order bound gives r <= q. Every old
absolute vertex now has degree q-1 and must have exactly two new neighbors.
No two absolute vertices can have the same unordered pair of new
neighbors, since that would give a C4. Hence

    binom(r,2) >= q+1.

For q >= 4 this forces r >= 4. There are exactly 2(q+1) edges between
old and new vertices. The graph induced by the new vertices therefore
has average degree

    a = [r(q+1)-2(q+1)]/r = (q+1)(r-2)/r >= (q+1)/2.

For any C4-free graph on r vertices with average degree a, counting
unordered two-edge paths and applying Cauchy--Schwarz gives

    sum_v binom(deg(v),2) <= binom(r,2),
    a(a-1) <= r-1.

But here

    a(a-1) >= (q^2-1)/4 > q-1 >= r-1,

where the strict inequality is equivalent to
q^2-4q+3 = (q-1)(q-3) > 0 for q >= 4. This is the contradiction.

## Verification and scope

The proof uses incidence uniqueness and elementary degree counts, and
applies to every even prime power q >= 4. A direct calibration using
`polarity_graph` from `verify_binary_post_square_interval.py` checks all
absolute pairs at q=4,8,16: respectively 10,36,136 pairs, each with
exactly q-1 simple three-edge paths avoiding the nucleus. These finite
checks do not enumerate extensions and are not the uniform proof.

No new Lean theorem, graph witness, or solution of Erdős 85 is claimed.
