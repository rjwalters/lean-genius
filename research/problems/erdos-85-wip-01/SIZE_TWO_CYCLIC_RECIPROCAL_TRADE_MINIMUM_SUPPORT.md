# Reciprocal trade minimum-support theorem

Node: cap-preserving defect-rank descent beneath
`BinarySizeTwoCyclicPackingBound`.

## Setup

Let `K` and `K'` be two reciprocal routing codes on the same allowed cells,
both satisfying the exact target-row and absolute-target-column hit laws.
Colour an edge **minus** if it belongs to `K\K'` and **plus** if it belongs
to `K'\K`.  Let `W` be the set of vertices incident with a changed edge.

At every vertex `p`, the minus and plus degrees agree because both codes
have degree `q-2`.  More strongly, their incident target-row multisets agree
and their absolute-target-column multisets agree, since both codes hit the
same prescribed 0/1 margins.

## No degree-two changed vertex

Suppose an affected vertex had one minus neighbour `v` and one plus
neighbour `w`.  Equality of its row margins would force `v,w` to have the
same target base row.  Equality of its column margins would force them to
have the same absolute target column.  A cell is uniquely determined by
these two coordinates: its fibre is column minus row.  Hence `v=w`,
contradicting that one edge is removed and the other added.

Therefore every affected vertex has

```text
minus degree >= 2,    plus degree >= 2.               (1)
```

Equivalently, every nonzero symmetric-difference component has ordinary
degree at least four, with at least two edges of each sign at every vertex.
This uses both exact projections essentially; degree regularity alone would
permit an alternating cycle with one edge of each sign.

## Minimum closed trade size

The minus and plus graphs are edge-disjoint simple graphs on the same set
`W`.  By (1), each contains at least `|W|` edges.  Since their union is a
simple graph,

```text
2|W| <= choose(|W|,2),
```

so initially every nontrivial reciprocal trade has

```text
|W| >= 5.                                             (2)
```

The affine margins exclude equality in (2).  If `|W|=5`, both sign graphs
have exactly five edges and degree two everywhere, so they are two 5-cycles
whose union is `K_5`.  At each `p in W`, its two minus neighbours and two
plus neighbours partition `W\{p}` and have equal row multisets.  Therefore,
after deleting any `p`, every target-row multiplicity among the other four
vertices is even.

Let `c_y` be the number of vertices of `W` in row `y`.  Deleting a vertex in
row `y` says `c_y` is odd and every other occupied row count is even.  If two
rows `y,z` are occupied, deleting a vertex first in `y` and then in `z` says
that `c_z` is respectively even and odd, a contradiction.  Hence all five
vertices would lie in one row.  In one row a cell is uniquely determined by
its absolute column; equality of the two disjoint two-element column
multisets at any `p` is then impossible.

The six-vertex case is also impossible.  If `|W|=6`, disjointness of the two
sign-neighbour sets and equality of their degrees force both sign degrees to
be exactly two at every vertex.  Their union is 4-regular, so its complement
in `K_6` is a perfect matching `mu`.

For every matched pair `{p,mu(p)}`, the other four vertices are precisely the
two plus and two minus neighbours of `p`; hence all their row multiplicities
and all their column multiplicities are even.  Modulo two, every `mu`-pair
therefore has the same row-incidence vector.  Either all three pairs lie
within rows, or all three join the same two rows.  The identical dichotomy
holds for columns.

The within-row and within-column alternatives cannot both hold, since a
matched pair would then repeat one cell.  The two cross alternatives cannot
both hold, since six distinct cells cannot lie in a 2-by-2 grid.  Up to
interchanging rows and columns, `W` must therefore be the full 3-by-2 grid,
with `mu` pairing the two cells in each row.

Consider only the minus graph.  Between each pair of two-cell rows its edges
form a perfect matching: at every vertex the two minus neighbours must lie
in the two other rows, and their columns must be different.  A perfect
matching between two two-cell rows has a binary type, parallel or crossed.
At each of the three rows, the types on its two incident row-pairs must
differ, because its two minus neighbours have different columns.  This asks
the three binary row-pair types to be pairwise different, which is
impossible.  The 2-by-3 case is symmetric.

Consequently the sharp bound supplied by the two affine margins is

```text
|W| >= 7,                                             (3)
```

and a nontrivial closed trade changes at least seven old and seven new
undirected edges, hence at least fourteen edge memberships in total.

## Consequence for local cycle descent

A source-local transposition or three-cycle from the q8 descent census is
only the seed of a physical move.  After reciprocity is imposed, its target
vertices initially see one changed edge of each relevant sign and cannot be
terminal by the no-degree-two lemma.  Closure must propagate until every
affected source has a complete local column cycle.  Thus:

- an ordinary graph 2-switch is too small;
- a single collision-edge orientation token is too small; and
- the first meaningful bounded search is for a symmetric Latin bitrade on
  at least seven cells and at least fourteen toggled edge memberships.

The theorem is q-generic and does not use caps or the power-of-two
hypothesis.  Caps enter only when asking whether both endpoints `K,K'` of
such a closed trade remain packing codes and whether the trade lowers total
defect rank.
