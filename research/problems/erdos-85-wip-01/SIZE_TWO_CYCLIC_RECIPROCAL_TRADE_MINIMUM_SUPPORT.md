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

Seven vertices are likewise impossible.  At a vertex the common plus/minus
degree is either two or three.  If it is three, the two sign-neighbour sets
partition all six other vertices, so deleting that vertex leaves every row
and column multiplicity even.  Two degree-three vertices must consequently
share both their row and their column, hence would be the same cell.  There
is at most one.  But the sum of the common sign degrees is `14` plus the
number of degree-three vertices and must be even.  Hence there are none.

Both sign graphs are therefore 2-regular, their union is 4-regular, and its
complement `F` is a 2-factor on seven vertices.  Encode a vertex's row class
by its standard basis vector `a_p` over `F_2`.  At `p`, the changed
neighbours are all vertices except `p` and its two `F`-neighbours.  Their row
multiplicities are even, so on every cycle of `F`

```text
a_(i-1) + a_i + a_(i+1) = C,                          (4)
```

where `C` is the total row-parity vector of `W`.  Subtracting consecutive
instances gives `a_(i+2)=a_(i-1)`: row classes are 3-periodic around every
cycle.  The identical recurrence holds for column classes.

The only 2-factor types on seven vertices are `C_7` and `C_3 disjoint C_4`.
On `C_7`, period three makes all row classes equal and all column classes
equal, repeating cells.  In the second type, period three makes all four
vertices of the `C_4` share one row and, independently, one column, again
repeating a cell.  Thus `|W|=7` is impossible.

Consequently the sharp bound supplied by the two affine margins is

```text
|W| >= 8.                                             (5)
```

It changes at least eight old and eight new undirected edges, hence at least
sixteen edge memberships in total.

This support bound is sharp for the **abstract margin conditions**.  An
eight-vertex witness, with cells listed as `(row,column)`, is

```text
0:(0,0)  1:(0,3)  2:(1,0)  3:(0,1)
4:(3,1)  5:(0,5)  6:(3,5)  7:(1,3)

minus = {04,05,13,16,23,26,47,57}
plus  = {03,06,14,15,24,25,37,67}.
```

At every vertex the two sign-neighbour pairs have equal row and column
multisets.  This witness is not asserted to extend to two cyclic codes; it
shows that any improvement beyond eight must use the moving-hole/cyclic
labels, caps, or extendability outside the trade, rather than margin parity
alone.

Even the local cyclic admissibility conditions do not improve the bound.
The checker `size_two_cyclic_trade_support_probe.py` additionally requires
every vertex to be an allowed q8 cell and every signed edge to avoid the two
forbidden target rows and columns at both endpoints.  It returns SAT at
support eight for all four hole representatives `a=0,1,2,3`, for example:

```text
python3 size_two_cyclic_trade_support_probe.py 8 8 --a 1
```

The checker deliberately does not require either sign pattern to extend to
a full code and does not impose caps.  Thus the surviving discriminator is
global extendability, cap preservation, or strict defect-rank change, not
merely allowed-fibre or endpoint-admissibility checks.

## Consequence for local cycle descent

A source-local transposition or three-cycle from the q8 descent census is
only the seed of a physical move.  After reciprocity is imposed, its target
vertices initially see one changed edge of each relevant sign and cannot be
terminal by the no-degree-two lemma.  Closure must propagate until every
affected source has a complete local column cycle.  Thus:

- an ordinary graph 2-switch is too small;
- a single collision-edge orientation token is too small; and
- the first meaningful bounded search is for a symmetric Latin bitrade on
  at least eight cells and at least sixteen toggled edge memberships.

The theorem is q-generic and does not use caps or the power-of-two
hypothesis.  Caps enter only when asking whether both endpoints `K,K'` of
such a closed trade remain packing codes and whether the trade lowers total
defect rank.
