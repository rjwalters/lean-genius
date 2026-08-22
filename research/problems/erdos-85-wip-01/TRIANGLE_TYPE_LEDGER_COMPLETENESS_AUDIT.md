# Triangle-type ledger completeness audit

## Verdict

The proposed component trace ledger

```text
q m_i m_j = |T intersect B_ij| + 2 t_ij + 2 t_ji
```

is not q-generic when there are at least three defect components.  It omits
ambient A-triangles whose three vertices lie in three distinct defect
components.

## Correct edge partition

Let `C_i` and `C_j` be distinct second-order-defect components, and let
`B_ij` be the set of A-edges between them.  The component quotient laws give

```text
|B_ij| = q m_i m_j.
```

Every edge `xy in B_ij` has codegree exactly one: `x` and `y` cannot be
adjacent in the defect graph because they lie in different defect
components, and C4-freeness bounds their A-codegree by one.  Classify its
unique common neighbor `z`:

* `z in C_i`: a two-component triangle with its internal base in `C_i`;
* `z in C_j`: a two-component triangle with its internal base in `C_j`;
* `z in C_k`, `k` distinct from `i,j`: an all-distinct-component triangle.

An `i,i,j` triangle contributes its two cross edges to `B_ij`; an `i,j,k`
triangle contributes one.  Hence, with `r_ijk` the number of unordered
ambient triangles having one vertex in each of `C_i,C_j,C_k`, the corrected
undirected ledger is

```text
q m_i m_j = 2 t_ij + 2 t_ji + sum_{k != i,j} r_ijk.
```

There is no `T` term on a cross block: `T = A intersect D`, and `D` has no
edge between distinct connected components by definition.  (If `B_ij` was
intended to denote a different block, that block must be defined before the
displayed identity can be used.)

The internal-edge identity

```text
q m_i^2 / 2 = |T intersect C_i| + 3 t_i + sum_j t_ij
```

is unaffected, because an all-distinct triangle contains no internal edge.

## Existing formal evidence

This is not a hypothetical missing case.  The repository already formalizes
multi-component ambient triangles in
`Erdos85BinarySquareCrossTriangleLiteralMixed.lean`; in particular
`literalMixedOwnerAmbientCyclicTriangles_eq_multiComponentAmbient` identifies
the ambient mixed-owner census with ambient triangles spanning multiple
defect components.

More sharply, the existing theorem
`orderSixtyFour_regular_fourComponents_rootedPattern_four_card_ge_twelve` in
`Erdos85BinarySquareMixedOwnerRootedAllDistinct.lean` forces at least twelve
prescribed-color rooted triangles through three pairwise-distinct defect
components in the four-component control branch.  Thus the omitted
all-distinct term is known to be positive in a structurally relevant regime.
That theorem is order-64 evidence already in the bank; this audit neither
extends nor reopens the parked order-64 lane.

## Consequence for the trace proposal

The q=4 two-component trace dichotomy remains valid: with only two defect
components the sum of `r_ijk` is empty.  For the q-generic mixed branch,
however, cross-edge counts cannot pin the numbers of cross-saturated versus
T-saturated weight-two cycles without also controlling the all-distinct
triangle tensor `r_ijk`.  The next valid nonlinear currency is therefore
the distribution of third-component owners of cross edges, not the
two-component triangle ledger alone.
