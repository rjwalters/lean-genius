# A-REG centered cubic audit

Status: the cubic matrix identity is useful infrastructure, but its scalar
trace specialization is not a terminal for the hardest `q = 8`,
`[2,2,2,2]` partition.

## Formal results

The integrated proof branch contains:

- `86599cab02`: `sum_c C_c^3 = (q((q-1)I-D))^3`, including its trace form;
- `7454419a3d`: the one-color evaluation
  `tr(C_c^3) = q^3 (tr(O_c^3) + q^2(q-1)m_c^2(3-m_c))`;
- `cb0f1a55f0`: the cancelled global equation and
  `q^2 | tr(D^3) + sum_c tr(O_c^3)`.

All three modules compile under Lean 4.31 without warnings.

The graph-level object surviving the scalar audit is now formalized in
`Erdos85BinarySquareSizeTwoSelectorGraph`.  The `PROVEN` theorem
`binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph`
packages the selector graph `L_c` and proves

```text
L_c = complement(D[c]).
```

The companion theorem `binarySquare_regular_sizeTwoSelectorGraph_degree`
proves that `L_c` is `q`-regular on the `2q` points of `c`.  Thus subsequent
blockwise spectral or fourth-moment work can consume an actual Lean graph,
not only the pairwise prose interpretation.

The first blockwise spectral layer is also `PROVEN`.  Theorems
`binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_resolution` and
`binarySquare_regular_sizeTwoSelectorGraph_adjMatrix_comm` give

```text
I + A(D[c]) + A(L_c) = J,
A(D[c]) A(L_c) = A(L_c) A(D[c]).
```

On the zero-sum subspace,
`binarySquare_regular_sizeTwoSelectorGraph_mulVec_of_sum_eq_zero` specializes
this to `A(L_c)f = -f-A(D[c])f`.  The explicit theorem
`binarySquare_regular_sizeTwoSelectorGraph_eigenvalue_transport` therefore
sends every integral defect eigenvalue `mu` to selector eigenvalue `-1-mu`
on the same vector.  This retains information discarded by scalar trace and
is the current interface for simultaneous block constraints.

The first shared-indexing constraint is now `PROVEN` uniformly, not merely
for size-two parts.  For distinct defect components `c,d`,
`existsUnique_mem_cross_componentNeighborFinsets` says that every
`(u,v) in c×d` lies in the two corresponding selectors of a unique ambient
vertex.  In the all-two branch each ambient vertex therefore contributes a
`2×2` rectangle, and these `q²` rectangles partition the full
`(2q)×(2q)` cross-product.  The remaining compatibility gap is to turn this
rectangle partition into a restriction on the four commuting complement
blocks, rather than merely count it.

## Triangle interpretation

For a component `c`, the selector of an ambient vertex `x` is
`N_G(x) intersect c`.  The owner graph `O_c` is the intersection graph of
these selectors.  Every point `z in c` contributes the clique `N_G(z)` of
order `q` in `O_c`.  C4-freeness makes the resulting star triangles disjoint,
so the forced star contribution is

```text
|c| * choose(q,3) = q m_c choose(q,3).
```

Summed over colors, this is the partition-independent baseline
`q^2 choose(q,3)`.

## Why `[2,2,2,2]` is tautological

When `q = 8` and every `m_c = 2`, the selectors are two-element sets.  They
therefore form a simple graph `L_c` on the 16 points of `c`, with one edge for
each ambient vertex.  Point replication is eight, so `L_c` is 8-regular.

For distinct `u,v in c`, the pair is an edge of `L_c` exactly when it has a
common ambient neighbor.  By the second-order defect definition and
C4-freeness, this is exactly when `u,v` are not adjacent in `D[c]`.  Hence

```text
L_c = complement(D[c]).
```

Triangles of `O_c` are either star triangles or triangles of `L_c`.  The
cancelled cubic identity at partition `[2,2,2,2]` reduces to

```text
sum_c (triangles(D[c]) + triangles(complement(D[c]))) = 448.
```

But every `D[c]` is 7-regular on 16 vertices, and Goodman's identity gives

```text
triangles(H) + triangles(complement(H))
  = choose(16,3) - (1/2) * 16 * 7 * 8
  = 112.
```

There are four components, so the right side is automatically `4*112=448`.
Thus scalar cubic trace contains no new information in this branch.

## Consequence for the search

Do not spend further effort on scalar moments through degree three as an
all-two terminal.  A useful next invariant must retain information lost by
trace, for example:

1. a blockwise/eigenvalue refinement of `C_c^3`;
2. compatibility among the four complement graphs `L_c` imposed by the
   shared ambient vertex indexing;
3. a fourth moment that counts paired Berge triangles/4-walk collisions; or
4. the self-indexed diagonal-cycle constraint inside each `L_c`.
