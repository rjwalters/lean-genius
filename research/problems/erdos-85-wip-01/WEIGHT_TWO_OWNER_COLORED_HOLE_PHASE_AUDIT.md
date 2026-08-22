# Weight-two owner-colored hole-phase audit

## Question

The commuting-hole classification reduces a cross-saturated weight-two
component to dihedral matching blocks and canonical two-fold cycle covers.
Can the exact owner/selector factorization force incompatible choices of
their phases?

The answer from the currently banked interface is **not yet**.  There are two
different factorizations, and their commutants must not be conflated.

## The two exact decompositions

Fix a normalized size-two defect component `c` of order `2q`.

1. The exterior two-point trace graph `F` is an uncolored graph on `c`.
   In the alternating cyclic sector its opposite-sign complement

   ```text
   P = K_(q,q) - F
   ```

   is a 2-factor and satisfies `[H,P]=0`, where `H=G[c]` is the internal
   cycle union.  The report `WEIGHT_TWO_MIXED_CYCLE_HOLE_DECOMPOSITION.md`
   classifies every rectangular block of `P` as a dihedral matching pair or
   a canonical two-fold cover.

2. The selector graph on `c` is edge-partitioned by the component containing
   the unique ambient selector vertex.  For a source component `e` of
   normalized order `m_e`, `sourceIndexedSizeTwoSelectorGraph G e c` is an
   `m_e`-regular spanning layer.  Distinct source components give
   edge-disjoint layers.  These are the theorems

   ```text
   binarySquare_regular_sizeTwoSelectorGraph_adj_iff_existsUnique_source
   sourceIndexedSizeTwoSelectorGraph_adj_disjoint_of_source_ne
   binarySquare_regular_sourceIndexedSizeTwoSelectorGraph_degree
   ```

   In particular a size-two source contributes a 2-factor.

The second decomposition does color the exterior traces by source component,
but it also includes the internally selected pairs and is naturally stated
on the full selector graph, not on the hole graph `P`.

## The commutant mismatch

The banked q-generic commutation theorem is

```text
[restrictedComponentOwnerGraph(source,owner), D[source]] = 0.
```

It concerns layers colored by the **owner coordinate** of the unique common
neighbor and commutation with the induced defect block.  It does not say
that a source-indexed selector layer commutes with the internal cycle union
`H`, nor that any individual color summand of `F` commutes with `H`.

Only the uncolored sum `F` is known to commute with `H`.  From

```text
[H, F_1 + ... + F_r] = 0
```

one cannot infer `[H,F_i]=0`.  Therefore the rectangular-intertwiner
classification cannot currently be applied color by color, and a phase
pigeonhole among the owner/source 2-factors would assume an unproved
statement.

There is a second indexing distinction: `restrictedComponentOwnerGraph`
fixes the owner component and restricts its color to a source ground set,
whereas `sourceIndexedSizeTwoSelectorGraph` fixes the source component that
contains the selector vertex and draws its layer on the owner ground set.
Their degree formulas are transposed shadows of the same design, but they
are not definitionally the same graph.

## Exact next statement

A genuine phase argument needs one of the following new inputs.

* **Colorwise cycle commutation:** prove that every relevant source-indexed
  exterior layer `F_e` satisfies `[H,F_e]=0`.  Then each size-two source
  layer is individually a classified commuting 2-factor and its dihedral
  phase becomes meaningful.
* **Simultaneous block equation:** without colorwise commutation, derive the
  rectangular equations for all `F_e` together, retaining both the
  source-edge partition and the owner-coordinate path-balance law.  The sum
  equation alone is insufficient.
* **Commutant transfer:** show in the surviving cyclic sector that commuting
  with `D[c]` forces commuting with `H` for the restricted owner factors.
  This requires a graph-specific relation between the two commuting
  operators; it does not follow merely from `[D[c],H]=0`.

Until one of these statements is proved, the owner coloring does not impose
a valid phase constraint on the classified hole blocks.  The useful outcome
of this audit is the precise interface: the missing information is
**colorwise commutation or an equivalent simultaneous rectangular law**, not
another quotient degree count.
