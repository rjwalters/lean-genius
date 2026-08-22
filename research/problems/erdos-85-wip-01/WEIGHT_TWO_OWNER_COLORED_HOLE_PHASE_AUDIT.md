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

At the level of the separate APIs alone, the owner coloring does not impose
a valid dihedral phase constraint on the classified hole blocks.  The useful
interface is **colorwise commutation or an equivalent simultaneous
rectangular law**, not another quotient degree count.  The next subsection
extracts the latter law from the block form of the banked defect commutation.

## A simultaneous rectangular law that is already available

The commutant mismatch nevertheless yields a real colorwise equation after
resolving the alternating sign shores.  Let `e != c` be an exterior source
component and let `O_e` be its selector layer on `c`.  This is the same
relation described from the two transposed viewpoints

```text
restrictedComponentOwnerGraph G c e
sourceIndexedSizeTwoSelectorGraph G e c.
```

The first presentation supplies `[O_e,D[c]]=0`; the second supplies its
source-component meaning and degree.  Because an exterior selector vertex
has one neighbor in each alternating sign shore, `O_e` is bipartite.  In
sign-ordered blocks write

```text
O_e  = [[0, Q_e], [Q_e^T, 0]],
D[c] = [[D_+, P], [P^T, D_-]].
```

Here the cross-sign block of `D[c]` is exactly the hole block
`P=K_(q,q)-F`: opposite-sign pairs cannot have an internal common neighbor,
so they are defect-adjacent precisely when they are not exterior traces.
Expanding `[O_e,D[c]]=0` gives, for every exterior source color `e`,

```text
Q_e P^T = P Q_e^T,             (colored hole equation)
Q_e D_- = D_+ Q_e.             (same-shore intertwining)
```

Thus the bank does contain an equivalent simultaneous rectangular law; it
is weaker than `[H,Q_e]=0` but stronger than the uncolored quotient.  The
next phase consumer should classify binary biregular matrices `Q_e` that
simultaneously satisfy these two equations and edge-partition
`F=K_(q,q)-P`.  Applying the dihedral classification directly to `Q_e`
remains invalid, but ignoring these two equations would also discard the
available owner coupling.

The remaining formal task is a shore-block extraction theorem packaging the
displayed equations from the existing global commutation theorem.  Its
mathematical content is matrix block multiplication; the graph-facing inputs
to expose are (i) exterior owner layers are opposite-sign and (ii) the
cross-sign defect block equals the hole relation.

## Uniform cyclic factorization countermodel

The first colored equation alone still gives no obstruction, even together
with binary degree two and exact edge partition.  This has a q-generic
construction.

Let `q` be even and let `S` be the cyclic shift matrix on one q-point sign
shore.  After a cyclic relabeling, take the hole block

```text
P = I + S^delta
```

with `delta` odd.  (The two shifts of an opposite-sign cyclic hole factor
differ by an odd residue.)  The involution

```text
R(a) = delta-a
```

on `Z/qZ` has no fixed point: `2a=delta` has no solution for even `q` and odd
`delta`.  Its orbit `{0,delta}` is exactly the pair of shifts used by `P`.
For every other orbit define

```text
Q_[a] = S^a + S^(delta-a).
```

Then each `Q_[a]` is binary with every row and column of degree two, distinct
orbits have disjoint support, and

```text
sum_[a] Q_[a] = J-P.
```

Moreover every color satisfies the colored hole equation, since

```text
Q_[a] P^T
 = S^a + S^(a-delta) + S^(delta-a) + S^(-a)
 = P Q_[a]^T.
```

Thus `(q-2)/2` size-two colors give a complete legal factorization of the
cross-sign trace block at the level of

```text
binary + degree two + edge partition + Q_e P^T = P Q_e^T.
```

In the one-cycle alternating sector, even the second colored equation adds
no restriction.  Number the positive and negative shores compatibly with the
ambient cycle.  Two same-sign vertices have an internal common neighbor
exactly at cyclic separation one, so

```text
D_+ = D_- = J-I-C_q.
```

This matrix is circulant.  Every `Q_[a]` above is circulant as well, and hence

```text
Q_[a] D_- = D_+ Q_[a].
```

The internal-source selector layer supplies the omitted same-sign cycle
edges, while the exterior size-two layers `Q_[a]` partition the opposite-sign
trace block.  Therefore the construction realizes the entire
single-component owner-factor algebra:

```text
binary regular layers,
exact edge partition,
[O_e,D[c]]=0 for every exterior color e.
```

It is still not asserted to realize a full ambient graph, because the same
source color must define compatible selector layers on every other target
component, with unique ambient selector vertices and C4-free routing between
them.  The conclusion is sharper: neither colored block equation nor any
single-component cyclic phase count can close
`BinarySizeTwoCyclicPackingBound`.  A valid terminal must couple the layers
of one source component across multiple target components (or use an
equivalent exterior-routing law).
