# Size-two simultaneous routing partition audit

Status: q-generic synthesis of already proved routing and self-indexing
theorems, 2026-08-22.  The routing-color partition itself is already
formalized; this note isolates its endpoint-color identification with the
self-indexed diagonal blocks, which is absent from a single ODC or a single
target factorization.

## 1. Setup

Assume the binary square-order regular branch, and assume every second-order
defect component has normalized weight two.  Hence every component has order
`2q`, there are `r = q/2` components, and every cross-incidence block

```text
R_cd = Adj(G)[c,d]
```

is a `2q x 2q` zero-one matrix with every row and column sum equal to two.
The symmetry of the ambient graph gives

```text
R_dc = R_cd^T.                                           (1)
```

For a component `c`, write `A_c = Adj(G[c])`.  The self-indexing theorem is
the exact diagonal identity

```text
R_cc = A_c.                                              (2)
```

The relevant formal inputs are:

* `defectComponentCrossIncidenceMatrix_transpose`;
* `binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package`;
* `defectComponentSelfIncidenceMatrix_eq_induced_adjMatrix` and
  `binarySquare_regular_sizeTwoPart_selfIndexedBlock_package`;
* `transpose_cross_mul_cross_apply_eq_ite_intermediate`;
* `binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four`;
* `binarySquare_regular_threeSizeTwoParts_routing_column_card_eq_four`.

The graph-facing factor package and its entrywise resolution are already
formalized in `Erdos85OrderSixtyFourRoutingColorFactors` and
`Erdos85OrderSixtyFourRoutingColorRectangularOrthogonality`.  Sections 2 and
the first half of Section 4 below are therefore a matrix translation of
banked facts, not a new theorem claim.  The new synthesis begins with the
self-indexed endpoint identification (6).

## 2. Exact intermediate-component partition

Fix distinct endpoint components `c,e`.  For every component `d`, define

```text
Q_d^(c,e) = R_dc^T R_de = R_cd R_de.                    (3)
```

For `x in c` and `z in e`, C4-freeness and the square-order codegree law give
a unique common neighbor of `x,z`.  Its defect component is exactly
`crossIntermediateComponent G hfree hce x z`.  The proved matrix-entry
theorem therefore says

```text
Q_d^(c,e)(x,z) = 1  iff  d is that intermediate component,
Q_d^(c,e)(x,z) = 0  otherwise.                          (4)
```

Consequently the `r=q/2` matrices in (3) have pairwise disjoint support and

```text
sum_d Q_d^(c,e) = J_(2q,2q).                            (5)
```

The routing row/column theorems show that every `Q_d^(c,e)` has all row and
column sums equal to four.  Thus (5) is an exact decomposition of the complete
bipartite relation between `c` and `e` into `q/2` canonically colored
4-regular bipartite relations.  This is stronger than the scalar statement
that there are `q/2` colors: it pins every entry to its unique intermediate
component.

## 3. The self-indexed endpoint layers

Equations (1)-(2) identify the two endpoint colors in (5):

```text
Q_c^(c,e) = A_c R_ce,
Q_e^(c,e) = R_ce A_e.                                   (6)
```

Therefore both products in (6) are zero-one, 4-regular, and support-disjoint:

```text
(A_c R_ce) hadamard (R_ce A_e) = 0.                     (7)
```

For every third component `d`, the remaining layer is

```text
Q_d^(c,e) = R_cd R_de.                                  (8)
```

Equations (5)-(8) are the simultaneous self-indexed routing partition:

```text
A_c R_ce + R_ce A_e
  + sum_(d != c,e) R_cd R_de = J,                       (SRP)
```

and every summand is a disjoint-support 4-regular zero-one matrix.

The endpoint identification is the precise coherence condition missed by choosing pairwise ODCs or
paired cross-factor intertwiners independently.  The same cross block `R_ce`
must simultaneously avoid the two endpoint cycle-route supports in (7), and
all residual entries must split into the products through the other component
blocks as in (8).

At `q=8`, (SRP) has exactly four layers: the two forced endpoint layers and
exactly two exterior layers.  Each row has the rigid partition

```text
4 + 4 + 4 + 4 = 16.
```

Thus the order-64 all-size-two terminal can be attacked as a four-color
factorization of `K_(16,16)`, with two colors fixed by the internal cycle
systems and the cross 2-factor.  This is substantially smaller than a fresh
64-vertex graph census and does not invoke either prohibited endpoint lane.

## 4. What this does and does not prove

The uncolored sum in (SRP) is the `(c,e)` block of the ambient square identity,
so summing entries, taking ordinary row sums, or reducing the whole equation
modulo two gives no new contradiction.  The information is entirely in:

1. zero-one support of every individual product;
2. pairwise disjointness of those supports;
3. the forced endpoint forms `A_c R_ce` and `R_ce A_e`;
4. reuse of each `R_cd` in the routing partitions for every other endpoint.

In particular, (7) alone is only the no-four-cycle condition inside the
two-component induced graph.  A closing invariant must compare (SRP) for at
least two different endpoint pairs, so that one exterior product in one
partition becomes an endpoint-constrained factor in another.

The next nonduplicative theorem target is therefore the formal matrix package
for (SRP), followed by a q-generic classification (or countermodel) of four
size-two coordinates satisfying all six coupled routing partitions.  A
single-pair spectral, row-sum, or phase argument cannot consume the new data.
