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

As a calibration only, at `q=8`, (SRP) has exactly four layers: the two forced
endpoint layers and exactly two exterior layers.  Each row has the rigid partition

```text
4 + 4 + 4 + 4 = 16.
```

Thus the parked order-64 all-size-two terminal admits a four-color
factorization of `K_(16,16)`, with two colors fixed by the internal cycle
systems and the cross 2-factor.  This observation is diagnostic only: the
order-64 lane is operator-gated, and this note neither proposes nor authorizes
a `q=8` census, SAT run, or endpoint attack.

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
for (SRP), followed by a **q-generic** classification (or uniform
countermodel) of simultaneous size-two coordinates satisfying all coupled
routing partitions.  A single-pair spectral, row-sum, or phase argument cannot
consume the new data.  No order-64-only classification belongs to this lane
without a new operator direction.

## 5. Cubic contraction audit

There is one tempting way to compare three endpoint partitions which is
already completely banked.  For pairwise distinct endpoint components
`c,e,f` and a routing color `d`, form

```text
T_d(x,z,w) = Q_d^(c,e)(x,z)
             Q_d^(e,f)(z,w)
             Q_d^(c,f)(x,w).                            (9)
```

Its support consists of endpoint triples whose three pairwise routes all have
intermediate component `d`.  The three canonical common neighbors either
coincide (the star completion) or are pairwise distinct and form an
owner-colored rainbow triangle inside `d`.  This is exactly the content of:

* `monochromatic_routing_completion_star_or_rainbow`;
* `binarySquare_regular_sizeTwoRoutingColor_two_lifts_or_owner_rainbow`;
* `binarySquare_regular_sizeTwoRoutingColor_rainbow_or_all_two_lifts`;
* `routingRainbowEndpointTriples_card_eq_ownerRainbowTriples_card`.

Thus an undifferentiated cubic sum of (9) cannot be advertised as a new
three-coordinate invariant.  In the no-rainbow branch the existing theorem
already gives the exact two canonical lifts; in the rainbow branch the exact
bijection transports the residual count to owner-factor triangles.

The genuinely unconsumed refinement is to intersect (9) with the endpoint
identities (6), especially when `d` equals one of `c,e,f`.  Then one factor is
forced to be `A_c R`, `R A_e`, or its cyclic analogue, so the star/rainbow
completion is constrained by a distinguished internal cycle step.  A next
argument must exploit that marked cycle step (or give a uniform model for it);
merely recounting monochromatic routing triples duplicates the existing
routing-rainbow package.

## 6. Endpoint-marked rooted normal form

Fix pairwise distinct endpoint components `c,e,f`, a root `x in c`, and take
the routing color to be the endpoint `c`.  Let the two internal neighbors of
`x` in the 2-regular graph `G[c]` be `u_0,u_1`.  The generic theorem
`routingRow_eq_biUnion_componentCrossNeighborFinset`, together with
`routingRow_starRows_pairwise_disjoint`, specializes to

```text
{z in e : route(x,z)=c} = Z_0 disjoint-union Z_1,
Z_i = N_G(u_i) cap e,             |Z_i|=2,              (10)

{w in f : route(x,w)=c} = W_0 disjoint-union W_1,
W_i = N_G(u_i) cap f,             |W_i|=2.              (11)
```

Thus the endpoint-colored four-point routing row is not merely an arbitrary
four-set: it is canonically paired by the two internal cycle directions at
`x`.

Now count pairs `(z,w)` for which all three routes `(x,z),(z,w),(x,w)` have
color `c`.

* If `z in Z_i` and `w in W_i`, then `u_i` is their common center.  These are
  the forced star completions.  There are exactly

  ```text
  2 * |Z_i| * |W_i| = 2 * 2 * 2 = 8.                  (12)
  ```

* If `z in Z_i` and `w in W_j` with `i != j`, a color-`c` route from `z` to
  `w` has a center `y in c` distinct from `u_i,u_j`.  The edges
  `u_i-y` and `y-u_j` in the owner factorization are owned by `e` and `f`,
  respectively.  Conversely such a colored two-step middle `y` has unique
  subdivision vertices `(z,w)` by C4-freeness.  Hence the excess over (12)
  is exactly

  ```text
  E_x(e,f) = |N_(O_e[c])(u_0) cap N_(O_f[c])(u_1)|
           + |N_(O_e[c])(u_1) cap N_(O_f[c])(u_0)|.    (13)
  ```

Every restricted owner factor on a size-two source component is 2-regular,
so each intersection in (13) has size at most two.  The rooted endpoint-color
count therefore has the exact form

```text
8 + E_x(e,f),                 0 <= E_x(e,f) <= 4.       (14)
```

Summing the forced term over the `2q` roots of `c` gives `16q`; the residual
sum `sum_x E_x(e,f)` is precisely the owner-rainbow contribution whose
unmarked version is handled by the bijection in Section 5.

This exposes the remaining local question without overclaiming: the present
bank gives neither parity nor a positive lower bound for `E_x(e,f)`.  Such a
claim would require a new interaction between the two restricted owner
2-factors across the distinguished self edge `{u_0,u_1}`.  Their separate
commutation with `D[c]` does not imply that they commute with each other.
Consequently (14) is a normal form, not yet a contradiction; the next useful
input must constrain these oriented intersections simultaneously as `x`,
`e`, and `f` vary.

## 7. Marked-triangle / defect-codegree bridge

Let `F_a` denote the owner-`a` factor restricted to `c`.  The owner
factorization edge-partitions the q-regular selector complement

```text
H_c = complement(D[c]) = disjoint-union_a F_a,           (15)
```

and `F_c` is the distinguished self-source distance-two 2-factor.

Here "distance-two" means the proved distinct-common-neighbor graph, not
graph-metric distance exactly two.  Consequently an internal `C_3` maps to
another `C_3` (each pair shares the third vertex).  An internal `C_4` would
degenerate to a matching because opposite roots repeat the same pair, but it
is excluded by ambient C4-freeness.  Thus `F_c` is indeed 2-regular in the
present branch, including triangle components.

The two summands in (13) are exchanged by swapping `e` and `f`, so

```text
E_x(e,f) = E_x(f,e).                                    (16)
```

More intrinsically, let `s_x={u_0,u_1}` be the `F_c` edge indexed by the root
`x`.  For an unordered pair of distinct exterior colors `{e,f}`, `E_x(e,f)`
is exactly the number of triangles of `H_c` containing `s_x` whose other two
edges have colors `e` and `f`.  Hence summing `E_x(e,f)` over exterior color
pairs counts the exterior-rainbow part of the triangles through the marked
self edge.

The full number of triangles of `H_c` through `s_x` is

```text
codeg_(H_c)(u_0,u_1).                                   (17)
```

It also has an exact defect interpretation.  On `2q` vertices, `D[c]` is
`(q-1)`-regular and `H_c = J-I-D[c]`.  Expanding the square gives

```text
H_c^2 = I + D[c]^2 + 2D[c].                             (18)
```

Since `s_x` is an `H_c` edge, it is not a `D[c]` edge, and its endpoints are
distinct.  Evaluating (18) at `(u_0,u_1)` therefore yields

```text
codeg_(H_c)(u_0,u_1) = codeg_(D[c])(u_0,u_1).           (19)
```

Thus endpoint-marked routing supplies a colored refinement of a defect
codegree across every self-source edge.  Explicitly, the right side of (19)
splits on the left into:

1. the exterior-rainbow terms `E_x(e,f)`;
2. exterior-monochromatic triangles (both remaining edges in one `F_e`);
3. triangles using another self-color edge and one exterior edge;
4. triangles lying wholly in the self factor `F_c`.

Equation (19) is exact but does not by itself fix any one class.  In
particular, symmetry (16) gives no parity: it merely says the rainbow count is
indexed by unordered exterior color pairs.  A closing q-generic invariant
must control the other three classes, or compare the colored decomposition of
(19) at consecutive roots of the internal cycle.  Ordinary triangle totals
erase precisely this marked-edge information, as already observed in the
owner triangle inventory.
