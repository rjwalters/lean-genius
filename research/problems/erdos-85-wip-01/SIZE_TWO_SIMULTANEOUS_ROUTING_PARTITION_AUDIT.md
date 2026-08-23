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

## 8. Joint-moment form of the marked mass

Write `A_c` for the adjacency matrix of the internal 2-factor `G[c]`, `S_c`
for the adjacency matrix of the self-source factor `F_c`, and `D_c` for
`D[c]`.  C4-freeness makes every off-diagonal common-neighbor count in
`G[c]` Boolean, while every diagonal entry of `A_c^2` is two.  The
distinct-common-neighbor theorem therefore gives the integer matrix identity

```text
S_c = A_c^2 - 2I.                                      (20)
```

This also covers an internal triangle: for `C_3`, `A_c^2-2I=A_c`.

Let `M_c` count pairs consisting of an `H_c`-triangle and a distinguished
self edge of that triangle.  (A triangle with two self edges is counted
twice.)  Summing (17) over the edges of `F_c` gives

```text
2 M_c = trace(S_c H_c^2) = trace(S_c D_c^2),            (21)
```

where the second equality is the summed form of (19).  The factor two comes
from the two orientations of every marked edge in the matrix trace.

The global commutation `AD=DA` restricts to `A_c D_c=D_c A_c`, because `D`
is block diagonal on its connected components.  Substituting (20) into (21)
and using this commutation yields

```text
2 M_c
  = trace((A_c^2-2I)D_c^2)
  = trace((A_c D_c)^2) - 2 trace(D_c^2)
  = trace((A_c D_c)^2) - 4q(q-1).                      (22)
```

Thus the endpoint-marked routing mass is a genuine joint fourth moment of the
internal cycle block and the defect block.  It is not determined by the
ordinary spectra of `A_c` and `D_c` separately: their common eigenbasis (or,
equivalently, the placement of `D_c` inside the commutant of the cycle
system) is required.

Equation (22) gives the necessary inequality

```text
trace((A_c D_c)^2) >= 4q(q-1),                          (23)
```

but this is just `M_c >= 0`; it is not a terminal by itself.  Its value is
that it identifies the exact spectral consumer of the colored refinement in
Section 7.  Any useful parity or lower bound for the exterior-rainbow portion
must refine (22) by owner colors, rather than recomputing the already fixed
uncolored trace.

## 9. Collision-table and parity localization

The joint moment has a more concrete entrywise form.  Put

```text
B_c = A_c D_c = D_c A_c.                                (24)
```

For vertices `x,k in c`, the entry `B_c(x,k)` counts the internal neighbors
of `x` that are defect-adjacent to `k`.  Since `x` has exactly two internal
neighbors,

```text
B_c(x,k) in {0,1,2}.                                    (25)
```

The self edge indexed by `x` is precisely the pair of those two internal
neighbors.  Thus `k` is a defect common neighbor of that self edge exactly
when both are defect-adjacent to `k`, equivalently when `B_c(x,k)=2`.
Using (19), this gives the exact collision-table identity

```text
M_c = #{(x,k) in c x c : B_c(x,k)=2}.                   (26)
```

It also recovers (22) without spectral language.  Every row of `B_c` has sum
`2(q-1)`, so

```text
sum_(x,k) B_c(x,k) = 4q(q-1).
```

For entries in `{0,1,2}`, `b^2=b+2*choose(b,2)`, and `choose(b,2)` is the
indicator of `b=2`.  Hence

```text
trace(B_c^2) = sum_(x,k) B_c(x,k)^2
             = 4q(q-1) + 2M_c,                         (27)
```

because `B_c` is symmetric.

Symmetry also localizes the parity question.  Off-diagonal entries equal to
two occur in transposed pairs, so

```text
M_c mod 2 = #{x in c : B_c(x,x)=2} mod 2.               (28)
```

Finally, `B_c(x,x)` is the number of the two internal `G[c]` edges incident
to `x` that are also edges of `D_c`.  Therefore

```text
B_c(x,x)=2
  iff both internal cycle edges at x are triangle-free edges of G.  (29)
```

Here “triangle-free edge” is literal: for an ambient edge `xy`, membership in
the second-order defect graph says that `x,y` have no common ambient neighbor.

Equations (28)-(29) show exactly why the raw joint trace did not decide
parity.  Evenness of `M_c` is equivalent to evenness of the number of internal
cycle vertices whose two incident internal edges are both triangle-free.

For even `q`, the bank is stronger than the handshake lemma:

* `binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two`
  says every vertex of `c` has triangle-free degree zero or two;
* `binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_of_reachable`
  says this status is constant along every connected component of `G[c]`.

Therefore the diagonal-two set in (28) is a disjoint union of whole internal
cycles, and

```text
M_c mod 2
  = (total order of the all-triangle-free internal cycles in c) mod 2. (30)
```

This removes arbitrary cycle runs from the residual.  The exact remaining
question is whether the triangle-free/antipodal color trace forces the total
order in (30) to be even for every normalized size-two defect component, or
only after summing across components.  Commutation and row sums alone stop at
(28); the proved 0-or-2 propagation sharpens the missing input to the
componentwise parity in (30).

In particular, (30) is automatically even when `G[c]` is a single internal
cycle: its all-triangle-free order is either zero or the full order `2q`.
The parity residual exists only for a size-two defect component containing at
least two internal cycles, with an odd total order among the all-triangle-free
ones.  This cleanly separates the already harmless connected internal-cycle
case from the genuine mixed-cycle case.

There is a stronger sectorwise conclusion.  Under the full-support
`-2` alternating-eigenline hypotheses, the banked theorem
`binarySquare_regular_sizeTwoPart_internalCycle_even_six_le` says that
**every** connected component of `G[c]` has even order.  Consequently every
all-triangle-free internal cycle has even order separately, and (30) gives

```text
M_c = 0  (mod 2)                                             (31)
```

for an arbitrary number of internal cycles.  Thus the multi-cycle parity
residual is absent throughout the full-support `-2` sector, not only in its
single-cycle subcase.  Any genuinely odd residual in (30) requires failure
of that hypothesis (for example, no full-support `-2` eigenline, or a
candidate `-2` eigenvector vanishing on an internal cycle).  This does not
exclude other signed joint eigenvalues `mu`; it routes the residue away from
the specifically alternating `mu=-2` cell toward the transport/other-mode
side of the dispatcher.

The same elementary recurrence sharpens that routing.  Suppose more
generally that `s` is full-support with values in `{+1,-1}` and

```text
A_c s = mu s.
```

At a vertex, the two neighboring signs sum to `-2`, `0`, or `2` times the
sign at that vertex.  Since `mu` is common to the whole component,

```text
mu in {-2,0,2}.                                             (32)
```

For `mu=-2`, signs alternate at every step, so each internal cycle is even.
For `mu=0`, the cycle recurrence is `s_(i+2)=-s_i`, whose nonzero sign
pattern has exact period four; every internal cycle therefore has order
divisible by four.  Both modes force `M_c` even by (30).  Consequently an
odd collision residue can coexist with a full-support signed joint eigenline
only in the internal `mu=2` mode (where signs are constant on each internal
cycle), or else in the no-full-support-signed-eigenline transport branch.
This isolates the residue more sharply than the `-2` statement alone; it
does not claim that the `mu=2` mode is itself realizable.

The `mu=2` branch cannot be closed from the commuting exterior-pair quotient
alone.  There is an explicit abstract model on sixteen points.  Split the
points into two sign shores of order eight and put

```text
H_+ = H_- = C3 disjoint_union C5.
```

On the two shore copies, let `Z` be the bipartite two-regular relation which,
on each corresponding cycle, joins a vertex to its copy and to the copy of
its successor.  Put `X=J-Z` and

```text
H = diag(H_+,H_-),             R = [[0,X],[X^T,0]].
```

Then `R` is connected, bipartite, and six-regular; `HR=RH`; and for the sign
vector `s=(1^8,-1^8)` one has

```text
Hs = 2s,                       Rs = -6s.                 (33)
```

The four-cycle quotient of `R`, with component order
`(C3_+,C5_+,C3_-,C5_-)`, is

```text
[[0,0,1,5],
 [0,0,3,3],
 [1,5,0,0],
 [3,3,0,0]].
```

It satisfies row sum six, weighted reciprocity, the target-size bounds, and
the diagonal separation bound `0+3 <= |C|`.  The pointwise separation input
also holds: an `R`-edge crosses the sign shores, while the two `H`-neighbor
sets lie in different shores and hence have empty intersection.

If only `C3_+` is declared all-triangle-free, the residue in (30) is odd.
This declaration is deliberately not asserted to arise from an ambient
graph: its role is to prove that **all currently banked `H/R` quotient and
joint-eigenline data leave the triangle-free cycle selector free enough to
carry odd parity**.  Thus the remaining `mu=2` consumer must use an identity
involving the second-order defect block (or the ambient triangle owner data),
not merely shore balance, commutation, regularity, separation, or the
component quotient ledger.  Equivalently, it must couple the selector to
the `R` quotient rather than treating it as an arbitrary union of internal
cycles.

That coupling is supplied by
`exteriorPairGraph_adj_iff_not_defect_and_no_internal_common`.  In the
`mu=2` joint line, `s` is constant on each internal cycle, while every
`R`-edge reverses `s`; hence no two vertices on the same internal cycle are
`R`-adjacent.  Now take an internal ambient edge `xy`.

* If its cycle is a `C3`, the third vertex is an internal common neighbor of
  `x,y`.  Thus `xy` is not a second-order defect edge and the entire cycle is
  all-triangle.
* If its cycle has order at least four, adjacent cycle vertices have no
  internal common neighbor.  They are not `R`-adjacent, so the adjacency
  criterion forces them to be second-order defect adjacent.  Since `xy` is
  already an ambient edge, it cannot be antipodal; it is a triangle-free
  edge.  Thus the entire cycle is all-triangle-free.

Consequently the formerly arbitrary selector is exact:

```text
all-triangle cycles = the internal C3 components,
all-triangle-free cycles = every other internal cycle.       (34)
```

Because the size-two component has even order `2q`, equations (30) and (34)
give the generic reduction

```text
M_c mod 2 = (# internal C3 components) mod 2.                 (35)
```

This also explains why the abstract model above needed the deliberately
non-ambient declaration that `C3_+` was all-triangle-free: the actual defect
adjacency bridge forbids precisely that declaration.

At `q=8`, (35) closes the `mu=2` residue using only the four-cycle quotient
ledger.  Each sign shore has order eight and is a disjoint union of cycles
of order at least three, with no `C4` because the ambient graph is C4-free.
Its shape is therefore either `C8` or `C3 disjoint_union C5`.  The two shores
cannot have different shapes: if a `C8` shore faced a `C3+C5` shore, weighted
reciprocity for the `R` quotient would make the per-vertex `C8`--`C3` entry a
multiple of three.  Entry zero would force the `C8`--`C5` entry to be six,
exceeding the target size five; entry three would force the reverse
`C3`--`C8` entry to be eight, exceeding the six-regular row sum.  Therefore
the shores have the same shape and contain either zero or two triangles.
By (35), `M_c` is even.  This is a structural `q=8` corollary, not a census;
in fact the same quotient ledger closes the triangle parity uniformly.

Let the internal cycles be split between the two sign shores, and write
`n_a` for their orders.  Since `R` has degree `q-2` and only crosses the
shores, define its componentwise bipartite complement by

```text
z_ab = n_b - componentQuotientMatrix(R,H,a,b).
```

The target-size bound makes `z_ab` nonnegative, and the quotient identities
give

```text
sum_b z_ab = 2,                 n_a z_ab = n_b z_ba.     (36)
```

Thus every nonzero `z_ab` is one or two.  Regard these entries as weights on
the bipartite support graph of internal cycles.  A node of order three has
only the following possibilities, forced by weighted reciprocity:

* a weight-one edge can only meet another order-three node, again with
  reverse weight one;
* a weight-two edge meets either an order-three node with reverse weight two,
  or an order-six node with reverse weight one.

The row sum two now classifies every support component which contains an
order-three node.  Weight-one order-three nodes form a bipartite cycle, so
there are evenly many of them.  A weight-two `3--3` edge is an isolated pair.
Finally, a weight-two `3--6` edge makes the order-three endpoint a leaf and
leaves one unit at the order-six endpoint.  Reciprocity says that every
subsequent weight-one edge goes to another order-six node (reverse weight
one) or to an order-three leaf (reverse weight two).  Hence the finite
component is a path

```text
C3 -- C6 -- ... -- C6 -- C3,
```

again with exactly two order-three endpoints.  Therefore

```text
# internal C3 components = 0  (mod 2).                    (37)
```

Combining (35) and (37) gives the uniform signed-mode terminal

```text
full-support signed joint eigenline  ==>  M_c = 0 (mod 2). (38)
```

The modes `mu=-2,0` were closed by cycle-length divisibility; the `mu=2`
mode is closed by the defect-selector bridge and the two-regular complement
quotient above.  Consequently any odd collision residue is now confined to
the transport/no-full-support-signed-eigenline side of the dispatcher.  The
remaining task is no longer a signed-mode parity question.

## 9. Exact transport-side trace target

The same defect/exterior-pair adjacency bridge removes the cycle selector
even without a signed line.  Let `H=A_c` be the internal ambient two-factor,
let `R` be its exterior-pair graph, and let `t_3(H)` be the number of internal
`C3` components.  The cycle-sector dichotomy and the adjacency criterion give
an exact trichotomy.

* A `C3` is all-triangle, but none of its ambient edges belongs to `R`, since
  the third vertex is an internal common neighbor.
* On every longer all-triangle cycle, an ambient cycle edge is not a defect
  edge and has no internal common neighbor, so it is an `R`-edge.
* On every longer all-triangle-free cycle, an ambient cycle edge is a defect
  edge, so it is not an `R`-edge.

Consequently

```text
|E(H) cap E(R)|
  = total order of the longer all-triangle internal cycles. (39)
```

The component has even order `2q`.  Partitioning that order among the three
classes above and using (30) yields

```text
M_c = |E(H) cap E(R)| + t_3(H)  (mod 2).                (40)
```

Both terms have canonical trace forms:

```text
trace(H R) = 2 |E(H) cap E(R)|,
trace(H^3) = 6 t_3(H).                                  (41)
```

Thus the entire collision-parity problem, including the transport branch,
is equivalent to the single mixed trace congruence

```text
trace(H^3 + 3 H R) = 0  (mod 12).                       (42)
```

Here (40)--(42) retain the even-`q` triangle-free degree `0/2` and
cycle-propagation hypotheses used in (30); they are not assertions about an
arbitrary commuting pair of graphs.

The signed-mode argument above proves (42) whenever the exterior-pair bottom
line supplies a full-support `{+1,-1}` joint eigenvector.  In the other horn,
`B^T` transports every relevant nonprincipal internal mode to the exterior
adjacency block with negated eigenvalue.  Therefore (42), rather than another
cycle-by-cycle selector analysis, is the precise remaining transport-side
consumer.  A proof must use the transported exterior spectrum or the
simultaneous routing partition; commutation and ordinary quotient row sums
alone do not distinguish the two summands in (40).

There is also an exact graph interpretation of (42).  Let `B` be the
incidence block from `c` to its complement and form the spanning subgraph
which deletes all edges wholly outside `c`, with adjacency matrix

```text
S = [[H,B],[B^T,0]].
```

The exterior Gram identity is `B B^T=(q-2)I+R`.  Since `trace(H)=0`, a block
cube expansion gives

```text
trace(S^3)
  = trace(H^3) + 3 trace(H B B^T)
  = trace(H^3 + 3 H R).                                 (43)
```

Thus (42) is equivalently the assertion that this canonical spanning
subgraph has an even number of triangles.  Its degree sequence is especially
rigid: the `2q` vertices of `c` have degree `q`, every exterior vertex has
degree two, the exterior vertices form an independent set, and C4-freeness
is inherited from `G`.  Its triangles are exactly the internal `C3`s and the
subdivided exterior-pair edges which also lie in `H`, reproducing (40).
This packages the transport target as a pure parity theorem for a C4-free
even-degree split graph, while retaining the self-indexed origin of its
degree-two side.

Finally, (43) reconnects directly to the simultaneous owner colors.  Let
`F_d[c]` be the owner-`d` two-factor on `c`.  For `d != c`, every edge of
`F_d[c]` has its unique common neighbor in the exterior component `d`, so
the exterior-pair graph is the disjoint owner sum

```text
R = disjoint_union_(d != c) F_d[c].                      (44)
```

For the self color, (20) gives `F_c[c]=H^2-2I`.  Hence its intersection with
`H` consists exactly of the three edges of every internal `C3`, and

```text
|E(H) cap E(F_c[c])| = 3 t_3(H).                         (45)
```

Combining (40), (44), and (45) yields the fully colored form

```text
M_c = sum_d |E(H) cap E(F_d[c])|  (mod 2).               (46)
```

The factors `F_d[c]` edge-partition the selector complement of `D[c]`, so
(46) is also the parity of the internal ambient edges which are assigned an
owner color rather than lying in the triangle-free defect sector.  This is
algebraically equivalent to (42), but it is the form visible to (SRP): each
exterior color is built from a cross incidence block reused in every routing
partition, and the self color is the distinguished distance-two factor.
Thus the next simultaneous-routing statement can be phrased sharply as

```text
sum_d |E(A_c) cap E(F_d[c])| is even.                    (47)
```

Proving (47) from the coupled endpoint partitions closes the transport horn;
ordinary factor degrees or the uncolored owner partition merely restate it.

## 10. The first SRP contraction and its exact blind spot

For distinct components `c,e`, put

```text
p_ce = |E(A_c) cap E(F_e[c])|,
tau_ced = number of ambient triangles with one vertex in each of c,e,d.
```

Multiply (SRP) on the right by `R_ec=R_ce^T` and take the trace.  Cyclicity
of trace and the owner-factor interpretation give

```text
trace(A_c R_ce R_ec) = 2 p_ce,
trace(R_ce A_e R_ec) = 2 p_ec,
trace(R_cd R_de R_ec) = tau_ced.
```

Since every cross block has row sum two,
`trace(J R_ec)=4q`.  Therefore the contraction is the exact pair law

```text
2(p_ce + p_ec) + sum_(d != c,e) tau_ced = 4q.            (48)
```

In particular the three-component sum in (48) is even, and

```text
p_ce + p_ec
  = (1/2) sum_(d != c,e) tau_ced  (mod 2).               (49)
```

Summing (48) over all unordered component pairs shows that the total number
of three-distinct-component triangles is even and determines the parity of
the global exterior-owner mass.  But (48) has a precise blind spot: it sees
only the symmetric combinations `p_ce+p_ec`, whereas the target (47) is the
directed row sum

```text
p_cc + sum_(e != c) p_ce.
```

Thus this natural SRP trace contraction collapses to the already known
unoriented triangle inventory and cannot close a componentwise collision
parity.  A genuinely new consumer must retain the direction of the owner
transfer—equivalently, compare `p_ce` with `p_ec` rather than immediately
adding them.  Endpoint-marked rows such as (10)--(14), or a nonsymmetric
test matrix inserted before taking trace, are the remaining routes to that
information.

## 11. Rooted contraction retains the direction

The direction is recovered by keeping a diagonal coordinate instead of
taking the full trace.  Fix `x in c` and `e != c`, and define

```text
a_xe = number of H-neighbors of x whose H-edge is owned by e,
b_xe = 1 iff the two R_ce-neighbors of x are adjacent in A_e,
tau_xed = number of triangles (x,y,z), y in e, z in d.
```

Take the `(x,x)` entry after multiplying `SRP(c,e)` by `R_ec`.  The first
endpoint term is `a_xe`; the second is `2 b_xe`, because the two distinct
`e`-neighbors contribute both orders when they are adjacent; and a third
component contributes `tau_xed`.  The right side is the column sum two of
`R_ec`.  Hence

```text
a_xe + 2 b_xe + sum_(d != c,e) tau_xed = 2.             (50)
```

All terms are nonnegative integers, `a_xe in {0,1,2}`, and `b_xe in {0,1}`.
Thus (50) gives the exact rooted alternatives

```text
b_xe=1  ==>  a_xe=0 and all tau_xed=0;
b_xe=0  ==>  a_xe + sum_d tau_xed=2.                    (51)
```

In particular

```text
a_xe = 1  iff  exactly one three-component triangle
                 through x uses the color e.            (52)
```

Summing (50) over `x` recovers (48), so the new content is precisely its
rootwise location data.  Moreover

```text
sum_x a_xe = 2 p_ce,             sum_x b_xe = p_ec.      (53)
```

Equation (50) is therefore a directed refinement rather than a new scalar
count.  To extract `p_ce mod 2`, the next step must pair the `a_xe=1`
locations or control the `a_xe=2` locations along the internal cycles.  This
is exactly the endpoint-marked problem anticipated in (10)--(14), now with
an explicit two-unit budget at every root.

## 12. Owner-run normal form

For fixed distinct `c,e`, let

```text
K_ce = A_c cap F_e[c].
```

This is a subgraph of the internal two-factor, and its degree at `x` is
exactly `a_xe`.  Hence every connected component of `K_ce` is an isolated
vertex, a path, or a cycle.  The rooted budget refines this elementary
decomposition:

* a path endpoint (`deg K_ce = 1`) carries exactly one rooted
  three-component triangle involving the color `e`, by (52);
* a path or cycle interior (`deg K_ce = 2`) has `b_xe=0` and carries no such
  rooted triangle;
* an isolated vertex (`deg K_ce = 0`) either has `b_xe=1` and no such
  triangle, or has `b_xe=0` and exactly two of them.

Thus the three-component triangles mark precisely the boundaries and holes
of the color-`e` runs along the internal cycles.  Since

```text
p_ce = |E(K_ce)|,
```

its parity has the exact component form

```text
p_ce = number of odd-edge paths and odd cycles in K_ce  (mod 2). (54)
```

The handshake lemma pairs the path endpoints, but it does not determine the
parity of the distance between paired endpoints, and closed monochromatic
owner runs have no endpoints at all.  Therefore (50) alone still does not
prove (47).  The missing simultaneous input can now be stated without
matrices: the coupled routing partitions must pair the marked endpoints with
even run distance and pair the odd closed owner cycles, after summing over
all colors.  A countermodel to that statement would likewise be a definitive
failure certificate for the rooted-parity route.

## 13. The root--color state two-factor

Equation (50) couples the separate owner runs through a canonical state
graph.  Fix `c`.  Its active states are pairs

```text
(x,e),   x in c, e != c, b_xe=0.
```

Give these states two kinds of edges (allowing a multigraph if two rooted
triangles have the same pair of exterior colors).

* A horizontal edge joins `(x,e)` to `(y,e)` whenever the internal edge
  `xy` belongs to `K_ce=A_c cap F_e[c]`.
* A vertical edge joins `(x,e)` to `(x,d)` for every three-component
  triangle rooted at `x` with its other vertices in `e` and `d`.

At `(x,e)`, the horizontal degree is `a_xe` and the vertical degree is
`sum_d tau_xed`.  Since `b_xe=0`, equation (50) says their sum is exactly
two.  States with `b_xe=1` have both degrees zero and were omitted.  Hence

```text
the active root--color state graph is two-regular.          (55)
```

Its horizontal components before the vertical edges are precisely the owner
runs of Section 12.  A degree-one run endpoint receives one vertical edge;
a degree-zero hole receives two; and a degree-two run interior receives none.
Thus the vertical triangle edges perform the endpoint pairing which the
handshake lemma alone did not specify.

The edge census is exact:

```text
# horizontal edges = sum_(e != c) p_ce,
# vertical edges   = number of three-distinct-component triangles
                     having their c-vertex as root.        (56)
```

This is a genuine cross-color normal form, but two-regularity alone still
does not force horizontal parity.  An all-horizontal state cycle is exactly
a closed internal cycle monochromatically owned by one exterior color; more
generally, a mixed state cycle can wind an odd number of horizontal steps
around an odd internal cycle.  The final simultaneous invariant must rule
out or pair those odd-horizontal state cycles.  Equivalently, it must supply
a bipartition or a zero-holonomy label on the state graph which is not already
a function only of the completed-shift conjugacy class eliminated earlier.

## 14. Cohomological form of the missing invariant

Let `Gamma_c` be the active root--color state two-factor and mark its
horizontal edges by one and its vertical edges by zero in `F_2`.  Every
state cycle has even horizontal length exactly when this edge marking is a
coboundary.  Concretely, the sufficient-and-cyclewise-necessary datum is a
potential

```text
sigma : {(x,e) : active state} -> F_2
```

satisfying

```text
sigma(x,e) + sigma(y,e) = 1   on every horizontal owner edge,
sigma(x,e) + sigma(x,d) = 0   on every vertical triangle edge. (57)
```

If (57) exists, every component of `Gamma_c` has even horizontal edge count,
so (56) gives

```text
sum_(e != c) p_ce = 0  (mod 2).                          (58)
```

Together with the self-color term, this leaves only the already isolated
internal-`C3` contribution; in the signed quotient branch that contribution
is even by (37).  More generally, (57) is the exact exterior-owner part of
the desired parity.

Conversely, failure of (57) is witnessed by a state cycle with an odd number
of horizontal edges.  This gives a canonical, fiber-labelled obstruction
cycle rather than an arbitrary failed sign assignment.  It is materially
different from the eliminated completed-shift comparison: its vertices
remember both the root `x` and the actual owner color `e`, and its vertical
edges remember the locations of three-component triangles.  The transport
horn can therefore be sharpened to a dichotomy:

```text
root--color potential (57),
or a fiber-labelled odd-horizontal state cycle to transport. (59)
```

Proving the first alternative uniformly, or showing that the second creates
an impossible exterior eigenmode, would consume the simultaneous routing
data at the level that the scalar and conjugacy-class audits do not see.

## 15. Canonical port resolution of the state cycles

The state two-factor has additional ambient structure which an arbitrary
two-regular graph does not.  A state `(x,e)` has exactly two **ports**: the
two vertices of `e` adjacent to `x` through the cross block `R_ce`.

Every incident state edge canonically uses one of these ports.

* If the horizontal edge comes from an `e`-owned internal edge `xy`, its port
  is the unique common neighbor of `x,y` in `e`.
* If the vertical edge comes from a triangle with vertices in `c,e,d`, its
  port is the triangle's vertex in `e`.

No two distinct state edges incident to `(x,e)` can use the same port `z`.
Indeed, their other ambient endpoints would be two distinct common neighbors
of `x,z`, producing a C4.  At an active state there are two incident state
edges by (55) and exactly two ports, so

```text
incident state edges  <-->  the two ports of (x,e)       (bijectively). (60)
```

The transition behavior is also exact:

```text
horizontal transition: the port vertex is the same at both ends;
vertical transition:   the two port vertices are joined by an ambient edge.
                                                                  (61)
```

Thus every state cycle has a canonical port-resolved lift.  The cocycle
problem (57) is not merely a coloring of an abstract cycle: its holonomy is
generated by repeated changes to the other port at a state, interspersed
with identity transport across horizontal edges and ambient-adjacency
transport across vertical edges.  Any proof or countermodel for (57) should
preserve (60)--(61); a bare odd-horizontal two-factor without this port
resolution is not an admissible failure model.

## 16. Exact local odd-holonomy countermodel

The port resolution does **not** by itself force (57).  There is a completely
explicit even-`q` local countermodel at `q=10`, with two shores `c,e` of order
twenty.  Split each shore into blocks of orders nine and eleven.  On each
pair of corresponding blocks, let the cross incidence be the standard
bipartite cycle

```text
e_i -- c_i, c_(i+1).
```

Its two shore shadows are both the step-one cycle.  Choose the internal
two-factors by the following cyclic steps:

```text
order 9 block:   A_c step 1,   A_e step 3;
order 11 block:  A_c step 3,   A_e step 1.              (62)
```

The union of the two internal factors and the cross incidence is simple,
four-regular, and C4-free (direct common-neighbor check gives maximum one).
The endpoint owner intersections are

```text
p_ce=9,                         p_ec=11.                 (63)
```

There are no third-component/vertical edges in this local model.  On the
order-nine block the source state graph is an all-horizontal `C9`; on the
order-eleven block the reverse state graph is an all-horizontal `C11`.
Every state still has its two distinct ambient ports, and the rooted budgets
read `a=2,b=0` on the owned block and `a=0,b=1` on the opposite block.  Thus

```text
p_ce+p_ec=20=2q,
```

exactly as (48) requires when the three-color term is zero, while both
directed parities are odd and the potential (57) fails.

Scope is essential: `q=10` is not a binary power, and this is a single-pair
model, not a realization of all five coupled routing colors or of an ambient
square-order graph.  It proves only—and sharply—that C4-freeness, endpoint
orthogonality, rooted budgets, and canonical port resolution do not kill odd
holonomy.  The closing theorem must use the simultaneous reuse of the other
cross blocks (and, in the target campaign, the binary-power hypothesis); no
further invariant confined to one endpoint pair can suffice.

## 17. Full-SRP boundary transport of an odd closed run

The other routing colors do detect the local countermodel's missing datum.
Suppose an internal cycle `C` of odd order `n` is monochromatically owned by
an exterior component `e`.  Its owner ports form a set `Z subset e` of the
same order, and the `C--Z` part of `R_ce` is the bipartite incidence cycle.
It is an entire connected component of that cross two-factor: every vertex
of `C` and `Z` has both cross neighbors inside the block.  Therefore over
`F_2`, writing indicator vectors with the same symbols,

```text
R_ce Z = 0,                         R_ec C = 0.          (64)
```

Apply `SRP(c,e)` to `Z`.  The first endpoint layer vanishes by `R_ce Z=0`.
Now pair the resulting vector with `C`.  The second endpoint layer also
vanishes, since

```text
C^T R_ce A_e Z = (R_ec C)^T A_e Z = 0.
```

On the right, `J Z = n 1_c = 1_c` because `n` is odd, and pairing with `C`
again gives `n=1` in `F_2`.  Consequently the exterior routing colors obey
the exact simultaneous identity

```text
sum_(d != c,e) (R_dc C)^T (R_de Z) = 1  in F_2.         (65)
```

Both vectors in each summand are incidence-boundary vectors on the same
component `d`; each has even Hamming weight because every cross block has
column degree two.  Nevertheless (65) says that an odd number of third
colors have odd overlap, in particular

```text
there exists d != c,e with
  |supp(R_dc C) cap supp(R_de Z)| odd.                   (66)
```

This is the first obstruction in this audit which genuinely uses all the
simultaneous routing colors and is absent from the single-pair model of
Section 16.  An odd all-horizontal state cycle cannot remain isolated: it
exports an odd boundary-overlap mark to at least one third component.  The
next parity step is to show that these exported marks pair globally, or that
iterating the export creates a forbidden odd incidence cycle in the finite
component-color system.

## 18. Off-diagonal propagation between incidence components

The exported mark in (65) cannot terminate on the same cross-factor
component.  Fix `c,e`, and write the connected components of the bipartite
two-factor `R_ce` as paired shore sets

```text
(U_i subset c, V_i subset e),                       i in I.
```

Thus the `U_i` partition `c`, the `V_i` partition `e`, and the component
containing the odd owner run of Section 17 is `(U_0,V_0)=(C,Z)`.  For a third
component color `d`, define the binary component-interaction matrix

```text
t^d_ij := (R_dc U_i)^T (R_de V_j)  in F_2.            (67)
```

Every row and every column of `t^d` has even sum.  Indeed, the cross blocks
have degree two, so

```text
R_de 1_e = 0,                         R_dc 1_c = 0
```

over `F_2`; summing (67) over `j`, respectively over `i`, gives zero.  In
particular the diagonal mark exported by `(C,Z)` has the exact off-diagonal
resolution

```text
t^d_00 = sum_(j != 0) t^d_0j
       = sum_(i != 0) t^d_i0.                            (68)
```

Combining the first equality with (65) yields

```text
sum_(d != c,e) sum_(j != 0) t^d_0j = 1.                 (69)
```

Consequently an odd monochromatic owner run propagates, with odd total
parity, through third colors to *different* `R_ce` incidence components.
Pointwise, `t^d_0j` is the parity of vertices `y in d` whose two `c`-neighbors
straddle `U_0` and its complement and whose two `e`-neighbors straddle `V_j`
and its complement.  Thus (69) is a genuine component-switch statement, not
just a relabeling of the diagonal overlap in (65).

The remaining gap is now sharper.  The target `(U_j,V_j)` in (69) is an
arbitrary cross-factor component and need not itself be a closed
monochromatic owner run.  A terminal parity argument must either pair the
switches at such non-owner components or prove that following component
switches eventually re-enters the owner-run locus with forbidden odd
holonomy.

Equivalently, for each fixed `d`, regard `t^d` as the adjacency matrix of a
bipartite graph on two labeled copies of the `R_ce` component set.  The
row/column laws say that this graph is Eulerian.  Hence every nonzero
diagonal export edge lies on an even alternating cycle, and after deleting
that edge there is an odd-length replacement path from the source copy of
the owner component to its target copy.  Its first and last edges are
necessarily off-diagonal component switches, although intermediate edges
may again be diagonal.  What is still missing is a rule that transports
ownership (rather than only incidence) along this forced path.

## 19. Exact aggregate interaction and the ownership blind spot

In fact the interaction matrices have a complete aggregate description.
For arbitrary incidence components `(U_i,V_i)` and `(U_j,V_j)` of `R_ce`,
their indicator vectors satisfy

```text
R_ec U_i = 0,                         R_ce V_j = 0       (70)
```

over `F_2`, because each bipartite component is a cycle.  Pair `SRP(c,e)`
on the left with `U_i` and on the right with `V_j`.  Equation (70) kills
both endpoint terms, leaving

```text
sum_(d != c,e) t^d_ij = |U_i| |V_j|  (mod 2).           (71)
```

The two shores of each incidence component have equal size.  If

```text
s_i := |U_i| mod 2 = |V_i| mod 2,
T_ij := sum_(d != c,e) t^d_ij,
```

then (71) is the exact rank-one law

```text
T = s s^T  over F_2.                                    (72)
```

Since the shore order `2q` is even, `sum_i s_i=0`: every cross two-factor
has an even number of odd half-length components.  For an odd owner component
`i=0`, (72) says more precisely

```text
sum_(d != c,e) t^d_0j = s_j.                            (73)
```

Thus the aggregate third-color switch parity from the owner run is one to
every other odd incidence component and zero to every even incidence
component.  Summing (73) over `j != 0` recovers (69), because an even total
number of odd components leaves an odd number besides `0`.

This both strengthens and limits Sections 17--18.  The simultaneous routing
partition does force component switches, but after summing the routing color
their parity is determined entirely by the cycle-length parities of `R_ce`;
ownership has disappeared.  Therefore iterating the uncolored matrices
`t^d` cannot by itself prove that an odd owner run reaches another owner run.
A closing argument must retain either the individual third color `d` together
with owner data at its switch vertices, or a second marked structure not
annihilated in the contraction (71).

## 20. Affine freedom of the color-resolved parity matrices

Retaining the third-color label `d` without any further geometric datum is
still not enough at the binary-matrix level.  If `R_ce` has `k` incidence
components, let

```text
E_k = { X in Mat_(k x k)(F_2) : X 1 = 0 and 1^T X = 0 }.
```

The last row and column are determined by the leading `(k-1) x (k-1)`
block, so

```text
dim_F2 E_k = (k-1)^2.                                  (74)
```

Section 18 says `t^d in E_k` for every third color.  Conversely, the only
linear constraints established so far on the color-resolved family are

```text
t^d in E_k,                 sum_d t^d = s s^T.          (75)
```

The target `s s^T` belongs to `E_k` because `sum_i s_i=0`.  Hence if there
are `r >= 1` third colors, the abstract solution set of (75) is a nonempty affine
space of dimension

```text
(r-1)(k-1)^2:                                          (76)
```

choose any `r-1` matrices in `E_k`, and the last is forced.  In particular,
the full aggregate may be placed in one color and zero in all others, or
redistributed by adding an arbitrary Eulerian matrix to two colors.

This is an algebraic freedom statement, not a claim that every such tuple is
realizable by an ambient graph.  It does prove that row/column parity,
component oddness, and the color labels alone cannot yield an additional
linear contradiction.  The next invariant must use a realizability
constraint tying `t^d_ij` to the owner factors or internal cycle geometry in
component `d`; otherwise it factors through the affine system (75) and sees
only the already exhausted rank-one aggregate.

## 21. The first owner-sensitive marked contraction

The lowest-degree refinement which sees geometry inside a third routing
component inserts its internal two-factor.  Retain the odd closed owner run
`(C,Z)=(U_0,V_0)` and, for `d != c,e`, define

```text
h^d_0j := (R_dc C)^T A_d (R_de V_j)  in F_2.            (77)
```

This is the parity of internal `A_d` edges between the two incidence-boundary
vectors (with an edge in their intersection counted twice and hence zero).
Unlike `t^d_0j`, it depends on the marked cycle geometry inside component
`d`.

There is an exact four-color transfer law.  Apply `SRP(c,d)` to the vector
`R_de V_j` and pair on the left with `C`.  Since the owner run is an entire
internal `A_c` cycle,

```text
A_c C = 0.
```

Thus the `c`-endpoint term vanishes.  The right side also vanishes because
`R_de V_j` has even weight.  In the exterior sum, the `f=e` term vanishes by
`C^T R_ce=0`.  What remains is

```text
h^d_0j
  = sum_(f != c,d,e) C^T R_cf R_fd R_de V_j  in F_2.    (78)
```

The same partition argument as before gives even margins:

```text
sum_j h^d_0j = 0,                                      (79)
```

because `sum_j R_de V_j = R_de 1_e = 0`.  But (78) no
longer collapses to the rank-one law (72): it retains both the marked
internal step `A_d` and, on the other side, the individual fourth routing
color `f`.  Combinatorially, its right side counts parity of length-three
routes

```text
C -- f -- d -- V_j
```

with the middle `d--V_j` leg constrained by the original `e` incidence.
This is therefore the first contraction in the present chain which can in
principle transport ownership information.  It is not yet a terminal: one
must relate the four-color route parity in (78) back to owner-factor edges
or triangles in `d`.  Equation (78) fixes the exact object that such a
relation has to control.

## 22. Four-color routing curvature

Fix a target incidence component `V_j`.  For distinct colors `d,f`, both
different from `c,e`, write the ordered marked path parity

```text
ell^j_fd := C^T R_cf R_fd R_de V_j.                    (80)
```

Equation (78) says that `h^d_0j` is the `d`-column sum of these ordered
four-color paths:

```text
h^d_0j = sum_(f != c,d,e) ell^j_fd.                     (81)
```

Therefore, after summing over the third component and grouping the two
orders of every unordered pair,

```text
sum_(d != c,e) h^d_0j
  = sum_({d,f} subset colors minus {c,e})
      (ell^j_fd + ell^j_df).                            (82)
```

The summand in (82) is the exact binary routing curvature of the pair
`{d,f}` relative to `(C,V_j)`.  To see its local meaning, put

```text
u_f = R_fc C,        v_f = R_fe V_j.
```

Then

```text
ell^j_fd = u_f^T R_fd v_d,
ell^j_df = u_d^T R_df v_f.                             (83)
```

For an edge `a--y` of the cross two-factor between `f` and `d`, the first
orientation marks it when `a` has odd incidence into `C` and `y` has odd
incidence into `V_j`; the second exchanges the roles of `d` and `f`.

C4-freeness makes the two orientations pointwise support-disjoint after the
endpoints `x in C`, `z in V_j` are fixed.  Indeed, simultaneous paths

```text
x -- a(f) -- y(d) -- z,
x -- y(d) -- a(f) -- z
```

would create the four-cycle `x--a--z--y--x`.  But support-disjointness does
not imply equality of their total parities.  Thus (82) isolates the precise
directed datum which survives the symmetric cancellations: closing the
marked route requires proving that the total curvature is even, or pairing
its oriented paths by an owner-sensitive involution.  Ordinary row sums and
the rank-one incidence law (72) do not address this orientation imbalance.

## 23. The ambient cubic identity is tautological on curvature

It is natural to hope that the global cubic polynomial forces the total in
(82) to vanish.  It does not.  Let `A` now denote the full ambient adjacency
matrix and `D` the defect adjacency.  From

```text
A^2 = (q-1) I + J - D
```

and even `q`, one has over `F_2`

```text
A^3 = A + A D.                                          (84)
```

Pair (84) with `C` on the left and `V_j` on the right.  The `A` term is zero
because `R_ce V_j=0`; the `AD` term is zero because `D` is block diagonal
and `C^T R_ce=0`.  Hence

```text
C^T A^3 V_j = 0.                                       (85)
```

Expand the left side by the component colors of the two intermediate
vertices.  Any route whose first intermediate color is `c` vanishes by
`A_c C=0`; first color `e` vanishes by `C^T R_ce=0`; and second color `c`
vanishes by `R_ce V_j=0`.  The surviving terms are

```text
sum_(d != c,e) h^d_0j
+ sum_(d,f != c,e, d != f) ell^j_df
+ E_j,                                                  (86)
```

where the only remaining endpoint layer is

```text
E_j := sum_(d != c,e) C^T R_cd R_de A_e V_j.
```

But `E_j=0`: substitute the third-color sum from `SRP(c,e)`.  The `J` term
has even mass after `A_e V_j`, the `c`-endpoint term is killed by `A_c C=0`,
and the `e`-endpoint term is killed by `C^T R_ce=0`.

Thus (85)--(86) say that the marked sum equals the ordered curvature sum.
This is already exactly the sum over `d` of (78).  Equivalently the cubic
identity reduces to two copies of the same binary scalar and hence to
`2x=0`.  Therefore no unmarked use of the ambient cubic polynomial can force
the routing curvature to vanish.  A successful next contraction must retain
an owner-color mark, a distinguished internal edge, or higher information
before the component-color sums are taken.

## 24. Root-marked identity and the two endpoint coboundaries

The information discarded in (78) can be located exactly by retaining one
root of the owner cycle.  Write the odd cycle as

```text
C = (x_i)_(i mod n)
```

and label its owner ports in `Z` so that the two `e`-neighbors of `x_i` are
`z_(i-1),z_i`.  Fix `d != c,e` and a target incidence component `V_j`.  Put

```text
r_i^d := e_(x_i)^T R_cd R_de V_j,
h_i^d := (R_dc e_(x_i))^T A_d (R_de V_j),
lambda_i^(f,d) := e_(x_i)^T R_cf R_fd R_de V_j.         (87)
```

Apply `SRP(c,d)` to `R_de V_j`, but now pair with the single root `x_i`
rather than with all of `C`.  The right side still has even mass.  Separating
the exterior color `f=e` gives

```text
h_i^d
  = r_(i-1)^d + r_(i+1)^d
    + e_(x_i)^T R_ce R_ed R_de V_j
    + sum_(f != c,d,e) lambda_i^(f,d).                  (88)
```

The middle endpoint term is already owner-colored.  The individual cross
Gram identity is

```text
R_ed R_de = 2 I + F_d[e]
```

over the integers, where `F_d[e]` is the owner-`d` factor on component `e`.
Therefore modulo two, if

```text
w^d := F_d[e] V_j,
```

then the port term in (88) is exactly

```text
e_(x_i)^T R_ce R_ed R_de V_j
  = w^d(z_(i-1)) + w^d(z_i).                            (89)
```

Thus both endpoint contributions in the root-marked identity are explicit
cycle coboundaries:

```text
i |-> r_(i-1)^d + r_(i+1)^d,
i |-> w^d(z_(i-1)) + w^d(z_i).                          (90)
```

For the first sequence, assign `r_i^d+r_(i+1)^d` to the cycle edge
`x_i x_(i+1)`; its vertex divergence is
`r_(i-1)^d+r_(i+1)^d`.  The second is the ordinary adjacent difference of
the port labels `w^d(z_i)`.

Their sums around `C` vanish, the first because every `r_i^d` occurs twice
and the second by telescoping around the port cycle.  Summing (88) therefore
recovers (78), with no unexplained cancellation.

This exposes the correct owner-sensitive interface.  The curvature row

```text
i |-> h_i^d + sum_f lambda_i^(f,d)
```

is the sum of an internal-cycle coboundary and an owner-`d` port coboundary.
To close the original state potential (57), one must make these rootwise
potentials compatible as `d` and the target incidence component vary.  A
scalar sum cannot see that compatibility, but (88)--(90) retain exactly the
port label and owner factor needed to formulate it.

## 25. Canonical primitive of the marked curvature row

The two coboundaries in (90) combine without solving a linear system.  For
fixed `d,j`, define an edge-indexed binary potential around the owner cycle by

```text
phi_i^(d,j)
  := r_i^d + r_(i+1)^d + w^d(z_i),
w^d = F_d[e] V_j.                                      (91)
```

Let the rootwise residual be

```text
kappa_i^(d,j)
  := h_i^d + sum_(f != c,d,e) lambda_i^(f,d).
```

Then (88)--(90) give the exact adjacent-difference law

```text
kappa_i^(d,j) = phi_(i-1)^(d,j) + phi_i^(d,j).          (92)
```

Indeed the two copies of `r_i^d` cancel when the consecutive values of
`phi` are added, leaving precisely
`r_(i-1)^d+r_(i+1)^d+w^d(z_(i-1))+w^d(z_i)`.

Thus every marked curvature row has a canonical primitive, not merely even
total parity.  As usual for the incidence derivative on a connected cycle,
an abstract primitive of `kappa` is unique up to adding the constant-one
function; (91) chooses a distinguished representative from the routing and
owner data.

This choice is already compatible across the target incidence components.
Since the `V_j` partition `e`, over `F_2`

```text
sum_j r_i^d
  = e_(x_i)^T R_cd R_de 1_e = 0,
sum_j w^d
  = F_d[e] 1_e = 0,                                    (93)
```

using degree two of `R_de` and of the owner factor.  Consequently

```text
sum_j phi_i^(d,j) = 0       for every i,d.              (94)
```

Equations (91)--(94) remove the target-component ambiguity: the marked
potentials are canonically normalized and have zero target sum.  The
remaining compatibility problem is only across the routing color `d` (and,
ultimately, across the choice of endpoint pair).  This is strictly smaller
than the unconstrained state-potential problem in (57).

## 26. Routing-color aggregate as one marked owner operator

The remaining compatibility across `d` also has an exact closed form.  Let

```text
s_j := |V_j| mod 2,
g^j := A_e V_j.
```

Summing the definition of `r_i^d` over all third colors and using
`SRP(c,e)` gives

```text
sum_(d != c,e) r_i^d
  = s_j + (R_ce A_e V_j)(x_i)
  = s_j + g^j(z_(i-1)) + g^j(z_i).                     (95)
```

Let `H_e` denote the full selector complement on `e`, equivalently the
disjoint sum of all owner factors `F_a[e]`.  Over `F_2`,

```text
sum_(d != c,e) F_d[e] V_j
  = (H_e + F_c[e] + F_e[e]) V_j
  = (H_e + A_e^2) V_j.                                 (96)
```

For the last equality, `F_e[e]=A_e^2-2I` and `F_c[e]V_j=0`; the latter holds
because `V_j` is a whole cycle component of the cross-shadow owner factor
`F_c[e]`.

Now sum the canonical primitive (91) over `d`.  The two copies of `s_j`
cancel, and the consecutive port evaluations in (95) reduce to

```text
g^j(z_(i-1)) + g^j(z_(i+1))
  = (F_c[e] A_e V_j)(z_i).
```

Consequently

```text
sum_(d != c,e) phi_i^(d,j)
  = ((F_c[e] A_e + H_e + A_e^2) V_j)(z_i).             (97)
```

Thus all routing-color compatibility of the canonical primitives is
concentrated in the single marked operator

```text
Theta_(c,e) := F_c[e] A_e + H_e + A_e^2                (98)
```

evaluated on incidence-component indicators and then restricted to the
owner-port cycle `Z`.  A sufficient next statement is now concrete:
`Theta_(c,e) V_j` should vanish, or at least be constant, on `Z` in a way
compatible across endpoint pairs.  Establishing that requires a genuine
relation between the distinguished cross-shadow factor `F_c[e]`, the
internal cycle `A_e`, and the full owner sum `H_e`; none of the scalar SRP
contractions supplies it automatically.

## 27. Alternating incidence-component compression of `Theta`

Although (98) does not yet imply pointwise constancy on the port cycle, its
compression to the `R_ce` incidence components is rigid.  Put

```text
P := F_c[e],                    B := A_e,
Theta = P B + H_e + B^2.
```

Every incidence-component indicator lies in the binary kernel of `P`:

```text
P V_i = 0.                                             (99)
```

Indeed `P` is the cycle shadow of `R_ce`, and `V_i` is a whole component of
that shadow.  Define the compressed matrix

```text
theta_ij := V_i^T Theta V_j.                           (100)
```

The marked noncommuting term disappears after left compression:

```text
V_i^T P B V_j = (P V_i)^T B V_j = 0.
```

Hence, for supports at distinct actual-route occurrences,

```text
theta_ij = V_i^T (H_e + B^2) V_j.                     (101)
```

The matrix `H_e+B^2` is symmetric and has zero diagonal over `F_2`:
`H_e` is a simple adjacency matrix, while every diagonal entry of `B^2` is
the internal degree two.  Therefore `theta` is alternating,

```text
theta_ij = theta_ji,                 theta_ii = 0.      (102)
```

It also has zero row sums.  The owner sum `H_e` has even degree `q`, and
`B^2 1 = 4 1`, so `(H_e+B^2)1=0`; since the `V_j` partition `e`,

```text
sum_j theta_ij = 0.                                    (103)
```

Thus the total values of the routing-color aggregate potential on the
incidence components form the adjacency matrix of an Eulerian simple graph
on those components.  In particular, for the owner-port component `Z=V_0`,

```text
sum_(z in Z) (Theta V_0)(z) = 0,
sum_j sum_(z in Z) (Theta V_j)(z) = 0.                  (104)
```

This is weaker than pointwise constancy: an even-weight nonconstant vector
on `Z` is still allowed.  It identifies the remaining gap precisely as a
within-component fluctuation invisible to every component-indicator test.
Any proof of the proposed constancy target after (98) must control that
fluctuation, not merely another quotient parity.

## 28. Exact detector for the within-component fluctuation

On the odd owner-port component `Z`, the shadow factor `P=F_c[e]` is an odd
cycle adjacency.  Its binary kernel on that component consists exactly of
the constant functions: `P u=0` says `u_(i-1)=u_(i+1)`, and odd cyclic order
forces all coordinates equal.  Since the `P`-neighbors of a vertex of `Z`
remain in `Z`, the proposed constancy after (98) is equivalent to

```text
(P Theta V_j)|_Z = 0.                                  (105)
```

This detector removes the full owner sum.  Each owner factor commutes with
the defect adjacency and hence with its selector complement `H_e`; in
particular

```text
P H_e = H_e P.
```

Using `P V_j=0` and `Theta=P B+H_e+B^2`, where `B=A_e`, gives

```text
P Theta V_j
  = (P^2 B + P H_e + P B^2) V_j
  = P (P+B) B V_j.                                     (106)
```

Therefore the routing-color aggregate potential is constant on the owner
ports exactly when

```text
(P (P+B) B V_j)|_Z = 0.                                (107)
```

The remaining obstruction is now a distinguished endpoint cubic, but unlike
the ambient cubic of Section 23 it keeps both the cross-shadow cycle `P` and
the internal cycle `B` marked.  Equation (107) is the sharp next theorem
target.  Proving it requires an interaction between these two two-factors;
their separate commutation with `H_e` is enough to remove the background
owner sum but not enough by itself to annihilate `P(P+B)B`.

## 29. Exact local failure of the marked cubic

The target (107) is not forced by the two-shore C4 geometry alone.  There is
an explicit local model at `q=6`, with two shores `c,e` of order twelve.
Split both shores into blocks of orders five and seven.  On corresponding
blocks use the standard bipartite incidence cycles

```text
e_i -- c_i, c_(i+1),
```

so the two shore shadows are `P=C5 disjoint-union C7`.  Take the source
internal factor to be the same `C5 disjoint-union C7`; hence both source
cycles are closed runs monochromatically owned by `e`.  On the target shore
take the Hamilton cycle

```text
(5,8,3,10,0,6,2,11,7,1,9,4).                          (108)
```

The resulting 24-vertex two-shore graph is simple, four-regular, and
C4-free: direct multiplication gives maximum off-diagonal common-neighbor
count one.  Let `V_0` be the five-point port component.  Direct binary
calculation gives

```text
(P (P+A_e) A_e V_0)|_(V_0) = (0,1,0,0,1),              (109)
```

so the marked cubic does not vanish and `Theta V_0` is not forced constant
by the local endpoint geometry.

The reproducer `verify_local_marked_cubic_failure_q6.py` checks regularity,
C4-freeness, both cross shadows, the owner-run identification, and (109).
Scope is essential: `q=6` is not a binary power, and this is a single-pair
model rather than a realization of all `q/2=3` simultaneous component
colors and their coupled SRP partitions.  Thus (109) does not refute the
target campaign.  It proves that the next theorem must use simultaneous
reuse and/or the binary-power input; no argument confined to the marked
two-shore factors `P,A_e` can establish (107).

## 30. The local failure is blocked by the first SRP extension

The model of Section 29 does not extend even to the single missing routing
color at `q=6`.  Its endpoint residual is

```text
Q := J - A_c R_ce - R_ce A_e.                          (110)
```

The two endpoint products are zero-one and support-disjoint, and `Q` is a
zero-one matrix with every row and column sum four.  Since `q/2=3`, a
three-component SRP extension would have exactly one third layer and would
require

```text
Q = R_cd R_de                                           (111)
```

for two degree-two incidence blocks.

Every support edge of a product in (111) lies in a `K_(2,2)` support
rectangle: if a path from `x in c` to `z in e` uses an intermediate vertex
`y in d`, the two `c`-neighbors and two `e`-neighbors of `y` contribute the
whole rectangle.  In the explicit residual (110), however, the edge `(0,3)`
lies in no `K_(2,2)`.  Hence (111) is impossible before any global reuse
condition is imposed.

The reproducer now verifies this obstruction by enumerating all residual
rectangles.  This sharpens the lesson of (109): endpoint C4-freeness and
owner ports permit nonzero marked cubic, but the first SRP factorability
condition already detects that particular failure.  The next natural
q-generic theorem target is therefore stronger and narrower than (107):

```text
does an SRP-factorable endpoint residual force
  (P(P+A_e)A_e V_j)|_Z = 0 ?                            (112)
```

If yes, no cross-pair simultaneous comparison is needed for the all-horizontal
owner-run case; if no, a countermodel must preserve an actual rectangle
factorization rather than only the two endpoint layers.

## 31. Pairwise SRP factorability still does not kill the cubic

The question (112) has a negative answer.  Keep the same `C5 disjoint-union
C7` cross incidence and source internal factor as in Section 29, but replace
the target internal cycle by

```text
(11,3,7,10,1,5,9,4,6,2,8,0).                          (113)
```

The two-shore graph is again simple, four-regular, and C4-free.  This time
the residual `Q` in (110) has an exact factorization through a twelve-point
third shore.  Its twelve intermediate vertices use the following source and
target neighbor pairs:

```text
(01|79), (08|36), (17|4,11), (24|5,10),
(26|09), (35|8,10), (37|15), (4,11|27),
(59|03), (68|1,11), (9,10|26), (10,11|48).             (114)
```

Every source and target vertex occurs in exactly two pairs, and the twelve
`K_(2,2)` rectangles in (114) partition all 48 residual edges.  Thus the
associated zero-one blocks have row and column degree two and satisfy

```text
Q = R_cd R_de
```

exactly: the full `SRP(c,e)` equation holds for this endpoint pair.

Nevertheless, on the five-point owner-port component,

```text
(P(P+A_e)A_e V_0)|_(V_0) = (1,0,1,1,1),               (115)
```

so the marked cubic remains nonzero.  The reproducer
`verify_local_marked_cubic_srp_factorable_q6.py` checks C4-freeness, all
degree conditions, the exact matrix factorization, and (115).

Scope again matters.  The factor blocks in (114) have not been equipped with
an internal third-shore factor `A_d`, nor required to satisfy the two other
endpoint equations `SRP(c,d)` and `SRP(d,e)`; and `q=6` is nonbinary.  Hence
this is a pairwise-SRP countermodel, not a simultaneous three-component
countermodel.  It proves that rectangle factorability of one residual is
still insufficient.  The next admissible theorem must use reuse of
`R_cd,R_de` in the other SRP equations (or an essentially binary-power
constraint); the proposed shortcut (112) is closed.

## 32. The factorization is not ambient-C4-compatible

The rectangle partition (114) is an exact matrix factorization, but it cannot
serve as the cross blocks of a third component in an ambient C4-free graph.
A rectangle with source pair `{x,x'}` creates a new common neighbor of
`x,x'` in `d`; therefore that pair must have codegree zero in the existing
two-shore graph.  The same condition holds for its target pair `{z,z'}`.

Filter all `K_(2,2)` rectangles in the residual (110) by these two necessary
codegree-zero conditions.  Only ten compatible rectangles remain, and the
residual edge `(0,7)` lies in none of them.  Consequently **no** rectangle
partition of this residual— not merely the displayed choice (114)—can be
extended to C4-free cross blocks `R_cd,R_de`.

The reproducer now checks the uncovered edge after enumerating every
ambient-compatible rectangle.  This identifies the next exact boundary:

```text
an endpoint residual factorization into K_(2,2) fibers
whose source and target pairs all have prior codegree zero.             (116)
```

Condition (116) is forced before an internal factor `A_d` or the other two
SRP equations are considered.  The Section-31 example proves that abstract
matrix factorization is too weak, while this section shows precisely which
ambient realizability condition rejects it.  A further countermodel to the
marked cubic must preserve (116); otherwise the plausible next theorem is
that (116), together with the odd owner run, already forces (107).

## 33. Radius-two exclusion and the third-owner packing bound

Condition (116) has a uniform source-side consequence.  For every third
color `d`, let

```text
F_d[c] = (R_cd R_dc) off the diagonal
```

be its owner factor on `c`.  These factors are edge-disjoint and two-regular.
Their union over `d != c,e`, denoted `L_ce`, is therefore `(q-4)`-regular,
because there are `q/2-2` third colors:

```text
L_ce := disjoint_union_(d != c,e) F_d[c],
deg(L_ce) = q-4.                                        (117)
```

Let `C=(x_i)` be an odd internal cycle monochromatically owned by `e`, of
order `n`.  Such a cycle has `n >= 5`: order four is ambiently forbidden,
and at order three each internal edge would have both the third cycle vertex
and its owner port as common neighbors.  Within `C`, consecutive vertices
already share their owner port in `e`, while vertices at cyclic distance two
already share their middle internal neighbor in `c`.  Ambient C4-freeness
therefore forces

```text
x_i x_j in E(L_ce)  ==>  cyclicDistance(i,j) >= 3.      (118)
```

Equivalently, the third-owner graph induced on `C` is a subgraph of the
complement of the square of the `n`-cycle.  Hence

```text
e_(L_ce)(C) <= n(n-5)/2.                               (119)
```

If `b_ce(C)` is the number of `L_ce` edges leaving `C`, degree summation and
(119) give the exact packing consequence

```text
b_ce(C)
  = n(q-4) - 2 e_(L_ce)(C)
  >= n(q-n+1).                                         (120)
```

The lower bound is informative for `n <= q`; for `n=5`, every one of the
`5(q-4)` third-owner incidences must leave the cycle.  Moreover each
individual two-factor `F_d[c]` has an even cut across `C`, so `b_ce(C)` is a
sum of even colorwise contributions.

This reformulates ambient-compatible rectangle factorization as a constrained
owner-factor packing problem.  A countermodel preserving (116) must supply
`q-4` distinct third-owner partners at every cycle vertex while avoiding its
four radius-two neighbors, and must realize the resulting large boundary in
even color classes.  These restrictions are absent from the abstract
factorization of Section 31.

## 34. Clean third-color abundance

The aggregate packing bound admits a useful colorwise refinement.  For each
third color `d`, let

```text
a_d(C) := |E(F_d[c][C])|,
b_d(C) := |delta_(F_d[c])(C)|.
```

Since `F_d[c]` is two-regular,

```text
b_d(C) = 2n - 2 a_d(C),                                (121)
```

and `b_d(C)` is even.  Summing over third colors and using (119) gives

```text
sum_(d != c,e) a_d(C) <= n(n-5)/2.                     (122)
```

Call `d` **clean for `C`** when `a_d(C)=0`, equivalently when all `2n`
owner incidences of `F_d[c]` at vertices of `C` leave the cycle.  Every
nonclean color consumes at least one of the internal-edge slots counted in
(122).  As there are `(q-4)/2` third colors,

```text
# {d != c,e : d clean for C}
  >= (q-4)/2 - n(n-5)/2.                               (123)
```

The right side may be replaced by zero when negative.  Two small-cycle
specializations are especially rigid:

```text
n=5: every third color is clean and b_d(C)=10;
n=7: at most seven third colors are nonclean.           (124)
```

Thus for every fixed odd owner-cycle length, all but `O(n^2)` routing colors
have a completely external owner factor on that cycle, uniformly as the
binary power `q` grows.  A simultaneous argument can now choose a clean
third color whenever `q-4 > n(n-5)`.  This is stronger than the uncolored
boundary lower bound: it supplies an individual reused block `R_cd` whose
shadow has no chord at all inside `C`, which can be inserted into the other
endpoint partitions.

## 35. Clean colors give disjoint two-point lifts

Fix a third color `d` which is clean for `C`.  Let

```text
Y_d := supp(R_dc C) subset d,
Y_d(x) := N_G(x) cap d,                  x in C.
```

Every fiber `Y_d(x)` has size two.  Cleanliness says that no vertex of `d`
has both of its `c`-neighbors in `C`, since such a vertex would index an
edge of `F_d[c][C]`.  Therefore the fibers are pairwise disjoint and

```text
Y_d = disjoint_union_(x in C) Y_d(x),
|Y_d| = 2n.                                              (125)
```

Thus a clean owner factor is not merely chord-free on `C`: the reused cross
block `R_cd` restricts to a genuine two-point lift of the cycle roots into
component `d`.

The rooted SRP budget now constrains the internal geometry of that lift.
For `x in C`, both internal edges incident to `x` are owned by `e`, so
`a_xd=0`.  Recall that `b_xd=1` exactly when the two vertices of `Y_d(x)`
are adjacent in `A_d`.  Equations (50)--(51) specialize to the dichotomy

```text
Y_d(x) in E(A_d)
  ==> no three-component triangle through x uses d;

Y_d(x) notin E(A_d)
  ==> exactly two three-component triangles through x use d.            (126)
```

If `m_d(C)` is the number of lifted fibers which are internal `A_d` edges,
then summing (126) over the roots gives

```text
sum_(x in C) sum_(f != c,d) tau_xdf
  = 2 (n - m_d(C)).                                     (127)
```

Equations (125)--(127) are the first direct use of a clean reused block in
another endpoint component.  For a five-cycle every third color supplies
such a disjoint ten-point lift.  Any simultaneous countermodel must then,
for every one of those colors, choose fiber edges in `A_d` or route the
remaining fibers through exactly two further colors, with no collisions
allowed by C4-freeness.

## 36. Internal exclusions on a clean lift

The internal two-factor `A_d` cannot be arbitrary on the lifted set `Y_d`.
First, if

```text
y in Y_d(x_i),          y' in Y_d(x_(i+1)),
```

then `yy'` is not an `A_d` edge: otherwise

```text
x_i -- y -- y' -- x_(i+1) -- x_i
```

is an ambient four-cycle.  Hence

```text
E(A_d) cap (Y_d(x_i) times Y_d(x_(i+1))) = empty.       (128)
```

Second, the two vertices `y_0,y_1` of one fiber already have the common
neighbor `x_i`.  They therefore cannot have a common `A_d` neighbor:

```text
N_(A_d)(y_0) cap N_(A_d)(y_1) = empty.                 (129)
```

In particular, if the fiber itself is an `A_d` edge (the first branch of
(126)), that edge cannot lie in an internal triangle of `A_d`; its cycle
component has order at least five.

Thus a clean color replaces each root by a pair subject to two simultaneous
rules: consecutive root-pairs are anticomplete in `A_d`, and the two points
inside each pair have disjoint internal neighbor sets.  For `n=5`, every
third component must realize ten lifted points with these constraints, in
addition to the edge-or-two-triangles alternative (126).  This is the exact
finite local object on which the next simultaneous counting argument can
operate.

## 37. Rootwise vertical two-factor for an owned five-cycle

Now specialize to `n=5`.  By (124), every third color is clean, so every
root `x in C` has a lifted pair `Y_d(x)` for every `d != c,e`.  Define the
active third-color set

```text
N_x := {d != c,e : Y_d(x) notin E(A_d)}.                (130)
```

For `d in N_x`, (126) gives exactly two three-component triangles through
`x` using `d`; for `d` outside `N_x`, it gives none.  No such triangle uses
the owner color `e`, because the state `(x,e)` already has horizontal degree
two on the closed owner run and hence vertical degree zero in (55).

Make a multigraph on `N_x` by joining `d,f` once for every triangle with
vertices in `c,d,f` rooted at `x`.  Each vertex has degree exactly two, so

```text
the rooted triangle multigraph on N_x is two-regular.    (131)
```

Parallel edges are allowed, corresponding to two triangles using the same
unordered color pair.  Loops are not, since a three-component triangle has
distinct exterior colors.  Consequently

```text
|N_x| != 1.                                             (132)
```

Equivalently, at every root of an exterior-owned five-cycle, the number of
third components whose lifted fiber is a nonedge is either zero or at least
two.  In the first binary calibration `q=8` there are exactly two third
colors, so (132) says their lifted pairs agree pointwise: both are internal
edges or both are nonedges joined by the two parallel rooted triangles.
This last sentence is a q-generic specialization only and does not authorize
an order-64 computation under the standing park.

Summing degrees in (131) also identifies the triangle census:

```text
# {three-component triangles rooted at x using third colors}
  = |N_x|.                                              (133)
```

Thus the remaining five-cycle problem is a simultaneous five-row system of
small two-regular color multigraphs, coupled through the internal factors
`A_d` and the disjoint lifted fibers.  This structure is absent from every
single-pair countermodel above.

## 38. Clean-or-long dichotomy for odd owner runs

The positivity threshold in (123) gives a uniform structural split.  If an
odd exterior-owned cycle of order `n` has no clean third color, then

```text
q - 4 <= n(n-5).                                       (134)
```

Equivalently,

```text
n >= (5 + sqrt(4q+9))/2.                               (135)
```

Thus every odd owner run satisfies the dichotomy

```text
clean reusable third color,
or cycle order at least (5 + sqrt(4q+9))/2.             (136)
```

The second branch is globally sparse.  The internal two-factor on `c` has
only `2q` vertices, so if `L_q` is the least odd integer at least the bound
in (135), the number of no-clean odd owner cycles on the entire shore is at
most

```text
floor(2q / L_q).                                        (137)
```

For any fixed odd length `n`, the no-clean branch disappears once
`q > n(n-5)+4`.  Hence the simultaneous clean-lift mechanism covers every
bounded-length obstruction uniformly for all sufficiently large binary
powers, while the untreated cycles have order `Omega(sqrt(q))` and occur
only `O(sqrt(q))` times.  A closing parity argument may therefore be split
into a local clean-lift theorem and a global census of the long residual
cycles, rather than treating every odd run by the same invariant.

## 39. Ambient port lift of a mixed state cycle

The clean-run analysis above treats the all-horizontal obstruction.  A mixed
odd-horizontal component of the state graph has a different but still exact
ambient normal form.  Let `Omega` be a cycle of `Gamma_c`, with

```text
H(Omega) = number of horizontal state edges,
V(Omega) = number of vertical state edges.
```

At every state `(x,e)` on `Omega`, its two incident state edges use its two
distinct ports by (60).  Join those ports by the two-edge ambient path

```text
port_in -- x -- port_out.                              (138)
```

Now glue these state paths cyclically.  Across a horizontal state edge the
two port occurrences are the same ambient vertex, by (61), so no new edge
is inserted.  Across a vertical state edge the two ports are adjacent—the
exterior edge of the rooted triangle—so insert that one edge.  The result is
a canonical closed ambient walk `W(Omega)` of length

```text
|W(Omega)| = 2(H(Omega)+V(Omega)) + V(Omega)
           = 2H(Omega) + 3V(Omega).                    (139)
```

The walk is reduced at every root: its entering and leaving ports are
distinct.  Across a horizontal transition, the shared port is incident to
two distinct roots joined by the horizontal state edge, so the two cross
edges are distinct.  It is also reduced across a vertical transition, whose
exterior edge cannot be the following cross edge.  Thus the state holonomy is encoded
by a nonbacktracking closed walk with distinguished exterior transition
edges.  In particular,

```text
|W(Omega)| mod 2 = V(Omega) mod 2.                      (140)
```

When `V(Omega)=0`, the lift is exactly the bipartite incidence cycle `C--Z`
of Sections 17--19, and the shore indicators are binary kernel vectors for
`R_ce`.  When `V(Omega)>0`, the exterior transition edges splice incidence
paths belonging to different owner colors; there is no single pair of shore
indicators annihilated by one cross block.  This is why the boundary-vector
transport of (64)--(73) does not automatically cover mixed odd-horizontal
cycles.

The full parity target therefore retains two distinct residual branches:

```text
all-horizontal odd cycles: clean-or-long owner-run program;
mixed odd-horizontal cycles: nonbacktracking port walks W(Omega)
  with an odd number of horizontal state edges.         (141)
```

A mixed-cycle closure must exploit the marked exterior transitions in
`W(Omega)`—for example by a parity law for their owner-color sequence—rather
than reusing the single-pair kernel contraction.

## 40. Triangle cancellation and the mixed incidence skeleton

Every vertical transition has an additional exact signature inside
`W(Omega)`.  Suppose it joins `(x,e)` to `(x,d)` and uses ports `p in e`,
`q in d`.  The end of the first state path, the vertical edge, and the start
of the second state path form the literal ambient triangle

```text
x -- p -- q -- x.                                      (142)
```

Delete this three-edge triangle excursion at every vertical transition.
The other port of `(x,e)` and the other port of `(x,d)` remain joined through
the root `x`, so the deletions splice the walk rather than break it.  The
result is a canonical closed walk `S(Omega)` using only cross edges between
`c` and its exterior:

```text
|S(Omega)| = |W(Omega)| - 3V(Omega) = 2H(Omega).        (143)
```

It alternates between roots in `c` and exterior port vertices.  At a
horizontal state transition, the exterior port is shared and the walk moves
between two roots.  At a former vertical transition, the root is shared and
the walk moves between ports of two different owner colors.  Thus the state
cycle has a dual incidence description:

```text
horizontal state edge  <-> exterior-centered two-step in S(Omega),
vertical state edge    <-> color change at a root of S(Omega).           (144)
```

If `Omega` is an odd-horizontal obstruction, `S(Omega)` has an odd number
of root-centered two-edge steps.  When `V=0`, this skeleton is again the
single-color incidence cycle `C--Z`.  When `V>0`, it is a closed alternating
walk in the concatenated exterior incidence matrix

```text
B_c = [ R_ce ]_(e != c),
```

with owner color changing only at specified root visits.  This is the mixed
analogue of the kernel cycle used in Section 17.  The next transport target
is to turn the odd half-length of `S(Omega)` into a binary boundary vector or
to show that repeated vertices/edges pair its contribution; the raw walk
need not be a simple cycle, so that reduction is not automatic.

## 41. Extraction of an odd-half simple incidence cycle

The repeated-vertex issue in Section 40 can be removed at the cost of losing
the original state-cycle ordering.  In fact `S(Omega)` is a closed trail:
every one of its cross edges is the port attachment of one state of
`Omega`; a state occurs only once on the state-cycle component, its two
ports are distinct by (60), and two states at the same root use different
owner components.  Hence no ambient cross edge repeats.

Every closed trail in a simple graph decomposes into edge-disjoint ordinary
simple cycles.  Applying this to the bipartite incidence graph `B_c` gives
cycles of lengths

```text
2 ell_1, ..., 2 ell_t,
```

with every `ell_i >= 2`; a two-edge doubled piece is impossible because the
trail has no repeated edge.  Length additivity in (143) gives

```text
ell_1 + ... + ell_t = H(Omega).                         (145)
```

Consequently, when `Omega` is odd-horizontal, at least one extracted simple
cycle has odd half-length (necessarily `ell >= 3`):

```text
there is a simple cycle of B_c of length 2 ell,
with ell odd.                                           (146)
```

This cycle alternates between `ell` distinct roots in `c` and `ell`
distinct exterior port vertices.  Each exterior vertex carries its component
color.  At an exterior-centered two-step the two neighboring roots came
from a horizontal state transition and therefore share that owner color;
color changes inherited from vertical transitions occur at roots.  After
the walk decomposition, a cycle may retain only a subsequence of those
changes, but every edge is still an actual cross-incidence edge with its
exterior color label.

The extracted cycles are edge-disjoint.  Their inherited color-change
counts at roots therefore sum to at most `V(Omega)`, giving a residual
transition budget even though the original cyclic ordering is lost.

Thus both residual branches produce an odd-half incidence cycle:

* an all-horizontal obstruction gives a monochromatic cycle which is an
  entire component of one cross block;
* a mixed obstruction gives a possibly multicolored simple cycle in the
  concatenated block `B_c`.

Only the first is automatically a binary kernel vector for a single
`R_ce`; the second need not be induced or component-closed.  The next mixed
transport theorem must exploit the color changes on the simple cycle, or
show that an odd-half multicolored incidence cycle contains a smaller
monochromatic/kernel obstruction.

## 42. Root projection collapses the mixed geometry

The simple-cycle extraction is stronger after forgetting the exterior port
vertices.  Contract every exterior-centered two-step of `S(Omega)`.  By
(144), each such step came from a horizontal state edge, hence projects to
the corresponding internal edge of `A_c`.  Former vertical transitions
only concatenate two such edges at their common root.  We obtain a closed
walk

```text
pi(Omega) in A_c,       |pi(Omega)| = H(Omega).         (147)
```

The projection is edge-simple whenever `H(Omega)>0`.  Indeed, every internal
edge has a unique owner color, so an occurrence of that edge in the
projection lifts to its unique horizontal edge of `Gamma_c`.  A second
occurrence would repeat that state edge on the cycle `Omega`.  Hence
`pi(Omega)` is a nonempty closed trail in the internal two-factor.

The edge support of a closed trail is Eulerian.  A nonempty connected
Eulerian subgraph of the two-regular graph `A_c` must be an entire cycle
component `C`.  Therefore

```text
E(pi(Omega)) = E(C).                                   (148)
```

Edge-simplicity now gives

```text
H(Omega) = |C|,                                        (149)
```

and the horizontal edges of `Omega` project bijectively onto all edges of a
single internal `A_c` cycle.  The owner color may change at its vertices,
along the vertical subpaths of `Omega`, but there is no additional mixed
root geometry.

Consequently every odd-horizontal obstruction lies over an odd internal
cycle and traverses it exactly once.  The all-horizontal branch is the
monochromatic special case; the genuinely mixed branch is precisely an odd
internal cycle whose consecutive edges have different owners at some
vertices, with those owner changes realized by rooted triangle paths.  This
reduces the next invariant from arbitrary multicolored cycles of `B_c` to a
color-change law on the fixed cyclic edge word of an odd component of
`A_c`.

## 43. Canonical rooted transition paths

Write the cycle from Section 42 as

```text
C = (x_i)_(i mod n),
e_i = owner color of the horizontal edge x_i x_(i+1).
```

At a fixed root `x_i`, retain only the vertical edges of `Gamma_c`; this is
the rooted triangle multigraph on the active exterior colors.  The state
cycle enters the root at `(x_i,e_(i-1))` and leaves it at `(x_i,e_i)`.
The intervening vertical segment is therefore a path

```text
P_i : e_(i-1) --> e_i                                  (150)
```

in that rooted triangle multigraph.  If the two colors agree, (51) gives
horizontal degree two and vertical degree zero at the common state, so
`P_i` has length zero.  If they differ, each endpoint state has horizontal
degree one and hence vertical degree one by (51), while every intermediate
state on the segment has horizontal degree zero and vertical degree two.
Thus `P_i` is the entire path component joining the two owner colors; it is
simple even when the rooted triangle graph has parallel edges elsewhere.

There cannot be a second rooted path component with horizontal endpoints.
The two incident edges of `A_c` are the only possible horizontal state edges
at `x_i`, and Section 42 shows that both occur in `Omega`.  All remaining
vertical components at the root, if any, are disjoint vertical-only cycles.
Consequently `Omega` has the canonical cyclic substitution

```text
horizontal edge of color e_i,
then rooted transition path P_(i+1),
then horizontal edge of color e_(i+1), ...             (151)
```

and

```text
V(Omega) = sum_i |P_i|.                                (152)
```

This separates the residual data cleanly.  The root geometry is the odd
cycle `C`; its edge word is `(e_i)`; and each genuine color change is
certified by a unique chain of three-component triangles at that root.
The next possible parity input is therefore local: a mod-two label on rooted
triangle edges whose path integral between `e_(i-1)` and `e_i` telescopes
around the owner word.  Vertical-only rooted cycles must have zero integral
for such a label to be well defined.

## 44. The owner-change graph is Eulerian, so color potentials are blind

Forget the internal vertices of the rooted paths `P_i` and retain only their
endpoint owner colors.  For distinct exterior colors `e,d`, let `m_ed(C)`
be the number of roots of `C` at which the incoming and outgoing edge owners
are `e` and `d`.  These multiplicities form a loopless multigraph `Q_C` on
the owner colors.  Every maximal nonempty run of color `e` in the cyclic
edge word has two boundary roots, so

```text
deg_(Q_C)(e) = sum_(d != e) m_ed(C) is even.            (153)
```

Thus `Q_C` is Eulerian.  In particular, for every binary function `u` of
the owner color,

```text
sum_(owner changes {e,d}) (u(e)+u(d)) = 0.             (154)
```

The same conclusion holds if a label on rooted triangle edges is merely the
color coboundary `u(e)+u(d)`: its integral along `P_i` is
`u(e_(i-1))+u(e_i)`, and the sum of these path integrals vanishes around
the cyclic word.  Hence neither the owner-change multigraph nor a potential
depending only on owner colors can detect that `|C|` is odd.  A closing
cochain must retain at least the root, the actual port, or an owner-factor
mark transported between components.

There is nevertheless a forced odd local object.  If

```text
r_e(C) := number of edges of C owned by e,
```

then

```text
sum_e r_e(C) = |C| = 1  (mod 2).                       (155)
```

So some owner color has odd total run length.  Decomposing its edges into
maximal cyclic runs shows that it has an odd number of odd-length runs
(where a monochromatic `C` is the closed-run special case).  The mixed
transport target can therefore be stated minimally: pair or rule out these
odd owner paths using their two rooted transition paths.  Equation (154)
shows why recording only the two endpoint colors cannot do so; the needed
pairing must use the marked triangle/port data at the endpoints.

## 45. Radius-two packing on an owner path

Let `P` be a proper maximal run of owner color `e` on the mixed cycle `C`.
If it has `ell` edges, its vertex set `U` has

```text
m = ell + 1
```

distinct roots.  For every third owner color `d != c,e`, an edge of
`F_d[c][U]` cannot join vertices at path distance one or two.  Distance-one
vertices already share their owner-`e` port, while distance-two vertices
already share their middle root in `A_c`; a `d`-owner edge would give either
pair a second common neighbor.

The square of the length-`ell` path has `(m-1)+(m-2)=2m-3` edges.  Therefore
the union `L_ce` of the third owner factors satisfies

```text
e_(L_ce)(U)
  <= binom(m,2) - (2m-3)
  = (m-2)(m-3)/2
  = (ell-1)(ell-2)/2.                                  (156)
```

This remains valid when `U` is all of `C` minus one owner edge: the closing
edge and its additional distance-two exclusions can only reduce the number
of allowed third-owner chords.

For a third color `d`, call it `P`-clean when `F_d[c][U]` has no edge.  Each
nonclean color consumes at least one edge in (156), so

```text
# {P-clean third colors}
  >= (q-4)/2 - (ell-1)(ell-2)/2.                       (157)
```

Equivalently, a clean color is guaranteed whenever

```text
q - 4 > (ell-1)(ell-2).                                (158)
```

The first cases are particularly rigid: every third color is clean on a
one-edge run, and at most one third color is nonclean on a three-edge run.
For a `P`-clean color, the two-point fibers over all `m` roots are disjoint,
exactly as in (125), so the clean-lift dichotomy and the consecutive-fiber
exclusions (126)--(129) apply along the whole path.  The only new data are
at its two endpoints, precisely where the rooted transition paths of
Section 43 attach.  Thus the mixed problem now has the same clean-or-long
shape as the monochromatic branch, but localized to the odd owner runs
forced by (155).

## 46. Endpoint-neutral clean colors

Let the two `A_c` edges immediately before and after the maximal `e`-run
`P` have owners `f_-` and `f_+`; both differ from `e`, though they may equal
each other.  For a `P`-clean third color `d`, every internal root `x` of the
run has

```text
a_xd = 0,
```

because its two incident internal edges are both owned by `e`.  At the left
or right endpoint, the same holds unless `d=f_-` or `d=f_+`, respectively.
In the exceptional endpoint case `a_xd=1`, so the rooted budget (50)--(52)
forces

```text
b_xd = 0,       sum_g tau_xdg = 1.                     (159)
```

This unique rooted triangle is the vertical state edge incident to the
owner-`d` horizontal endpoint; equivalently, it is the terminal edge of the
rooted transition path from Section 43.

Call a `P`-clean color **endpoint-neutral** when it is different from both
`f_-` and `f_+`.  There are at most two forbidden colors, so (157) guarantees
an endpoint-neutral clean color as soon as

```text
(q-4)/2 - (ell-1)(ell-2)/2 >= 3,
```

or equivalently

```text
q >= (ell-1)(ell-2) + 10.                              (160)
```

For such a color `d`, one has `a_xd=0` at every root of `P`, including its
endpoints.  Hence the exact clean-lift alternative holds uniformly along
the entire path:

```text
Y_d(x) is an A_d edge and emits no rooted third-color triangle,
or
Y_d(x) is a nonedge and emits exactly two.              (161)
```

The fibers are pairwise disjoint, and consecutive fibers are anticomplete
in `A_d`.  Thus a short odd owner run has a reusable two-point lift with no
endpoint defect once (160) holds.  When (160) fails, either the run is
quadratically long in `q`, or all clean colors can be concentrated on the
at most two endpoint owners; the latter is now the finite exceptional
configuration requiring a marked endpoint count.

## 47. Root--port curl interface

The color-only failure in Section 44 specifies which part of a Farkas
potential can still carry information.  Orient an edge `t -> u` of the
state cycle, and let `p_t` and `p_u` be the actual ports used at its two
ends.  On a horizontal edge they are the same exterior vertex; on a
vertical edge they are the two exterior vertices of the rooted triangle.

For state prices `alpha_t` and cross-prices `mu_(t,p)`, define the binary
root--port curl

```text
W_(t,u)
  := alpha_t + alpha_u
   + mu_(t,p_u) + mu_(u,p_t).                           (162)
```

This is the characteristic-two version of the complete row--fiber Farkas
curl (12n) in the B.3 audit: the ordinary degree-gradient is the `alpha`
part, while the two crossed `mu` evaluations retain the individual root and
port at opposite ends of the transition.  It is symmetric as a binary edge
label, equivalently antisymmetric before reduction modulo two.

Around a state cycle `Omega`, the `alpha` terms cancel and

```text
sum_(tu in Omega) W_(t,u)
  = sum_(tu in Omega)
      (mu_(t,p_u) + mu_(u,p_t)).                        (163)
```

Unlike (154), the right side need not vanish when the owner-change graph is
Eulerian: two occurrences of the same owner color can have different roots
and different actual ports.  Thus (162) is the smallest imported curl shape
which escapes the proved blind spot.

The exact remaining theorem can now be stated without claiming arbitrary
prices suffice.  One must construct `mu` from the simultaneous clean-lift
or incoming-fiber-cap data, with whatever sign/integrality constraints that
construction imposes, so that on admissible state edges

```text
W_(t,u) = 1 on horizontal edges,
W_(t,u) = 0 on vertical edges.                          (164)
```

Equation (164) alone does **not** give `H(Omega)=0`: by (163), it only
identifies `H(Omega)` with the crossed-`mu` cycle integral.  The closing
theorem must additionally derive the routing/capacity conservation law

```text
sum_(tu in Omega) (mu_(t,p_u) + mu_(u,p_t)) = 0         (164a)
```

for every admissible state cycle (or derive a different forced value which
contradicts odd `H`).  Only (164) together with (164a) closes (57).
Without this routing-derived restriction on `mu`, (164) is merely a linear
reparameterization of the desired cocycle and proves nothing.  The
endpoint-neutral clean colors of Section 46 identify the available source
of the missing conservation: their disjoint two-point fibers give genuine
incoming capacity constraints indexed by the marked root and port, exactly
the data retained in (162).

## 48. The clean lift supplies an actual root--port capacity system

Fix an endpoint-neutral `P`-clean color `d`, and let

```text
T_d := {x in U : Y_d(x) is not an A_d edge}.
```

For each `x in T_d`, (161) gives two rooted triangles using `d`.  By the
port bijection (60), their `d`-vertices are exactly the two distinct members
of `Y_d(x)`, one per triangle.  Write

```text
y in Y_d(x)  -->  z(y)
```

for the other exterior vertex of that triangle.  Thus every demanded source
port `y` is assigned to one actual target port `z(y)` in a component other
than `c,d`.

The two targets at one root are distinct.  Otherwise the two members of
`Y_d(x)` would have the two common neighbors `x` and `z`, creating a C4.
More generally,

```text
z(y)=z(y')  ==>  pathDistance_P(x,x') >= 3             (165)
```

for sources over distinct roots `x,x'`.  At distance one the roots already
share their owner-`e` port; at distance two they already share the middle
root of the `A_c` path.  A repeated target would be a second common neighbor
in either case.

There is also a global target capacity.  If `z` lies in exterior component
`g`, its cross degree into `c` is two, so

```text
|{x in T_d : some y in Y_d(x) has z(y)=z}| <= 2.       (166)
```

Equations (165)--(166), together with two distinct demands at every root of
`T_d`, form a genuine root--port capacitated assignment, not a relaxation.
The allowed target of a source `y` is further constrained by the actual
cross edge `y z` in `R_dg`.  Fibers with `x notin T_d` consume no target:
their two source ports are paired internally by the `A_d` edge.

This is the direct analogue of the incoming-fiber caps priced by `mu` in
(12n).  Any Farkas dual of the assignment must retain the root of the source
and the individual target port, and therefore has exactly the crossed
root--port form (162).  What is not yet proved is that the cap system for all
endpoint-neutral clean colors can be coupled so that its dual evaluates to
the horizontal marking (164); (165)--(166) identify the concrete primal
constraints a closing separation theorem must use.

## 49. Target-support and collision bound

Continue with the clean color `d`.  Let `t_d=|T_d|`, and let `Z_d` be the
set of distinct target ports used by the `2t_d` assignments in Section 48.
By (166), every target has multiplicity one or two.  Hence the number of
target collisions is exactly

```text
kappa_d := 2t_d - |Z_d|.                               (167)
```

Each collision determines the unordered pair of roots whose source ports
use the repeated target.  By (165), that pair has path distance at least
three.  Moreover this map from collisions to root pairs is injective: two
different repeated targets for the same pair would be two common neighbors
of those roots, contradicting C4-freeness.  Therefore, if

```text
a(T_d) := # {{x,x'} subset T_d : pathDistance_P(x,x') >= 3},
```

then

```text
kappa_d <= a(T_d),
|Z_d| >= 2t_d - a(T_d),
|Z_d| >= t_d.                                          (168)
```

The last inequality is the global capacity-two bound; the middle inequality
is stronger when the demanded roots are concentrated in a short interval.
For example, a one-edge run has no allowable collision pair, so all targets
are distinct.  On a three-edge run, the only possible collision pair is the
two endpoints, so

```text
|Z_d| >= 2t_d - 1.                                     (169)
```

For demands at every one of the `m` path roots,
`a(T_d)=(m-2)(m-3)/2`, the same complement-of-path-square count as (156).
Thus the clean-lift primal has an explicit collision-energy coordinate
`kappa_d`, rather than only a coarse target capacity.  A root--port price can
charge each repeated target once, and (168) bounds the total charge by the
geometry of the demanded root set; this is the direct analogue of the
fiber-collision statistic retained by the successful B.3 Farkas curl.

## 50. Mixed clean-or-long dichotomy

Let `C` be an odd mixed cycle from Section 42.  By (155), choose an owner
color `e` for which `r_e(C)` is odd.  Its cyclic edge set has an odd number
of odd-length maximal `e`-runs.  Define `L'_q` to be the least positive odd
integer `ell` for which

```text
q < (ell-1)(ell-2) + 10.                               (170)
```

Then the parity-carrying runs have the following exact alternative:

```text
some odd e-run has length ell < L'_q
  and admits an endpoint-neutral clean lift;

or every odd e-run has length at least L'_q.            (171)
```

Indeed, in the first case the negation of (170) is precisely the sufficient
condition (160).  In the second case, the odd runs are edge-disjoint subsets
of `C`, so their number is at most

```text
floor(r_e(C)/L'_q)
  <= floor(|C|/L'_q)
  <= floor(2q/L'_q).                                   (172)
```

For large `q`, `L'_q` is asymptotic to `sqrt(q)`, so the second branch has
only `O(sqrt(q))` parity-carrying runs, each of length `Omega(sqrt(q))`.
For every fixed odd `ell`, the first branch holds once
`q >= (ell-1)(ell-2)+10`.

This is the mixed counterpart of (134)--(137), now with the endpoint mark
retained.  The short branch supplies the verified primal cap system and
collision bound (165)--(169) on an odd run.  The long branch is a sparse
global census on the one odd internal cycle `C`.  Thus a closing argument
need only prove root--port conservation for the endpoint-neutral short-run
system and separately pair the bounded family of long odd runs; no arbitrary
mixed state-cycle geometry remains.

## 51. Transpose symmetry on the endpoint-neutral clean core

For a fixed maximal `e`-run `P`, let `D_P` be the set of third colors which
are both `P`-clean and endpoint-neutral.  Consider a rooted triangle at
`x in U` whose two exterior vertices are

```text
y in d,       z in g,       d,g in D_P.
```

In the clean-lift capacity system for `d`, this triangle is the assignment
`y -> z`.  Since `g` is also endpoint-neutral, `a_xg=0`; the same triangle
forces `Y_g(x)` to be in its nonedge branch and appears in the `g`-system as
the reverse assignment `z -> y`.  Consequently the union of all directed
assignments with both colors in `D_P` is invariant under transpose:

```text
(x,d,y) -> (x,g,z)
  iff
(x,g,z) -> (x,d,y).                                    (173)
```

It follows immediately that every antisymmetric root--port weight cancels
on the clean core:

```text
sum_(d,g in D_P) W((x,d,y),(x,g,z)) = 0.               (174)
```

This is the conservation mechanism missing from (164a), but so far only on
the induced clean core.  All uncancelled assignments have their target
color outside `D_P`.  Their color support is sharply localized.  By (156),
at most

```text
(ell-1)(ell-2)/2
```

third colors are nonclean, and endpoint neutrality excludes at most the two
boundary owners `f_-`,`f_+`.  The run owner `e` can occur in a rooted
triangle only at the two boundary roots, because its state has horizontal
degree two and vertical degree zero at every internal root.  Thus the curl
defect is supported on

```text
at most (ell-1)(ell-2)/2 + 2 exceptional third colors,
plus at most two owner-e boundary assignments.          (175)
```

Equations (173)--(175) turn the desired global conservation into a boundary
problem: the large endpoint-neutral clean core cancels exactly by transpose,
and only a bounded exceptional-color interface remains.  This is the same
primal/transpose mechanism as the derived complete Farkas normal form
(12m)--(12n); here the clean-core cancellation itself is obtained directly
from the simultaneous rooted triangles, without yet constructing a boundary
price.

## 52. The exceptional boundary is even at every root

Fix a root `x in U` and view its rooted triangles as the vertical
multigraph on exterior colors.  For every `d in D_P`, endpoint neutrality
gives `a_xd=0`, and (50) gives

```text
deg_x(d) = sum_g tau_xdg = 2 - 2b_xd in {0,2}.         (176)
```

Apply the handshake identity to the vertex set `D_P` in this rooted
multigraph.  Internal triangle edges contribute twice, so the number
`lambda_x(D_P)` of triangles with exactly one exterior color in `D_P`
satisfies

```text
lambda_x(D_P)
  = sum_(d in D_P) deg_x(d)
  = 0  (mod 2).                                        (177)
```

Each such cut triangle is exactly one directed clean-system assignment whose
reverse lies outside the transpose-symmetric core of (173).  Therefore the
number of leakage assignments is even separately at every root, and hence
even on the entire run:

```text
sum_(x in U) lambda_x(D_P) = 0  (mod 2).               (178)
```

This closes the **unweighted** boundary parity.  It does not establish the
root--port conservation (164a), because a crossed price can distinguish the
different cut triangles at the same root.  The surviving obstruction is
therefore precisely a weighted distribution problem on the exceptional
interface (175), not a parity of its cardinality.  Any successful price
construction may be normalized by subtracting a constant boundary weight,
whose contribution vanishes by (177), leaving only price differences among
the exceptional target ports.

## 53. Global target capacity across all clean colors

The capacity in (166) is simultaneous across the source color `d`, not only
valid one clean system at a time.  Let

```text
N_P := 2 sum_(d in D_P) t_d
```

be the total number of demanded source ports over the endpoint-neutral clean
colors, and let `Z_P` be the union of all target ports they use.  A target
`z` cannot serve two different source colors at the same root `x`: the two
source ports `y in d`, `y' in d'` would give the ambient four-cycle

```text
x -- y -- z -- y' -- x.
```

Across distinct roots, every service consumes the cross edge `xz`, and `z`
has exactly two cross neighbors in `c`.  Hence every target has total
multiplicity at most two across **all** `d in D_P`.

Put

```text
T_* := union_(d in D_P) T_d,
K_P := N_P - |Z_P|.
```

As in Section 49, `K_P` is the number of multiplicity-two targets.  Such a
target determines two distinct roots in `T_*` at path distance at least
three.  Two repeated targets cannot determine the same root pair by
C4-freeness.  Therefore the global collision map is injective and

```text
K_P <= a(T_*),
|Z_P| >= N_P - a(T_*),
|Z_P| >= N_P/2 = sum_(d in D_P) t_d.                   (179)
```

In particular, since `T_* subset U`,

```text
a(T_*) <= (ell-1)(ell-2)/2.                            (180)
```

Unlike the result obtained by summing (168) color by color, (179) pays the
path-square collision budget only once, not once per clean color.  On a
one-edge run every target used anywhere in the clean core is distinct; on a
three-edge run there is at most one repeated target across the entire clean
core.  This is the first genuinely simultaneous quantitative constraint on
the endpoint-neutral lift systems.

## 54. Exact ambient port-support upper bound

Every target in `Z_P` is adjacent to its triangle root in `U`.  The total
pool of possible targets can therefore be counted exactly from the cross
blocks out of `c`.  For an exterior color `g != c`, put

```text
a_g(U) := |E(F_g[c][U])|.
```

There are `2m` incidences from the `m` roots of `U` into `g`.  A vertex of
`g` has one or two neighbors in `U`; the multiplicity-two vertices are in
bijection with the edges of `F_g[c][U]`.  Hence

```text
|supp(R_gc U)| = 2m - a_g(U).                          (181)
```

Let

```text
A_ext(U) := sum_(g != c) a_g(U).
```

There are `(q-2)/2` exterior colors, so their vertex sets are disjoint and
(181) sums to

```text
|union_(g != c) supp(R_gc U)|
  = m(q-2) - A_ext(U).                                 (182)
```

Since `Z_P` is a subset of this union, combine (179) and (182) to obtain the
simultaneous occupancy inequality

```text
2 sum_(d in D_P) t_d
  <= m(q-2) - A_ext(U) + a(T_*).                       (183)
```

The `ell` consecutive edges of the owner run all belong to `F_e[c][U]`, so

```text
A_ext(U) >= ell.                                       (184)
```

Thus (183) couples three quantities which the separate rooted budgets do
not: total nonedge-fiber demand over all neutral clean colors, every
exterior-owner chord internal to the run, and the once-paid collision budget
of its demanded roots.  It is a deterministic fixed-margin/collision-energy
constraint, not a fitted price inequality, and is the direct object to test
against a monotone transport or convexity argument.

## 55. Nonclean colors also consume the target pool

Let `h_P` be the number of third colors `d != c,e` which are not `P`-clean.
The owner factors are edge-disjoint.  Besides the `ell` run edges in
`F_e[c][U]`, every nonclean third color contributes at least one edge to its
own `F_d[c][U]`.  Therefore (184) sharpens to

```text
A_ext(U)
  >= ell + sum_(d != c,e, d nonclean) a_d(U)
  >= ell + h_P.                                        (185)
```

Substitution in (183) gives

```text
2 sum_(d in D_P) t_d
  <= m(q-2) - ell - h_P + a(T_*).                      (186)
```

Thus the two apparent exceptional mechanisms cannot be budgeted
independently: every color removed from the clean transpose core because it
contains a chord also removes at least one vertex from the ambient target
pool.  Conversely, when `h_P` is small, `D_P` contains almost every third
color (apart from the at most two endpoint owners), and the once-paid global
collision bound (179) applies to a large simultaneous family.  Equation
(186) is the clean-shortage versus target-capacity tradeoff to combine with
the monotone-transport collision statistic.

## 56. Full clean core with variable endpoint demand

Endpoint neutrality is needed for the uniform two-or-zero alternative
(161), but not for the assignment and capacity arguments.  Let `C_P` be the
set of **all** `P`-clean third colors, including either boundary owner when
it is clean.  For `d in C_P` and `x in U`, define its vertical demand

```text
v_xd := 2 - a_xd - 2b_xd
      = sum_g tau_xdg  in {0,1,2}.                     (187)
```

At internal roots `a_xd=0`; at an endpoint, `a_xd=1` only when `d` is that
side's boundary owner, in which case `v_xd=1` by (159).  The port bijection
(60) assigns the `v_xd` incident vertical edges to distinct members of the
clean fiber `Y_d(x)`.  Thus the capacity system of Sections 48--49 extends
verbatim with a one-port demand allowed at those exceptional endpoints.

Put

```text
N_P^+ := sum_(d in C_P, x in U) v_xd,
T_+   := {x in U : some d in C_P has v_xd > 0},
Z_P^+ := union of all targets of these demands.
```

The same-root C4 exclusion and the cross degree two of every target give
global target multiplicity at most two.  Repeated targets inject into
distance-at-least-three pairs of `T_+`.  Hence

```text
|Z_P^+| >= N_P^+ - a(T_+),
|Z_P^+| >= ceil(N_P^+/2).                              (188)
```

Every target still lies in the ambient port pool (182), so

```text
N_P^+
  <= m(q-2) - A_ext(U) + a(T_+)
  <= m(q-2) - ell - h_P + a(T_+).                     (189)
```

Transpose symmetry also enlarges: a triangle whose two exterior colors lie
in `C_P` gives reciprocal directed assignments whether their demands are one
or two.  Therefore every antisymmetric weight cancels on the full clean
induced core.  The remaining target colors are only the `h_P` nonclean third
colors and the run owner `e`; the latter has vertical degree zero internally
and contributes at most one assignment at each boundary root.  Relative to
(175), the two boundary-owner colors have been absorbed into the clean core
whenever possible.

This variable-demand formulation is the natural primal system for a Hall or
Farkas argument.  The endpoint-neutral subsystem remains useful when a
uniform two-demand row is required, but the deterministic target-capacity
and transpose-cancellation statements lose nothing by working with all
clean colors.

## 57. The clean-core threshold and its endpoint parity defect

The full clean core separates two thresholds which were conflated before
(187).  By (157), the strict inequality

```text
q - 4 > (ell-1)(ell-2)                                (190)
```

already guarantees `C_P` is nonempty.  Thus (190), equivalently (158), is
enough to obtain an actual clean root--port assignment system satisfying
the global capacity bounds (188)--(189) and the clean--clean transpose
cancellation.  The stronger bound

```text
q >= (ell-1)(ell-2) + 10                              (191)
```

is needed only when one must discard both possible boundary owners and keep
the uniform zero-or-two demand alternative (161).  In particular, a clean
color concentrated on a boundary owner is no longer an exceptional failure:
it supplies the same primal system with one demand at that endpoint.

There is also an exact parity description of the price paid for retaining
those boundary owners.  Let `lambda_x(C_P)` count rooted triangles with
exactly one exterior color in `C_P`, as in Section 52.  The rooted handshake
identity and (187) give

```text
lambda_x(C_P)
  == sum_(d in C_P) v_xd
  == #{sides of P ending at x whose boundary owner lies in C_P}  (mod 2).
                                                                  (192)
```

At an internal root the right side is zero.  At either endpoint it is one
exactly when that endpoint's boundary owner is clean (the two endpoints are
counted separately even when their owner colors agree).  Consequently the
full-clean leakage is even at every internal root, while each endpoint has
at most one unit of odd parity defect.  This does not prove the weighted
conservation (164a), but it localizes every parity defect of the enlarged
transpose core to the two rooted transition interfaces.  Together with the
last paragraph of Section 56, the remaining weighted boundary consists of
the `h_P` nonclean target colors and at most two endpoint incidences involving
the run owner `e`.

## 58. Exact boundary normal form for a one-edge owner run

Suppose `ell=1`.  Then `U={x_-,x_+}`, the only pair in `U` is the run edge
owned by `e`, and (157) gives `h_P=0`: every third color is `P`-clean.  Hence
`C_P` is the full set of exterior colors other than `e` (and the root color
`c`).

At `x_-`, let `f_-` be the owner of the preceding `A_c` edge.  In the rooted
triangle multigraph on exterior colors, (187) gives

```text
deg_(x_-)(e) = deg_(x_-)(f_-) = 1,
deg_(x_-)(d) in {0,2} for every other exterior color d. (193)
```

The same statement holds at `x_+` with `f_+`.  Each rooted color graph has
maximum degree two, so (193) gives an exact decomposition: one path from
`e` to the boundary owner `f_\pm`, together with vertex-disjoint cycles and
isolated vertices.  This is the Section-43 rooted transition path with no
nonclean color available anywhere along it.

Equivalently, the cut from `C_P` to its complement has exactly one edge at
each endpoint:

```text
lambda_(x_-)(C_P) = lambda_(x_+)(C_P) = 1.             (194)
```

Indeed, `e` is the only exterior color outside `C_P`, and its rooted vertical
degree is one at either endpoint.  All clean--clean directed assignments
cancel in reciprocal pairs under an antisymmetric weight.  Therefore the
entire one-edge run leaves precisely two uncancelled directed assignments,
one at each endpoint, both targeting an `e`-port:

```text
clean source at x_-  -->  e-port,
clean source at x_+  -->  e-port.                      (195)
```

The clean source need not be `f_\pm`: the transition path may pass through
other clean colors before reaching `e`.  Thus (195) is an exact two-port
boundary normal form, not yet a proof that the crossed prices of the two
ports agree.  Any constant contribution assigned to an `e`-target cancels
modulo two across the run; the remaining `ell=1` obstruction is only the
difference between these two rooted `e`-port prices.  This is the smallest
weighted conservation problem left by (164a), with no nonclean leakage and
no internal run root.

The two targets in (195) are in fact pinned more sharply.  Since the run
edge `x_- x_+` is owned by `e`, its two `e`-fibers have the form

```text
Y_e(x_-) = {p,p_-},    Y_e(x_+) = {p,p_+},             (196)
```

where `p` is their unique common owner port.  Neither cut assignment can
target `p`.  For example, if a clean source `y` at `x_-` formed the rooted
triangle `x_- y p`, then

```text
x_- -- y -- p -- x_+ -- x_-
```

would be an ambient four-cycle.  The argument at `x_+` is symmetric.  Hence
the two surviving targets are necessarily `p_-` and `p_+`.  They are
distinct: equality would give `x_-` and `x_+` the two common neighbors `p`
and `p_-=p_+`, again an ambient four-cycle.  Thus (195) refines to

```text
clean source at x_-  -->  p_-,
clean source at x_+  -->  p_+,       with p_- != p_+. (197)
```

The one-edge terminal is therefore not a collision case.  Its entire
uncancelled datum is the ordered pair of distinct private owner ports on the
two sides of the shared port `p`.  Closing `ell=1` now means proving that the
admissible crossed price has equal values on these two private ports (or that
their forced difference has the wrong parity); no target-support ambiguity
remains.

The two clean sources `y_-` and `y_+` in (197) are distinct as well.  If they
were one vertex `y`, then the adjacent roots `x_-` and `x_+` would have the
two common neighbors `p` and `y`, again giving a four-cycle.  Reversal of the
oriented run edge swaps both ordered pairs

```text
(x_-,x_+)  |-->  (p_-,p_+) and (y_-,y_+).             (198)
```

Thus (198) is a canonical oriented private-port mark attached to every
one-edge owner run.  Its collision count is zero, since `p_- != p_+`; a
price depending only on total target collisions cannot detect this terminal.
The missing invariant must retain the orientation of the two private ports
(possibly together with their distinct clean sources), precisely the
root--port information absent from the color-only no-go of Section 44.

## 59. The private-port mark is a line-cycle neighborhood

There is a canonical two-factor on the `e`-ports themselves.  Each port
`p in e` has two neighbors in `c`, hence labels the corresponding edge of
`F_e[c]`.  Define `B_ec` on the `e`-ports by joining two labels when their
`F_e[c]` edges share a root in `c`.  On every cycle of `F_e[c]`, this is its
line graph, so `B_ec` is again a disjoint union of cycles.

For the one-edge run of Section 58, the three ports in (196) satisfy

```text
N_(B_ec)(p) = {p_-,p_+}.                               (199)
```

Indeed, the `F_e[c]` edge labelled by `p` is `x_-x_+`; the other edge at
`x_-` is labelled by `p_-`, and the other edge at `x_+` by `p_+`.  Thus the
oriented mark (198) is exactly an orientation of the two neighbors of the
marked center `p` in this line-cycle.

More generally, this conclusion holds at every marked center `p in M_e`,
not only at an isolated one.  The internal two-factor `A_e` has no edge
inside its closed `B_ec`-neighborhood:

```text
E(A_e[N_(B_ec)[p]]) = empty.                           (200)
```

For the pairs `p p_-` and `p p_+`, the corresponding root has at least one
incident `e`-owned `A_c` edge, so its rooted budget has `a in {1,2}` and
forces `b=0`.  If instead `p_- p_+` were an `A_e` edge, then

```text
x_- -- p_- -- p_+ -- x_+ -- x_-
```

would be an ambient four-cycle.  These are all three possible pairs, proving
(200).

Let `M_e` be the set of `e`-ports labelling the `e`-owned edges of the
projected `A_c` cycle.  A center `p in M_e` comes from a one-edge maximal
run exactly when neither of its two `B_ec` neighbors lies in `M_e`.
Consequently the `ell=1` terminal is the following simultaneous-two-factor
object on component `e`: an isolated marked center of the cyclic factor
`B_ec` whose closed radius-one neighborhood is independent in the cyclic
factor `A_e`, together with an orientation of its two `B_ec` neighbors.
This is the self-indexing form of the private-port invariant.  A closing
argument may now seek a parity rule for these oriented isolated marks in the
pair `(A_e,B_ec)`, rather than an unconstrained price on ambient ports.

## 60. Consecutive edge marks telescope, but lose run parity

The line-cycle description makes the behavior on a longer `e`-run exact.
Orient a maximal run of `ell` edges and write consecutive `B_ec` labels as

```text
p_0, p_1, ..., p_ell, p_(ell+1),                       (201)
```

where `p_1,...,p_ell` label the run edges and `p_0,p_(ell+1)` label the
other `F_e[c]` edges at its boundary roots.  The oriented private-port mark
of the run edge labelled `p_i` is then

```text
delta_i := [p_(i+1)] - [p_(i-1)]                       (202)
```

in the free abelian group on `e`-ports.  Reversing the run negates every
`delta_i`.  Direct cancellation gives

```text
sum_(i=1)^ell delta_i
  = [p_ell] + [p_(ell+1)] - [p_0] - [p_1].             (203)
```

For `ell=1`, the two occurrences of `[p_1]` cancel and (203) is exactly the
private-target difference `[p_2]-[p_0]` from Section 58.  For longer runs,
all labels more than one step from the boundary cancel.  Thus the entire
linear oriented mark compresses to the two adjacent `B_ec` edges at each
end of the run.

Equation (203) is useful boundary localization, but also a no-go: its form
does not distinguish odd `ell` from even `ell`.  Applying any scalar port
potential to (203), or reducing it modulo two, still sees only those four
boundary labels.  Therefore the odd-run invariant demanded after (155)
cannot be the unweighted sum of the per-edge private-port differences.  It
must retain an alternating/root-dependent coefficient, a nonlinear feature
of the marked centers, or additional source-port transport along the rooted
paths `P_i`.  This identifies exactly what the self-indexed line-cycle
compression supplies and what parity information it discards.

## 61. Alternating signs retain the run parity at the boundary

Over a signed coefficient group, rather than characteristic two, there is a
minimal refinement of (203).  With the same indexing, define

```text
Delta_alt(P) := sum_(i=1)^ell (-1)^(i-1) delta_i.
```

The internal labels again cancel, but the signs at the far boundary remember
the parity of the run:

```text
Delta_alt(P)
  = ([p_1]-[p_0]) + (-1)^ell([p_ell]-[p_(ell+1)]).     (204)
```

Thus the two inward boundary differences occur with the same coefficient
for an even run and opposite coefficients for an odd run (with the displayed
convention).  If the reversed run is reindexed starting again with sign
`+1`, its alternating sum is `(-1)^ell Delta_alt(P)`; this dependence on the
choice of initial phase is exactly the parity datum, not an orientation-free
edge label.

This parity signal disappears after reduction modulo two, which explains
why the binary unweighted curl and the collision statistic were blind to the
one-edge terminal.  But (204) provides a concrete signed interface: attach
alternating signs along every monochromatic owner run and compare its two
oriented boundary edges through the rooted transition paths.  On the odd
projected cycle `C`, a globally consistent alternating sign assignment is
itself impossible without one sign defect.  A closing theorem can therefore
take either of two equivalent forms:

```text
the rooted transition transport preserves the signed B-boundary orientation,
or
every sign defect contributes a nonzero conserved private-port class.     (205)
```

Equation (204) alone proves neither alternative in (205); the missing input
is still the transport of actual source ports through `P_i`.  It does,
however, identify the exact signed quantity that transport must preserve and
the exact place where odd run length enters.  This is compatible with the
dyadic signed-terminal strategy: no division or arbitrary real price is
needed, only coefficients `+1` and `-1` on consecutive marked centers.

## 62. Rooted transition paths lift from private port to private port

Fix a genuine owner change at a root `x`.  Let the incoming `A_c` edge have
owner `f` and shared owner port `s_f`, and let the outgoing edge have owner
`e` and shared owner port `s_e`.  Write the other members of the two fibers
at `x` as

```text
Y_f(x) = {s_f,r_f},    Y_e(x) = {s_e,r_e}.             (206)
```

The endpoint triangle of the rooted transition path `P_x : f --> e` uses
`r_f`, not `s_f`.  Indeed, if its other exterior port were `y` and the
triangle used `s_f`, then `x-y-s_f-x_prev-x` would be an ambient four-cycle,
where `x_prev` is the other root of the incoming edge.  Symmetrically, the
last triangle of `P_x` uses `r_e`, not `s_e`.

At every intermediate color `d` of `P_x`, its two incident rooted triangles
use the two distinct members of `Y_d(x)`.  They cannot use one member twice:
that port and `x` would then be two common neighbors of the two opposite
exterior ports.  Equivalently, this is the port bijection (60) applied to
the vertical degree-two state.

Consequently `P_x` has a canonical actual-port lift

```text
r_f -- triangle -- (port in d_1)
    -- fiber switch -- (other port in d_1)
    -- triangle -- ... -- triangle -- r_e,            (207)
```

where a fiber switch joins the two members of `Y_d(x)` as a formal matching
edge.  The lift is a path: the color path is simple by Section 43, and its
two ports in every intermediate component are distinct.  Reversing `P_x`
reverses (207).

Thus the two signed boundary differences meeting at `x` are

```text
[s_f]-[r_f]    and    [s_e]-[r_e],                    (208)
```

and (207) canonically transports their **private** endpoints.  The shared
endpoints remain attached to the two horizontal edges.  The missing local
statement in (205) is now precise: assign signs to the formal fiber switches
in (207) so that transport from `[s_f]-[r_f]` to `[s_e]-[r_e]` preserves the
boundary phase.  No choice of target port remains.  Proving that statement
from the simultaneous cross-factor equations would make the alternating
defects telescope around `C`; disproving it requires a root-local
countermodel preserving the entire lifted path (207), not merely its color
sequence.

## 63. The projected odd cycle gives a closed odd port-switch walk

Complete the lift (207) at a genuine owner change by adding the two endpoint
fiber switches

```text
s_f -- r_f    and    r_e -- s_e.                       (209)
```

If `k=|P_x|>0`, the resulting handoff from the incoming shared port `s_f` to
the outgoing shared port `s_e` has

```text
k triangle edges + (k+1) fiber switches = 2k+1 edges. (210)
```

If there is no owner change, `P_x` has length zero and the two shared ports
are simply the two members of the common owner fiber `Y_e(x)`; define the
handoff to be their single fiber switch.  Thus (210), with `k=0`, holds at
every root of `C`.

The outgoing shared port at `x_i` is the same actual exterior vertex as the
incoming shared port at `x_(i+1)`: it is the unique owner port of the
horizontal edge `x_i x_(i+1)`.  Hence all root handoffs concatenate
canonically to a closed walk `Lambda_C` in the auxiliary port-switch graph,
whose edges are rooted triangle edges and formal two-point fiber switches.
Using (152), its length is

```text
|Lambda_C| = sum_i (2|P_i|+1)
           = |C| + 2V(Omega)
           = 1  (mod 2).                               (211)
```

This packages the signed phase defect without choosing an initial phase:
`Lambda_C` is an explicit closed odd walk.  Equivalently, alternating signs
can be propagated along every local lift, but return with the opposite sign
after one circuit.

Equation (211) is not by itself a contradiction, because the fiber switches
are formal edges and the resulting auxiliary graph has not been proved
bipartite.  It isolates the remaining simultaneous invariant exactly:

```text
the port-switch graph generated by the rooted lifts of an admissible
size-two routing cycle is bipartite (equivalently, admits a switch sign). (212)
```

If (212) follows from the simultaneous owner-factor equations, (211) closes
the nonbipartite branch immediately.  Conversely, a counterexample to the
signed strategy must realize an odd cycle of actual triangle edges and
two-point fiber switches while preserving all reused cross blocks; a
color-only or pairwise-SRP model cannot decide (212).  The alternating
boundary identity (204) is the runwise contraction of this same odd walk.

## 64. Port-switch expansion is equivalent to the state cocycle

The construction of `Lambda_C` should not be mistaken for an independent
parity contradiction.  It is the canonical two-port expansion of the state
cycle `Omega`: replace every active state by the switch joining its two
ports, realize every vertical state edge by its triangle edge, and contract
every horizontal state edge because its two endpoint ports are the same
actual vertex.  A state cycle with `H` horizontal and `V` vertical edges
therefore becomes a port-switch closed walk of length

```text
H + 2V == H  (mod 2).                                  (213)
```

In particular, a two-coloring of the relevant port-switch graph pulls back
to the state potential (57), and a state potential pushes forward to a
consistent sign on each occurrence in the expanded walk.  For the selected
cycle, (212) is therefore the port-resolved form of the same signed
alternative, not a theorem supplied by local C4-freeness.  The q=10
single-pair model of Section 16 already gives an all-switch odd cycle and
shows that this implication fails without simultaneous reuse.

The value of (211) is instead that it identifies the data the transport
branch must add: a sign must be forced on the **actual two-point fiber
switches**, compatibly when the same port occurs at its two roots.  The
clean-core capacity system records exactly those root--fiber incidences,
whereas a color potential or collision scalar does not.  Thus the remaining
route to (212) must combine the once-paid collision statistic with a
root-own versus external fiber-incidence flag (or an equivalent private-port
orientation).  This keeps the signed-mode and transport-mode sides of the
dispatcher logically separate.

## 65. Full port-occurrence collision splits into horizontal and vertical parts

Before contracting the horizontal transitions, retain the two port
occurrences at every state of `Omega`.  There are `2(H+V)` occurrences in
total.  Map each occurrence to its actual exterior port vertex and let

```text
kappa_all(Omega) := sum_z binom(load_Omega(z),2).       (214)
```

Every load is at most two, because an exterior port has exactly two
neighbors in the root component `c`.  A load-two port has exactly two
possible forms.

* If it is used horizontally at either root, it is the unique common owner
  port of those two roots.  The horizontal state edge uses it at both ends,
  and the port bijection prevents either occurrence from being vertical.
* Otherwise both occurrences are used by vertical triangle edges at the two
  roots.  This is a genuine repeated vertical target/source port.

Conversely every horizontal edge contributes its shared port with load two,
and every vertically repeated port contributes one load-two vertex.  The
two classes are disjoint.  If `kappa_vert(Omega)` counts the second class,
then

```text
kappa_all(Omega) = H(Omega) + kappa_vert(Omega).        (215)
```

Equivalently, if `Z_all(Omega)` is the set of actual ports used by the
expanded state cycle, then

```text
|Z_all(Omega)|
  = 2(H+V) - kappa_all(Omega)
  = H + 2V - kappa_vert(Omega).                         (216)
```

This explains why the clean target-collision statistic alone was blind to
the one-edge terminal: there `kappa_vert=0`, but the shared horizontal port
still contributes one unit to `kappa_all`.  The horizontal parity problem
can now be written

```text
H == kappa_all - kappa_vert  (mod 2).                   (217)
```

Thus the transport analogue of the all-color collision feature must count
**all root--port occurrences**, including the root-own shared labels, and
then separate its horizontal and vertical strata by the incidence flag.
Sections 53--56 control the vertical repeated-target term; the missing
root-incidence constraint is precisely what is needed to control their
difference in (217).  This is a collision formulation of the same switch
sign problem, but unlike target-only capacity it retains isolated owner
edges.

## 66. Full collision is the degree-two mass of a common-edge graph

Now take all cycles of `Gamma_c`, not only the selected `Omega`, and fix an
exterior color `d`.  Let

```text
I_d := {x in c : b_xd=1}
```

be its inactive roots.  A port `z in d` labels one edge `xx'` of the owner
factor `F_d[c]`; its two root occurrences are both active exactly when
`x,x'` both lie outside `I_d`.  Therefore the color-`d` part of the full
occurrence collision is

```text
kappa_all(d) = |E(F_d[c][c setminus I_d])|.             (218)
```

The owner factor is two-regular on the even-order component `c`.  Degree
summation across `I_d` gives

```text
kappa_all(d)
  = |c| - 2|I_d| + |E(F_d[c][I_d])|
  == |E(F_d[c][I_d])|  (mod 2).                         (219)
```

There is a symmetric interpretation inside component `d`.  Recall that
`B_dc` is the line-cycle on the `d`-ports: its edge labelled by a root `x`
joins the two members of `Y_d(x)`.  By definition,

```text
x in I_d  <=>  the B_dc edge labelled x also lies in A_d.
```

Put `K_dc:=A_d cap B_dc`.  Two inactive roots `x,x'` are adjacent in
`F_d[c]` exactly when their two common `B_dc` edges meet at the port which
labels `xx'`.  Hence

```text
|E(F_d[c][I_d])|
  = #{z in d : deg_(K_dc)(z)=2}.                        (220)
```

Combining (219)--(220),

```text
kappa_all(d)
  == #{degree-two vertices of A_d cap B_dc}  (mod 2).  (221)
```

Thus the all-occurrence collision feature is not an arbitrary transport
statistic.  It is exactly the parity of the internal vertices of the
common-edge path--cycle graph of the two self-indexed factors on `d`.
Summing (221) over exterior colors translates the collision/incidence
formulation of Section 65 back into the signed-support object studied at the
start of this audit.  The signed branch controls (221) by a global sign;
the transport branch must control the same degree-two mass using the rooted
capacity and incidence strata instead.  This is the precise bridge between
the two sides of the dispatcher.

## 67. The vertical collision error has the same radius-two bound

Return to the selected state cycle `Omega`, whose projected root cycle `C`
has order `n=H>=5` (an internal `C3` edge would have both the third root and
its owner port as common neighbors).  A vertically repeated port `z` is adjacent to two roots
`x,x'` of `C`, so it labels the owner-factor edge `xx'`.  The two roots
cannot have cyclic distance one: their `A_c` edge already has its horizontal
owner port as a common neighbor.  They cannot have distance two: their
middle root is already a common neighbor in `A_c`.  Thus every vertical
collision determines a root pair at cyclic distance at least three.

Two distinct repeated ports cannot determine the same pair, since those
ports would be two common neighbors of `x,x'`.  Therefore the assignment is
injective into the nonedges of the square of `C`, and

```text
kappa_vert(Omega) <= n(n-5)/2.                          (222)
```

This is the cycle version of the collision injection in Sections 49 and 53,
but it needs no clean-color restriction: it counts the actual vertical port
occurrences of `Omega` itself.  Combining (215) and (222) gives the exact
pinch

```text
H <= kappa_all(Omega) <= H + H(H-5)/2.                  (223)
```

In particular, when the projected root cycle is a `C5`,

```text
kappa_vert(Omega)=0,    kappa_all(Omega)=H=5.           (224)
```

So the smallest mixed obstruction has no vertical collision error at all:
its full collision mass is entirely the five horizontal shared-owner ports.
For larger root cycles, (222) quantifies exactly how far the all-occurrence
feature can drift from the desired horizontal count.  Any incidence-weighted
transport inequality strong enough to improve (222) to an even correction
would settle the parity problem through (217).

## 68. Vertical collision is an exact owner-factor cut deficit

For each exterior color `d`, let

```text
X_d(Omega) := {x in C : the state (x,d) lies on Omega},
v_d(Omega) := number of vertical edges of Omega incident with color d.
```

Every port used by `Omega` at a state `(x,d)` labels one `F_d[c]` edge
incident with `x`.  The `d`-port incidences used vertically have exactly two
forms:

* an `F_d[c]` edge with both endpoints in `X_d` but not used horizontally;
  its port occurs on two vertical edges and contributes one to
  `kappa_vert(d)`;
* an `F_d[c]` cut edge of `X_d`; its port occurs vertically at the unique
  endpoint state lying on `Omega`.

If both endpoints lie in `X_d` and their state edge is horizontal, the port
is instead one of the `2h_d` horizontal incidences and contributes to neither
class.  The port bijection makes the preceding partition exhaustive.  Hence

```text
v_d(Omega)
  = 2 kappa_vert(d;Omega) + |delta_(F_d[c])(X_d)|.      (225)
```

Equivalently, writing `h_d` for the number of horizontal color-`d` edges,

```text
kappa_vert(d;Omega)
  = |E(F_d[c][X_d])| - h_d.                            (226)
```

Indeed, every induced owner-factor edge supplies a load-two port, split
uniquely into the horizontal and vertically repeated classes.  Summing
(225) over colors and using `sum_d v_d=2V` gives

```text
kappa_vert(Omega)
  = V - (1/2) sum_d |delta_(F_d[c])(X_d)|.             (227)
```

Every displayed cut has even cardinality because `F_d[c]` is two-regular,
so the half-sum is integral.  More sharply,

```text
kappa_vert(Omega) is even
  <=> sum_d |delta_(F_d[c])(X_d)| == 2V  (mod 4).      (228)
```

Thus the missing parity is not obtained by observing that every collision
has two preimages; that fact is already the coefficient two in (225).  What
is needed is a genuine mod-four congruence for the simultaneous owner-factor
cuts of the color supports `X_d`.  The rooted transition paths determine
those supports, while the clean-core capacity controls their repeated
internal ports.  Equation (228) is the exact cut form in which the two data
sets must be combined.

## 69. Vertical collisions are the path-rank drop from state runs to owner factors

Let `H_d(Omega)` be the horizontal color-`d` subgraph on `X_d`: its edges
are the horizontal edges of `Omega` owned by `d`.  It is a subgraph of the
induced owner factor `F_d[c][X_d]`.  Degree summation in the state cycle and
in the owner factor gives, respectively,

```text
|X_d| - |E(H_d)|             = v_d/2,
|X_d| - |E(F_d[c][X_d])|     = |delta_F(X_d)|/2.        (229)
```

Subtracting the two identities and using (226),

```text
kappa_vert(d;Omega)
  = (|X_d|-|E(H_d)|)
    - (|X_d|-|E(F_d[c][X_d])|).                        (230)
```

For an induced subgraph of a two-factor, `|V|-|E|` is the number of path
components, counting isolated vertices as paths and counting a full cycle
as zero.  Thus `v_d/2` counts the horizontal state-run components of color
`d` (including isolated intermediate appearances), while
`|delta_F(X_d)|/2` counts the path components cut out by the same root set
inside the owner factor.  Each vertically repeated port is precisely one
additional owner-factor edge beyond `H_d`; adding it either merges two path
components or closes one path into a cycle.  Equation (230) says all such
rank drops are counted once.

Consequently the desired parity can also be stated as

```text
sum_d pathrank(H_d) == sum_d pathrank(F_d[c][X_d])  (mod 2). (231)
```

This component form is equivalent to the mod-four cut congruence (228), but
it exposes the required involution more concretely: pair the owner chords
which merge or close the rooted state-run components.  A pairing of their
two endpoint occurrences is insufficient; the pairing must act on these
component-changing chords themselves.

## 70. A `C7` rooted counterprofile to cut parity without simultaneous reuse

The congruence (228) is not a consequence of the owner word, rooted path
lengths, and radius-two exclusion alone.  Label a projected `C7` by
`x_0,...,x_6`.  Give the first three consecutive edges owner `e` and the
remaining four owner `f`, so the two change roots are `x_0` and `x_3`.
Take both rooted transition paths to be the single vertical edge `e--f`.
Then

```text
X_e = {x_0,x_1,x_2,x_3},   h_e=3,   v_e=2,
X_f = {x_0,x_3,x_4,x_5,x_6}, h_f=4, v_f=2.             (232)
```

On `X_e`, let `F_e[c]` contain the three run edges and the allowed
distance-three chord `x_0x_3`.  Thus `F_e[c][X_e]` is a four-cycle,
its cut is empty, and the chord port is used vertically at both change
roots:

```text
kappa_vert(e)=1,    |delta_(F_e[c])(X_e)|=0.           (233)
```

On `X_f`, retain only its four run edges and let the other owner-factor edge
at each boundary root leave `X_f`.  Then

```text
kappa_vert(f)=0,    |delta_(F_f[c])(X_f)|=2.           (234)
```

The partial factors extend abstractly to two-factors by continuing the two
`f` boundary edges through distinct unused roots and then completing the
remaining paths; the `e` restriction is already a cycle.  This only uses two
roots outside `C`, available in the uniform binary range `q>=8` considered
here.  Equations (225)--(227) hold exactly:

```text
2+2 = 2(1) + (0+2),
kappa_vert = V - (0+2)/2 = 2-1 = 1.                   (235)
```

The only added chord has cyclic distance three, so the radius-two exclusion
is respected.  At the two changes, its single port can serve the `e` side of
both direct transitions, while distinct cut ports serve the `f` sides.

This is deliberately a **rooted owner-factor counterprofile**, not a full
ambient graph or an SRP realization: the remaining cross blocks, internal
factors, and other colors have not been supplied.  Its conclusion is exact
at that scope.  The mod-four target (228), and hence evenness of
`kappa_vert`, cannot be proved from the cyclic owner word plus the local
transition paths and C4 radius exclusions.  A successful proof must use the
simultaneous reuse equations to forbid or pair precisely this distance-three
owner chord.  The reproducer
`verify_c7_vertical_collision_counterprofile.py` checks the displayed local
incidences, the cut/collision ledger, and maximum codegree one of the corrected
skeleton with distinct outside roots.

## 71. A closing chord on a three-edge run saturates the clean interface

The counterprofile identifies a general terminal inside an actual routing
system.  Let `P=x_0x_1x_2x_3` be a maximal three-edge run owned by `e`, and
suppose the two private `e`-ports at its boundary roots coincide.  Call the
common port `z`.  Since a port labels its pair of `c`-neighbors, this is
equivalent to

```text
x_0x_3 in E(F_e[c]).                                   (236)
```

Among the six pairs of the four roots, the three run edges have distance
one, the two pairs `x_0x_2,x_1x_3` have distance two, and `x_0x_3` is the
only remaining pair.  The radius-two argument excludes every third-owner
edge on the first five pairs, while (236) and exclusivity of pair ownership
exclude a third owner on the last pair.  Hence

```text
every third color d != c,e is P-clean.                 (237)
```

Moreover, any target port repeated by two rooted assignments over `U` pins
a distance-at-least-three root pair.  There is only the pair `x_0x_3`, and
two different repeated ports on that pair would form a four-cycle.  Thus
`z` is the unique possible repeated target; when it is used by both boundary
transitions,

```text
kappa_vert(P)=1,
every other clean target over U has multiplicity one.  (238)
```

Because (237) removes all nonclean leakage, clean--clean transpose
cancellation leaves only the two boundary assignments into the run owner
`e`.  Under (238), both have the same actual target port:

```text
clean source at x_0 --> z <-- clean source at x_3.     (239)
```

This is complementary to the one-edge terminal (197): there the two owner
targets are forced distinct private ports, while a three-edge closing chord
forces them to be one common private port and simultaneously makes the
entire third-color interface clean.  Any price depending only on the target
port cancels on (239); the sole surviving obstruction is the difference of
the two **root-incidence** evaluations at the same port `z`.  Therefore an
SRP proof need not forbid the closing chord outright.  It is enough to show
that the incidence-aware transport assigns equal phase to the two
occurrences of a repeated port.  The Section-70 profile demonstrates that
this equality is not supplied by rooted owner factors alone.

## 72. Complementary gaps canonically pair all owner-boundary ports

Fix an owner color `e` and retain the marked set `M_e` of Section 59 inside
the line-cycle factor `B_ec`.  Two marked vertices are consecutive in
`B_ec` exactly when their labelled `F_e[c]` edges share a root; when both
are projected `A_c` edges, they are consecutive edges of `C`.  Therefore
the maximal marked blocks of `M_e` on the `B_ec` cycles are exactly the
maximal `e`-runs of the owner word (with a fully marked `B_ec` cycle giving
the closed-run case).

For a proper marked block

```text
p_1, ..., p_ell,
```

its two private boundary targets are the adjacent unmarked vertices
`p_0,p_(ell+1)`, as in (201).  Now decompose the complement of `M_e` on each
`B_ec` cycle into maximal unmarked gaps.  A vertex `z` occurs in the
multiset of all `e`-run boundary targets with multiplicity

```text
deg_(B_ec)(z,M_e) in {0,1,2}.                           (240)
```

Consequently:

* a one-vertex unmarked gap has two marked neighbors, so the same target
  occurs twice and cancels in the mod-two boundary;
* an unmarked gap of order at least two has exactly two vertices with one
  marked neighbor, namely its two endpoints; these are distinct and are
  canonically paired by the gap;
* all internal gap vertices have multiplicity zero.

Thus, after identifying repeated occurrences of one actual port, every
surviving distinct owner-boundary target belongs to a fixed-point-free
involution: pair the two endpoints of its complementary unmarked `B_ec`
gap.  There are no unmatched targets.  In symbols, if `L_e` is the boundary
target multiset over all proper `e`-runs, then

```text
L_e mod 2
  = disjoint union of endpoint pairs of unmarked B_ec gaps of order >=2.
                                                                  (241)
```

The two short terminals are the extreme cases of (241).  The three-edge
closing chord of Section 71 is a marked block whose complementary gap has
one vertex `z`, producing the doubled target in (239).  A one-edge run has
distinct `B_ec` neighbors by Section 58, so its two targets are the endpoint
pair of a nontrivial complementary gap (possibly shared with the boundary
of other marked blocks on that cycle).

Equation (241) supplies the **combinatorial involution** missing from the
target-only capacity count and is directly analogous to the complementary
nonedge matching in the Baer lane.  It does not yet supply equal prices at
the paired endpoints.  The remaining transport statement is now narrower:
phase must propagate across each unmarked `B_ec` gap.  Singleton gaps need
no propagation because their two occurrences are already the same port;
only gaps of order at least two carry a distinct-port residue.

## 73. SRP transports an oriented fiber difference across one gap step

The required single-step propagation has an exact linear identity.  Let
`u,v` be consecutive `B_ec` ports, so `Y_e(x)={u,v}` for the root labelling
their `B_ec` edge.  Orient the fiber difference

```text
w_(x,e) := 1_u - 1_v  in Z^e.
```

Each port has one other neighbor in `c`; call them `x_u,x_v`.  The common
root cancels with opposite signs, giving

```text
R_ce w_(x,e) = 1_(x_u) - 1_(x_v).                     (242)
```

Also `J w_(x,e)=0`.  Apply the simultaneous routing partition `(SRP)` to
this zero-sum column.  One obtains the signed single-switch identity

```text
A_c(1_(x_u)-1_(x_v))
  + R_ce A_e(1_u-1_v)
  + sum_(d != c,e) R_cd R_de(1_u-1_v)
  = 0.                                                  (243)
```

No parity or positivity has been discarded in (243); it is an equality of
integer vectors.  The first term transports the difference through the two
other roots, the second through the internal `A_e` factor, and the remaining
terms through every reused third-color block.  A pairwise model can balance
the first two terms incorrectly because it does not have to realize the
fixed third-color sum.

Now orient an unmarked gap of order `g>=2` as

```text
p_0, p_1, ..., p_(g-1).
```

Sum (243) over its `g-1` consecutive `B_ec` edges using
`w_i=1_(p_i)-1_(p_(i+1))`.  The input differences telescope:

```text
sum_i w_i = 1_(p_0)-1_(p_(g-1)).                       (244)
```

By linearity, the entire SRP transport of the gap is therefore the image of
its paired endpoint difference under the same three families of operators.
Equation (244) is the algebraic form of the complementary-gap involution
(241).

The remaining phase theorem is now a precise separation statement, not an
undefined sign choice: construct a signed functional from the clean
capacity/incidence dual whose pullback through one displayed transport is
the desired endpoint price, while its evaluations on the other transported
terms cancel.  Pairing (243) with that functional then gives zero on the
endpoint difference (244), so every complementary-gap pair cancels.
Conversely, any obstruction must exhibit which endpoint or third-color term
prevents this separation.  This is the minimal SRP-local equation unavailable
to the rooted owner-factor counterprofile of Section 70.

## 74. The one-edge root indicator kills both endpoint transports

For the one-edge run of Section 58, write `U={x_-,x_+}` and retain the
shared/private notation

```text
Y_e(x_-)={p,p_-},    Y_e(x_+)={p,p_+}.
```

Let `w=1_(p_-)-1_(p_+)` and pair `SRP(c,e)w=0` with the root indicator
`1_U`.  The first endpoint term vanishes:

```text
1_U^T A_c R_ce w = 0.                                  (245)
```

To see this, let `a_-` and `a_+` be the other `c`-neighbors of `p_-` and
`p_+`.  Then

```text
R_ce w = (1_(x_-)+1_(a_-))-(1_(x_+)+1_(a_+)).
```

The contributions of `x_-` and `x_+` to `1_U^T A_c` cancel.  Neither
`a_-` nor `a_+` is adjacent in `A_c` to a root of `U`: equality with the
opposite root would duplicate the shared port `p`; equality with the outer
cycle neighbor would make the boundary edge `e`-owned, contradicting run
maximality; adjacency at cyclic distance two would give the middle root and
the private port as two common neighbors.  This proves (245).

The reverse endpoint term also vanishes:

```text
1_U^T R_ce A_e w = 0.                                  (246)
```

Indeed,

```text
R_ec 1_U = 2 1_p + 1_(p_-) + 1_(p_+).
```

The last two terms pair to zero with `A_e(1_(p_-)-1_(p_+))` by symmetry of
`A_e`.  The `p` term is zero because the rooted budgets at both endpoints
have `a=1,b=0`, so neither `pp_-` nor `pp_+` is an `A_e` edge.

Pairing (243) with `1_U` therefore leaves the exact third-color balance

```text
sum_(d != c,e) 1_U^T R_cd R_de 1_(p_-)
  =
sum_(d != c,e) 1_U^T R_cd R_de 1_(p_+).                (247)
```

Both sides equal one.  At `x_-`, the pair `(x_-,p_-)` lies in neither
endpoint layer by the preceding arguments, so the SRP partition routes it
through its unique third color; at `x_+`, the source-endpoint layer reaches
`p_-` through the run edge and contributes there instead.  The roles reverse
for `p_+`.  Thus (247) is exactly equality of the two boundary assignments'
total third-color mass, not merely equality of two unconstrained column
sums.

This is the first explicit functional requested after (244): the root
indicator annihilates both endpoint transports and isolates the clean
third-color routing balance.  It still sums over the source color, so it
does not force equality for a dual price which distinguishes the two rooted
transition paths.  The remaining refinement is to split `1_U` by the
clean-color/root-incidence coordinates while preserving the cancellations
(245)--(246).

## 75. Unequal root weights recover only the run-edge defect

The most immediate attempted refinement of (247) cannot distinguish the
two route colors.  Put

```text
lambda = alpha 1_(x_-) + beta 1_(x_+).
```

The exclusions used in (245) are entrywise for the other roots `a_-` and
`a_+`.  Only the run edge `x_-x_+` remains, and hence

```text
lambda^T A_c R_ce w = beta-alpha.                       (248)
```

The reverse endpoint term is still zero for arbitrary `alpha,beta`.  Indeed,

```text
R_ec lambda
  = (alpha+beta)1_p + alpha 1_(p_-) + beta 1_(p_+).
```

The `p` contribution vanishes because `pp_-` and `pp_+` are absent from
`A_e`.  Moreover `p_-` and `p_+` both lie in the closed `B_ec`-neighborhood
of the marked center `p`, so Section 59 gives `p_-p_+` absent from `A_e` as
well.  Thus

```text
lambda^T R_ce A_e w = 0.                                (249)
```

Pairing (243) with `lambda` now yields

```text
sum_(d != c,e) lambda^T R_cd R_de 1_(p_-)
  - sum_(d != c,e) lambda^T R_cd R_de 1_(p_+)
  = alpha-beta.                                         (250)
```

But the location statement following (247) says that the first third-color
sum has its unique unit at `x_-`, whereas the second has its unique unit at
`x_+`.  Their weighted values are therefore already `alpha` and `beta`.
Consequently (250) is an identity, not a new constraint on the two unique
third colors.

This closes the diagonal root-reweighting branch: equal weights give the
color-blind balance (247), and unequal weights expose exactly the run-edge
cross term that reproduces the chosen weight difference.  A genuine
color-incidence refinement must therefore use a functional outside
`span{1_(x_-),1_(x_+)}` (or couple several gap steps so that their run-edge
defects cancel); merely reweighting the two roots cannot identify or pair
their route colors.

## 76. Boundary localization forces a two-periodic mark profile

There is an exact uniqueness statement behind the alternating profile of
Section 61.  For a run written as in (201), give its edge marks arbitrary
scalar coefficients `gamma_1,...,gamma_ell` and put

```text
Delta_gamma := sum_(i=1)^ell gamma_i delta_i.
```

For every deep interior label `p_j`, with `2 <= j <= ell-1`, its coefficient
in `Delta_gamma` is

```text
gamma_(j-1) - gamma_(j+1).                             (251)
```

Consequently `Delta_gamma` is supported only on the two labels nearest each
boundary if and only if

```text
gamma_(i+2) = gamma_i       for 1 <= i <= ell-2.       (252)
```

Thus every boundary-local profile is two-periodic: all odd-indexed marks
have one coefficient `gamma_odd` and all even-indexed marks have one
coefficient `gamma_even`.  The diagonal choice
`gamma_odd=gamma_even` is precisely the unweighted, parity-blind mode (203).
The anti-diagonal choice `gamma_even=-gamma_odd` is precisely the alternating
mode (204).  Over a coefficient ring in which `2` is invertible these two
modes span the full boundary-local space.  Integrally, (252) is the sharper
lattice statement and requires no division.

In particular, if the coefficients are restricted to signs and the profile
is not constant, then (252) forces the alternating profile up to a global
sign.  Hence (204) is the unique sign-valued boundary localization that can
retain run parity; every other sign choice leaves an interior port label.
Combined with Section 75, this removes arbitrary diagonal choices from the
remaining search.  Any closing functional using only boundary-local signed
marks has the fixed alternating root phase, and all additional information
must enter through off-diagonal roots, actual source ports, or color-specific
transport.

## 77. The paired other-root functional exposes four outward adjacencies

Section 75 points to the other roots `a_-` and `a_+` as the smallest
off-diagonal enlargement.  Let `q_-` be the other member of `Y_e(a_-)`
besides `p_-`, and define `q_+` similarly.  Use the multiplicity-sensitive
test vector

```text
mu := 1_(a_-) + 1_(a_+).
```

(Thus `mu=2 1_a` if the two other roots coincide.)  The source-endpoint
term again vanishes:

```text
mu^T A_c R_ce w = 0.                                  (253)
```

Indeed, Section 74 proved entrywise that neither `a_-` nor `a_+` is adjacent
in `A_c` to either run root.  In the remaining difference
`1_(a_-)-1_(a_+)`, the possible cross-edge `a_-a_+` contributes once with
each sign and cancels by symmetry; this also covers the coincident-root
case.

On the reverse endpoint side,

```text
R_ec mu = 1_(p_-)+1_(q_-)+1_(p_+)+1_(q_+).
```

The `p_-` and `p_+` rows cancel against
`w=1_(p_-)-1_(p_+)` by symmetry of `A_e`.  Therefore the entire endpoint
residue is the explicit four-entry quantity

```text
epsilon_e
  := A_e(q_-,p_-) - A_e(q_-,p_+)
   + A_e(q_+,p_-) - A_e(q_+,p_+),

mu^T R_ce A_e w = epsilon_e.                          (254)
```

Pairing (243) with `mu` gives the first non-diagonal third-color identity

```text
sum_(d != c,e) mu^T R_cd R_de 1_(p_-)
  - sum_(d != c,e) mu^T R_cd R_de 1_(p_+)
  = -epsilon_e.                                       (255)
```

Unlike (250), this is not determined by the two known boundary units at
`x_-` and `x_+`: it samples third-color routing at the outward roots.  The
same-fiber entries in (254) have a direct owner interpretation.
Specifically, `A_e(q_-,p_-)=b_(a_-,e)` and
`A_e(q_+,p_+)=b_(a_+,e)` are the two rooted fiber-switch bits.  Since the
edges labelled `p_-` and `p_+` are unmarked, the corresponding owner counts
are at most one, and the rooted budgets constrain these bits together with
the outward vertical demands.  The two crossed entries are the remaining
uncontrolled terms.

Thus the one-edge terminal has been reduced to a four-bit outward residue,
not closed outright.  A C4 exclusion or complementary-gap pairing that
controls the crossed entries `A_e(q_-,p_+)` and `A_e(q_+,p_-)` would turn
(255) into an owner-boundary equation.  This is strictly beyond diagonal
root reweighting and gives a concrete local target for the port-side
enrichment.

## 78. Equality types reduce the outward residue to finite patterns

The four entries in (254) have only three equality types.  First,

```text
a_- = a_+
  iff q_- = p_+
  iff q_+ = p_-.                                      (256)
```

For example, if the roots coincide, their two-element `e`-fiber is
`{p_-,p_+}`, giving both port equalities.  Conversely, `q_-=p_+` makes
`a_-` a `c`-neighbor of `p_+`.  It cannot be the run root `x_+` by the
duplicate-shared-port exclusion in Section 74, so it is the other root
`a_+`; the other implication is symmetric.  In this coincident-root case,
substitution in (254) gives

```text
epsilon_e = 0.                                        (257)
```

Suppose next that `a_- != a_+` but `q_-=q_+=q`.  All equalities between a
`q`-port and the opposite private port have already been excluded by (256),
and (254) collapses to

```text
epsilon_e = 2(A_e(q,p_-)-A_e(q,p_+)) in {-2,0,2}.     (258)
```

Finally suppose `q_- != q_+` as well.  Then the four ports
`p_-,p_+,q_-,q_+` are distinct.  The four bits in (254) cannot all equal
one, since they would form the `A_e` four-cycle

```text
q_- -- p_- -- q_+ -- p_+ -- q_-.
```

Thus this last branch has at most fifteen raw four-bit patterns, with

```text
epsilon_e in {-2,-1,0,1,2},
epsilon_e == number of the four displayed A_e edges  (mod 2).   (259)
```

Equations (257)--(259) are a finite normal form, not yet a parity kill.  They
show exactly where an odd residue can occur: only in the four-distinct-port
branch, and only when the induced four-edge interface has odd size.  By
(255), any odd outward third-color imbalance therefore certifies that same
odd interface.  The remaining local question is now whether the rooted
budgets and transpose routing force this interface size even; neither the
coincident-root nor shared-outward-port branch can carry the desired odd
obstruction.

## 79. An odd outward residue propagates through the owner two-factor

In the four-distinct-port branch of Section 78, put

```text
P := {p_-,p_+},    Q := {q_-,q_+},
O := e \ (P union Q).
```

The pair `P` is independent in `A_e` by (200), and every `A_e` degree is
two.  Summing degrees over `P` gives

```text
4 = e_(A_e)(P,Q) + e_(A_e)(P,O).
```

Summing over `Q` allows the possible internal edge `q_-q_+` and gives

```text
4 = e_(A_e)(P,Q) + 2 e_(A_e)(Q) + e_(A_e)(Q,O).
```

Together with (259), reduction modulo two yields the exact port-current law

```text
epsilon_e
  == e_(A_e)(P,Q)
  == e_(A_e)(P,O)
  == e_(A_e)(Q,O)                    (mod 2).          (260)
```

Thus an odd residue in (255) cannot terminate on the four displayed ports:
an odd number of owner-factor edges exits `P` and an odd number exits `Q`.
Conversely, either even exit count forces even `epsilon_e`.  This is a
genuine propagation statement supplied solely by the two-regularity of
`A_e`; no assumption about the individual four-bit pattern is needed.

Equation (260) converts the remaining local obstruction into a port-side
current.  Following its exit edges along the `A_e` cycles cannot create an
endpoint, so any odd one-edge residue must continue to another marked
interface or close through unmarked ports.  The missing global step is now
sharply stated: show that the alternating `B_ec` boundary phase of Section
76 pairs these `A_e` current handoffs.  If so, odd currents occur in pairs,
and (255) supplies the required even boundary contribution.

## 80. Radius-two C4 constraints do not kill the odd interfaces

The finite local check suggested after (259) has a sharp negative answer.
Take the nine distinct vertices

```text
x_-, x_+, a_-, a_+, p, p_-, p_+, q_-, q_+
```

and include exactly the forced run edge and `c`--`e` incidences used in
Sections 74 and 77.  Exhaust the four optional `A_e` interface edges from
(254), rejecting a pattern whenever two vertices acquire two common
neighbors.  Of the sixteen patterns, exactly fifteen remain `C4`-free on
this known local skeleton.  The sole rejection is `1111`, witnessed by the
four-cycle in Section 78.  In particular, all eight odd-size patterns
survive.

The exhaustive reproducer is

```text
python3 research/problems/erdos-85-wip-01/verify_one_edge_outward_interface.py
```

and reports

```text
excluded=1111 witness=('p-', 'p+', ['q-', 'q+'])
admissible=15 odd_admissible=8
```

This is deliberately a local-profile no-go, not an ambient realization of
the full simultaneous routing system.  It proves that the already recorded
radius-two adjacencies plus `C4`-freeness cannot force the interface parity
in (259).  Any successful evenness proof must use information absent from
that skeleton: the rooted budgets, third-color transpose coupling, or the
global `A_e` current continuation (260).  Thus Section 79 is not optional
bookkeeping; it is the first surviving route beyond the complete local
pattern audit.

## 81. Owner-cycle compression turns odd current into a mixed gap path

Fix one four-distinct interface and its partition `P,Q,O` from Section 79.
On every cycle of the two-factor `A_e`, delete the vertices in `P union Q`.
Each remaining nonempty component is an `O`-path whose two boundary edge
occurrences return to marked vertices (components containing no marked
vertex are irrelevant).  Contract every such path to a gap edge.  Direct
`A_e` edges among marked vertices are retained.  The result on each original
cycle is a cyclic multigraph whose marked occurrences carry labels `P` or
`Q`.

Every cyclic binary word has an even number of label changes.  Its changing
edges split into two disjoint types:

```text
direct P--Q edges, and
contracted O-gap paths with one P endpoint and one Q endpoint.
```

Let `g_e(P,Q;O)` count the second type over all `A_e` cycles, with boundary
occurrences counted when a cycle meets the marked set only once.  Then

```text
e_(A_e)(P,Q) == g_e(P,Q;O)                    (mod 2),
epsilon_e     == g_e(P,Q;O)                    (mod 2). (261)
```

The first congruence is the even-change count on each compressed cycle; the
second is (260).  In particular, an odd outward residue forces at least one
actual `A_e` path

```text
P -- O -- ... -- O -- Q,                               (262)
```

whose internal ports avoid all four interface ports.  Conversely, the
parity of these mixed gap paths is the entire residue parity.

This is stronger than the nontermination statement after (260): the current
has a canonical complementary-gap realization on the owner cycles.  It is
also the exact analogue of Section 72's gap pairing on `B_ec`.  The closing
problem is now a comparison of two gap systems on the same port set:
`B_ec` supplies the unique alternating marked-run phase, while `A_e`
supplies the mixed `P`--`Q` paths counted by (261).  A proof that these two
gap systems have even interleaving would eliminate every odd one-edge
residue.

## 82. The outward interface is the radius-one/radius-two B boundary

The ports introduced algebraically in Section 77 have a direct location in
the line-cycle.  The port `p_-` labels the `F_e[c]` edge `x_-a_-`; its two
`B_ec` neighbors are therefore the labels of the other factor edges at
`x_-` and `a_-`, namely `p` and `q_-`.  The plus side is symmetric.  In the
four-distinct branch, the five ports occur consecutively as the simple
`B_ec` path

```text
q_- -- p_- -- p -- p_+ -- q_+.                        (263)
```

Thus `P={p_-,p_+}` is exactly the radius-one boundary of the isolated marked
center `p`, while `Q={q_-,q_+}` is its oriented radius-two boundary.  The
four bits in (254) are all possible `A_e` edges from radius two to radius
one.  They split canonically into

```text
same-side:  q_-p_-, q_+p_+,
crossed:    q_-p_+, q_+p_-.                           (264)
```

The same-side pairs are the two outward `B_ec` edges of (263); the crossed
pairs bridge across the marked center.  Consequently (261) has a completely
self-indexed reading: an odd radius-two/radius-one `A_e` interface forces an
odd number of complementary `A_e` gap paths between the two boundary
layers of one isolated `B_ec` mark.

This identifies the common cyclic order needed for the final interleaving
problem.  No arbitrary shore labeling remains: reversal of the marked
`B_ec` path swaps the minus and plus sides, while preserving the unordered
partition `{P,Q}` and the parity in (261).  What remains is to compare the
endpoints of the mixed `A_e` gaps with the fixed alternating phase on
successive marked centers of `B_ec`.

## 83. The private-shore current is conserved integrally

The modulo-two current (260) has a signed refinement on the private shore.
Write `deg_Q(p)` and `deg_O(p)` for the numbers of `A_e` neighbors of `p`
in `Q` and `O`.  The definition (254) groups exactly by its private-port
column:

```text
epsilon_e = deg_Q(p_-) - deg_Q(p_+).                  (265)
```

By (200), `p_-p_+` is absent from `A_e`.  Since both private ports have
`A_e` degree two and `e=P disjoint_union Q disjoint_union O`, one has

```text
deg_Q(p_-) + deg_O(p_-) = 2,
deg_Q(p_+) + deg_O(p_+) = 2.
```

Subtracting gives the exact signed handoff law

```text
epsilon_e = deg_O(p_+) - deg_O(p_-).                  (266)
```

Thus the interface imbalance entering the radius-one layer from `Q` exits
into the complementary owner-cycle gaps with the opposite orientation.  In
particular, (255) can be rewritten without the four local bits as

```text
sum_(d != c,e) mu^T R_cd R_de 1_(p_-)
  - sum_(d != c,e) mu^T R_cd R_de 1_(p_+)
  = deg_O(p_-) - deg_O(p_+).                          (267)
```

This retains information discarded by (260): an odd residue not only
forces mixed gap paths, but determines which private side has the excess
complementary exit.  That signed side is exactly the datum on which the
alternating `B_ec` phase can act.  The remaining global theorem must pair
these signed exits along the compressed `A_e` gaps; an unsigned pairing of
gap endpoints would be insufficient.

## 84. Two-factor transversality alone still permits odd current

The abstract topological shortcut suggested after (261) is false without a
routing hypothesis.  On ports `0,...,8`, let `B` be the cyclic factor

```text
(0,1,2,3,4,5,6,7,8)
```

and mark the isolated center `p=0`, so

```text
P={8,1},    Q={7,2},    N_B[p]={8,0,1}.
```

Let the second cyclic factor have order

```text
A=(8,7,0,2,4,1,3,5,6).
```

Then `A[N_B[p]]` is independent, exactly matching the Section 59
transversality condition.  Nevertheless the only `A` edge between `P` and
`Q` is `8--7`, so

```text
e_A(P,Q)=1.                                            (268)
```

Both overlays are genuine cycle covers; deleting the four interface ports
from `A` produces the complementary gap system of Section 81.  Thus
two-regularity, complementary-gap compression, and closed-neighborhood
independence do **not** force even interleaving.

The same reproducer as Section 80 now verifies this completion and reports

```text
two_factor_completion=odd interface=1 induced_closed_B=0
```

This remains an abstract two-factor counterprofile, not an ambient
simultaneous-routing realization.  Its role is exact: it eliminates a pure
Jordan/FPF-pairing proof from the currently established transversality
axioms.  Any valid global pairing theorem must use additional information
from (255)/(267), such as the third-color transport at the outward roots or
a compatibility equation tying the signed `A_e` exits to the alternating
`B_ec` phase.

## 85. Transpose swaps the root-sum and port-difference profiles

The additional information in (267) lies in the third-color terms.  For
each `d != c,e`, set

```text
T_d(mu,w) := mu^T R_cd R_de w.
```

The incidence blocks satisfy `R_dc=R_cd^T` and `R_ed=R_de^T`, so scalar
transposition gives the exact duality

```text
T_d(mu,w) = w^T R_ed R_dc mu.                         (269)
```

This is the available reciprocal routing, but it does not cancel (267) by
itself.  On the `c` side the test profile is the **sum**

```text
mu = 1_(a_-) + 1_(a_+),
```

whereas on the `e` side the input profile is the oriented **difference**

```text
w = 1_(p_-) - 1_(p_+).
```

After transposition, these two profile types exchange sides; they do not
return to another copy of the same one-edge functional.  This is why the
clean--clean antisymmetric cancellation of Section 56, which pairs matching
profile types, does not already eliminate the residue.

Equation (269) isolates the exact global closure requirement.  A successful
self-indexing invariant must pair the family of root-sum profiles `mu` with
the family of oriented port differences `w` under the reversed two-step
routing.  The unique alternating phase from Section 76 is the only remaining
linear mechanism capable of changing the boundary sign pattern; absent such
a sum--difference compatibility, Section 84 shows that the two owner-factor
gap systems can carry odd current.

## 86. The companion SRP polarization realizes difference--sum

The profile exchanged in Section 85 is itself accessible from the same SRP
block.  In the four-distinct branch, put

```text
rho   := 1_(a_-) - 1_(a_+),
sigma := 1_(p_-) + 1_(p_+).
```

Although `J sigma` is nonzero, `rho^T J sigma=0` because `rho` has coordinate
sum zero.  Pair the full `SRP(c,e)sigma=J sigma` with `rho`.  The first
endpoint term vanishes:

```text
rho^T A_c R_ce sigma = 0.                             (270)
```

Indeed, `R_ce sigma=1_(x_-)+1_(a_-)+1_(x_+)+1_(a_+)`.
Neither other root sees a run root by Section 74, while a possible edge
`a_-a_+` contributes equally at the two oppositely weighted rows.

For the reverse endpoint term,

```text
R_ec rho = 1_(p_-)+1_(q_-)-1_(p_+)-1_(q_+).
```

The private rows cancel against `sigma` by symmetry.  Define the outward-row
imbalance

```text
eta_e
  := A_e(q_-,p_-) + A_e(q_-,p_+)
   - A_e(q_+,p_-) - A_e(q_+,p_+).
```

Then the companion polarization is

```text
rho^T R_ce A_e sigma = eta_e,
sum_(d != c,e) rho^T R_cd R_de sigma = -eta_e.        (271)
```

It has the same signed-current interpretation on the outward shore.  Since
the possible internal edge `q_-q_+` contributes equally to both outward
degrees and every `A_e` degree is two,

```text
eta_e = deg_P(q_-) - deg_P(q_+)
      = deg_O(q_+) - deg_O(q_-).                       (272)
```

Thus SRP supplies both orientations of the sum--difference mismatch, not
just the original one.

To make their relation explicit, let `K_d` be the `2 by 2` restriction of
`R_cd R_de` with rows `(a_-,a_+)` and columns `(p_-,p_+)`, and write its
entries as `k_d^{--},k_d^{-+},k_d^{+-},k_d^{++}`.  Then

```text
mu^T K_d w     = k_d^{--}-k_d^{-+}+k_d^{+-}-k_d^{++},
rho^T K_d sigma = k_d^{--}+k_d^{-+}-k_d^{+-}-k_d^{++}.
```

Adding and subtracting (255) and (271) yields the exact Hadamard split

```text
epsilon_e + eta_e
  = -2 sum_d (k_d^{--}-k_d^{++}),
epsilon_e - eta_e
  = -2 sum_d (k_d^{+-}-k_d^{-+}).                     (273)
```

In particular `epsilon_e == eta_e (mod 2)`, but (273) retains the two
integer half-residues: diagonal third-color imbalance and crossed
third-color imbalance.  The alternating phase no longer needs to invent a
sum--difference conversion; SRP already provides both polarizations.  The
remaining global task is to pair their diagonal and crossed half-residues
across successive marked centers.

## 87. The compressed SRP block is determined entrywise

The Hadamard split (273) should not be mistaken for a new local parity
constraint.  Sum the third-color matrices and write

```text
K := sum_(d != c,e) K_d,
h := A_c(a_-,a_+).
```

Also abbreviate the four interface bits by

```text
s_-:=A_e(q_-,p_-),  c_-:=A_e(q_-,p_+),
c_+:=A_e(q_+,p_-),  s_+:=A_e(q_+,p_+).
```

Evaluate SRP at the four pairs `(a_i,p_j)`.  The Section 74 exclusions kill
every other-root/run-root `A_c` entry, and (200) kills `A_e(p_-,p_+)`.
The endpoint partition therefore gives the complete binary matrix

```text
K = [ 1-s_-      1-h-c_- ]
    [ 1-h-c_+    1-s_+   ].                           (274)
```

For example, at `(a_-,p_+)` the source endpoint contributes exactly `h`,
the reverse endpoint contributes exactly `c_-`, and the third-color sum is
the remaining `1-h-c_-`.  Endpoint disjointness guarantees these displayed
quantities lie in `{0,1}`; the other entries are symmetric.

Substituting (274) into (273) recovers identities:

```text
sum_d (k_d^{--}-k_d^{++}) = s_+ - s_-,
sum_d (k_d^{+-}-k_d^{-+}) = c_- - c_+.
```

Hence the companion polarization is valuable because it exposes both
oriented route channels, but it cannot rule out any of the fifteen local
patterns from Section 80.  The scalar third-color sum `K` contains exactly
the same local information as `(h,s_-,c_-,c_+,s_+)`.

The final invariant must retain the **color decomposition**
`K=sum_d K_d`: which clean color supplies each surviving unit and how that
label transforms under (269).  Summing over `d` before comparing successive
marks necessarily collapses back to the locally realizable matrix (274).
This is the precise point where simultaneous self-indexing, rather than one
more scalar SRP functional, must enter.

## 88. The residual block is a partially labeled two-by-two matrix

Because every `K_d=R_cd R_de` has nonnegative integer entries and the total
matrix `K` in (274) is binary, each occupied cell `(i,j)` has a unique third
color `d_(ij)` such that

```text
(K_(d_(ij)))_(ij) = 1,
(K_d)_(ij) = 0 for d != d_(ij).                        (275)
```

Moreover the unit product has a unique intermediate port
`y_(ij) in d_(ij)`: two such ports would be two common ambient neighbors of
`a_i` and `p_j`, producing a four-cycle.  Thus every occupied cell records a
canonical routed path

```text
a_i -- y_(ij) -- p_j                                  (276)
```

together with its color label.  Empty cells record endpoint-layer routing
through `A_c` or `A_e` as displayed in (274).

Scalar transposition (269) now has an entrywise form.  The path (276)
reverses to

```text
p_j -- y_(ij) -- a_i,
```

with the same third color; equivalently the color-labeled residual block for
the reversed ordered pair is the transpose of the original labeled block.
No choice of intermediate port or relabeling is available.

This is the minimal simultaneous datum left by the local audit: a partially
filled `2 by 2` matrix, with at most four occupied cells, whose labels and
intermediate ports are preserved under reversal.  Section 87 proves that
forgetting these labels recovers only the locally arbitrary interface bits.
The closing invariant must therefore compare the labeled matrices at
successive isolated marks—most plausibly by showing that the alternating
phase pairs equal labels in opposite signed cells.  Whether two occupied
cells in one row or column may share a label remains an open incidence
constraint; it is not decided by (275) alone.

## 89. Transpose kills the crossed channel and preserves the diagonal one

For each third color define its two signed Hadamard contributions

```text
alpha_d := k_d^{--} - k_d^{++},
beta_d  := k_d^{+-} - k_d^{-+}.                       (277)
```

With the displayed minus/plus ordering fixed on both shores, reversal of the
two-step routing replaces `K_d` by `K_d^T`.  Therefore

```text
alpha_d(K_d^T) =  alpha_d(K_d),
beta_d(K_d^T)  = -beta_d(K_d).                        (278)
```

Thus the two halves in (273) have opposite transpose character.  The
crossed half is already antisymmetric: whenever the global ledger contains
both orientations of the same labeled rectangle with equal weight, their
`beta_d` contributions cancel.  The diagonal half is symmetric and doubles
instead; transpose alone cannot remove it.

This reduces the color-resolved closing problem from two channels to one.
The remaining alternating phase need only control

```text
sum_d alpha_d = sum_d (k_d^{--}-k_d^{++}),            (279)
```

the difference between same-label routing at the two diagonal cells.  Any
failure of global crossed cancellation must now be exhibited as a failure
to pair the reversed labeled rectangles with equal weight, not as an
intrinsic sign defect of `beta_d`.  Conversely, even perfect transpose
pairing leaves (279) untouched, so the diagonal label transport is the sole
genuine phase obstruction.

Equation (278) is algebraic and does not assert that the required reversed
rectangles occur among the isolated marks.  Establishing that occurrence
and weight pairing is part of simultaneous self-indexing; once it is
available, only the transpose-even diagonal channel must be propagated
along `B_ec`.

## 90. Diagonal labels are actual rooted transition edges

The diagonal channel has more structure than an arbitrary labeled matrix
entry.  For either sign `i in {-,+}`, the private port `p_i` lies in the
fiber `Y_e(a_i)`, so `a_i p_i` is an ambient cross edge.  If the diagonal
cell `K_(ii)=1`, Section 88 supplies its unique path

```text
a_i -- y_(ii) -- p_i,
```

of color pattern `c--d_(ii)--e`.  Together with `p_i--a_i`, this is an
actual rooted triangle at `a_i`.  Equivalently, the diagonal label `d_(ii)`
is a neighbor of `e` in the rooted exterior-color graph at `a_i`, and the
triangle uses the specific `e`-port `p_i`.

This also follows numerically from (274):

```text
K_(--)=1-s_-,    K_(++)=1-s_+,
```

where `s_i=b_(a_i,e)` is the `A_e` fiber-switch bit.  The diagonal route is
present exactly when that specific same-side endpoint layer is absent; SRP
then assigns the unit to its unique third-color triangle.

Consequently `alpha_d` from (277) has the intrinsic interpretation

```text
alpha_d
  = [the p_- rooted transition at a_- has color d]
  - [the p_+ rooted transition at a_+ has color d].    (280)
```

The sole transpose-even obstruction (279) is therefore a signed difference
of **rooted transition endpoints**, not an unconstrained color label.  This
reconnects the boundary functional calculus to Sections 43 and 62: the
label can be followed along the canonical rooted color path and its actual
port lift.  A global alternating-phase proof may now pair endpoint tokens
through those lifted paths rather than attempting to pair arbitrary matrix
entries.

No analogous triangle interpretation is asserted for a crossed cell:
`a_-p_+` and `a_+p_-` are absent in the four-distinct branch, which is why
the crossed channel instead closes by transpose antisymmetry.

## 91. The outward rooted budget has exactly three states

At either outward root `a_i`, the edge labelled `p_i` is unmarked because
`p` is an isolated marked center.  The other `A_c` edge at that root is
labelled `q_i`.  Hence, for owner color `e`, the rooted owner count is

```text
a_(a_i,e) = [q_i in M_e].
```

Write `s_i=A_e(q_i,p_i)=b_(a_i,e)` as above and let `v_i` be the rooted
vertical degree of `e`.  The rooted budget becomes

```text
[q_i in M_e] + 2s_i + v_i = 2.                        (281)
```

There are exactly three possibilities:

```text
q_i marked:     (a,s_i,v_i)=(1,0,1),
q_i unmarked,
  no switch:    (a,s_i,v_i)=(0,0,2),
q_i unmarked,
  fiber switch: (a,s_i,v_i)=(0,1,0).                 (282)
```

By (274), the diagonal cell is occupied exactly in the first two states.
In the marked case, `e` has rooted color-graph degree one, so the label
`d_(ii)` of Section 90 is its unique neighbor and is the endpoint color of
the rooted transition path at the boundary of the next `e`-run.  In the
unmarked no-switch case, `e` has degree two: the `p_i` triangle supplies one
incident transition and the port bijection assigns the other transition to
the other `e`-port `q_i`.  Thus the diagonal label is one half of a canonical
through-transition at `a_i`.

The third state has no diagonal label at all; its two `e`-ports are joined
internally by `A_e`.  Therefore every diagonal token in (280) belongs to a
canonical rooted transition path, either as an endpoint at the next marked
run or as a through-step across an unmarked radius-two port.  This gives the
promised propagation rule: follow the degree-two states until the token
reaches a marked endpoint or closes on a rooted color cycle.  The remaining
global parity question is how these endpoint/closed-cycle alternatives
interact with the alternating signs of successive isolated marks.

## 92. Routing and run reversal give complementary sign characters

There are two different involutions on a labeled boundary block.  Let

```text
S = [0 1]
    [1 0]
```

swap the minus and plus indices.  Routing reversal from Section 89 acts by

```text
T(K_d) := K_d^T,
```

while reversal of the oriented run swaps both shores and acts by

```text
C(K_d) := S K_d S.
```

They commute, and their effects on the two Hadamard channels are

```text
             alpha_d   beta_d
identity        +         +
T               +         -
C               -         -
C T             -         +.                         (283)
```

The first nontrivial row is (278).  Conjugation swaps both diagonal entries
and both crossed entries, negating both differences.  Their composite
therefore negates only `alpha_d`.

This is the exact symmetry division required by the closing invariant.
Equal-weight pairing under routing reversal cancels the crossed channel but
leaves the diagonal channel.  Equal-weight pairing under the composite
run--routing reversal cancels the diagonal channel but leaves the crossed
one.  A family of labeled mark occurrences closed equivariantly under both
involutions has zero total residue in both channels.

The needed equivariant closure is not yet proved.  Run reversal always
exists as a reorientation of one mark, but that is not by itself a second
occurrence in the global ledger; routing reversal always exists algebraically
by (269), but need not land on another isolated mark.  The alternating phase
must supply exactly this occurrence/weight matching.  Equation (283) turns
that task into a finite group-action statement: construct the required
`{1,T,C,CT}` orbits of color-labeled transition endpoints, or identify the
unpaired orbit that carries the obstruction.

## 93. Equal labels pass straight through a private port

Return to one side `i in {-,+}` of the isolated mark.  Section 74 gives a
mandatory boundary triangle at the run root `x_i`, using the private port
`p_i`; let its unique third color be `r_i` and its intermediate port be
`z_i`.  If the diagonal cell at the outward root `a_i` is occupied, Section
90 gives the second triangle through the same private port, with label
`d_i:=d_(ii)` and intermediate port `y_i`:

```text
x_i -- z_i -- p_i -- x_i,       color(z_i)=r_i,
a_i -- y_i -- p_i -- a_i,       color(y_i)=d_i.        (284)
```

If `d_i=r_i=d`, then `z_i != y_i`.  Otherwise the two distinct `c`-roots
`x_i,a_i` would have the two common neighbors `p_i` and `z_i=y_i`, giving
an ambient four-cycle.  Since `p_i` has exactly two neighbors in component
`d`, the pair `{z_i,y_i}` is exactly its `d`-fiber.  Equal labels therefore
give a canonical straight-through pairing across the private port:

```text
boundary d-token at x_i  <-->  outward d-token at a_i. (285)
```

If `d_i != r_i`, the private port carries a genuine **color turn**: the two
rooted transition tokens cannot cancel labelwise.  If the diagonal cell is
absent, Section 91 is in the fiber-switch state and there is no outward
token to pair with the boundary token.  Thus every side of an isolated mark
has exactly one of three continuation types:

```text
straight label-preserving passage,
color turn,
owner-factor fiber switch.                            (286)
```

Only the last two types can contribute to an unpaired labeled orbit in
Section 92.  Equation (285) removes all straight passages canonically,
without choosing signs or paths.  The remaining global invariant may now be
formulated as a balance between color turns and fiber switches along the
alternating `B_ec` phase—the same signed bundle boundary that survives in
the B3 lane.

## 94. Closed labeled occurrence flow would be Eulerian, not reversible

The pairing (285) crosses an **unmarked** edge of the shadow factor
`F_e[c]`.  It is therefore not a horizontal edge of the state graph
`Gamma_c`, whose horizontal edges are the marked owner edges in
`K_ce=A_c cap F_e[c]`.  Two triangles paired through `p_i` may consequently
belong to different state cycles.  The closed walks of Sections 63--64 do
not by themselves prove that the new token pairings close into cycles.

The required closure lemma can now be stated precisely: combine the
straight pairings (285), the rooted degree-two continuations of Section 91,
and the owner-factor switches into an auxiliary graph on labeled triangle
tokens, and prove that every token has one predecessor and one successor.
If this holds, its components are cyclic words `...,r,e,d,...`; at each
middle occurrence `e`, record the induced turn `r --> d`.

Conditioned on that closure lemma, let `N(r,d)` count directed turn
occurrences before inserting alternating signs.  Cyclicity then gives

```text
sum_d N(r,d) = sum_d N(d,r)     for every label r.     (287)
```

Straight terms `N(r,r)` cancel locally by (285), leaving a divergence-free
directed flow of genuine color turns.  This is weaker than the reversibility
needed for transpose-odd cancellation:

```text
N(r,d) = N(d,r).                                      (288)
```

An oriented label cycle `r --> d --> f --> r` satisfies (287) but violates
(288).  Hence even after auxiliary closure is proved, Eulerian bookkeeping
alone cannot supply the occurrence-weight pairing required in Section 92.
After straight passages are removed, the only possible obstruction is a
circulation on a directed label cycle of length at least three.

This separates two open obligations which were previously conflated: first
prove closure of the port-token continuation graph, then exclude or pair its
nonreversible circulations.  The B3 bundle lane faces the second obligation
directly; the present lane must still establish the first.

## 95. Straight passages preserve the line-cycle orientation

Fix one oriented side of the five-port window (263), written

```text
p -- p_i -- q_i
```

in the outward direction.  The run root `x_i` is the common endpoint in
`F_e[c]` of the edges labelled `p` and `p_i`; the outward root `a_i` is the
common endpoint of the edges labelled `p_i` and `q_i`.  Therefore the
straight pairing (285) through the fixed port `p_i` moves from the first
root occurrence to the second:

```text
(p,p_i) at x_i  -->  (p_i,q_i) at a_i.                (289)
```

This is exactly one forward step of the oriented `B_ec` window.  The reverse
orientation gives the reversed step.  There is no third root incident to
the factor edge labelled `p_i`, so a straight passage cannot branch or
reverse while preserving its port and label.

Iterating (289) across consecutive straight states produces a directed arc
of the `B_ec` cycle.  Its endpoints are precisely the first nonstraight
events from (286): a color turn, an owner-factor fiber switch, or a marked
run boundary.  Hence every maximal straight chain has a genuine `B_ec`
orientation.  This does not yet show that the chains join into a cyclic
token flow; that is exactly the closure lemma isolated in Section 94.

This supplies the orientation compatibility requested after (285).  Once
auxiliary closure is established, the alternating phase of Section 76 acts
on consecutive residual events in their genuine line-cycle order.  Only
then does the reversible-weight/circulation question of Section 94 apply.

## 96. A rooted color triangle already supports irreversible circulation

The two-regularity of the rooted exterior-color graphs does not by itself
exclude the length-three obstruction from Section 94.  At one root, suppose
three exterior colors `r,d,f` form a rooted color triangle.  Traverse its
state-color cycle as

```text
r --> f --> d --> r.
```

The skip-one turns at the three middle states are

```text
at f: r --> d,
at d: f --> r,
at r: d --> f.
```

Together these are the irreversible directed circulation

```text
r --> d --> f --> r.                                  (290)
```

Every rooted color has degree two, every transition uses a distinct port by
the port bijection, and no loop is involved.  Thus maximum degree two,
looplessness, and the local rooted path/cycle classification are all
compatible with the minimal nonreversible flow.

This is a structural local counterprofile, not a claim that the triangle
extends to the full odd-horizontal state cycle or satisfies every SRP block.
It closes one tempting shortcut: the remaining directed circulations cannot
be killed solely inside a rooted triangle multigraph.  A valid exclusion
must use a proved closure/embedding of the oriented `B_ec` chains from
Section 95, the odd horizontal count, or the simultaneous occurrence weights
supplied by the other colors.

## 97. The final obstruction is a horizontally odd labeled circulation

The rooted triangle in Section 96 has no horizontal transport: all three
state changes occur at one root.  It therefore has horizontal parity zero
and does not contradict the desired mixed-cycle theorem.

For any **closed** auxiliary token flow `Z` obtained after contracting the
straight passages of Section 95, retain on every directed residual edge the
length of the suppressed oriented `B_ec` arc and define

```text
omega_B(Z) := sum_(arcs of Z) arc_length              (mod 2).  (291)
```

The grading is well-defined for such a closed token flow.  What is not yet
proved is that a state cycle `Omega` canonically induces one while preserving
horizontal parity.  The missing bridge is

```text
Omega |--> Z(Omega) closed, with
omega_B(Z(Omega)) = H(Omega)  (mod 2).                (292)
```

The unmarked-shadow warning in Section 94 shows that (292) is a theorem, not
a formal consequence of the state-cycle lift.  If it is established, then
the rooted triangle of Section 96 has grading zero while an odd-horizontal
`Omega` induces grading one.  The second required theorem is the homological
strengthening

```text
every simultaneously realizable balanced labeled occurrence flow Z
satisfies omega_B(Z)=0.                               (293)
```

Equations (292) and (293) are both targets.  The first is the auxiliary
closure/grade-preservation lemma; the second is the simultaneous-routing
kernel statement.  Together they contradict an odd-horizontal `Omega`.
Keeping them separate prevents the line-cycle port pairing from being
mistaken for a state-graph edge and identifies the exact additional work
needed before the homological terminal can be used.

## 98. The aggregate incidence-dart flow closes canonically

Per-state-cycle closure is unnecessary for the original parity sum.  Fix
`c != e` and let

```text
D_ce := {(x,p) : R_ce(x,p)=1}
```

be the incidence darts of the cross two-factor.  There are two canonical
fixed-point-free involutions on `D_ce`:

```text
R(x,p) := (x,p'),   where Y_e(x)={p,p'},
P(x,p) := (x',p),   where the c-neighbors of p are {x,x'}.
```

The graph with the `R`- and `P`-pairs as edges is two-regular, hence a
disjoint union of cycles.  Contracting its port pairs gives `B_ec`, while
contracting its root pairs gives `F_e[c]`; keeping the darts gives the
subdivision common to both line cycles.  This closure is
unconditional and may splice triangles lying on different `Gamma_c` cycles,
which is exactly why it survives the warning in Section 94.

The rooted budget decorates every `R`-pair exhaustively.  If neither port is
marked, the root pair is either two rooted transition tokens (`b=0,v=2`) or
an owner-factor switch (`b=1,v=0`).  If exactly one port is marked, the
unmarked dart carries the unique boundary transition (`a=1,v=1`).  If both
are marked, the root is internal to an owner run (`a=2,v=0`).  These are the
global versions of the three outward states in (282), now including run
interiors and boundaries.

A `P`-pair at port `p` is marked precisely when `p in M_e`, equivalently
when its two roots form an edge of `K_ce=A_c cap F_e[c]`.  Thus marked
`P`-pairs are in bijection with the horizontal state edges, and

```text
number of marked P-pairs = |M_e| = p_ce.              (294)
```

For an auxiliary dart cycle `Z`, define

```text
omega_M(Z) := number of its marked P-pairs  (mod 2).
```

Summing over all dart cycles gives the exact aggregate bridge

```text
sum_Z omega_M(Z) = p_ce  (mod 2).                     (295)
```

No map from an individual state cycle is asserted or needed.  The original
target is now equivalent to proving

```text
sum_(e != c) sum_(dart cycles Z in D_ce) omega_M(Z)=0. (296)
```

The remaining simultaneous task is to lift the color labels/intermediate
ports of Sections 88--93 to these closed dart cycles and show that their
total marked grading cancels.  Unlike the conditional bridge (292), the
cycle closure and aggregate grade identity (295) are already proved by the
two involutions; only the labeled kernel statement remains.

## 99. The dart cycles carry a complete H/V/S alphabet

The port bijection (60) decorates each incidence dart `(x,p)` by the state
edge using that port.  There are three types:

```text
H     if p labels a horizontal owner edge,
V_d   if the rooted triangle through p joins owner e to color d,
S     if b_(x,e)=1 and p belongs to the A_e fiber switch at x.
```

At every root, the `R`-paired darts have exactly one of the four forms

```text
(H,H)        a=2, b=0, v=0       run interior,
(H,V_d)      a=1, b=0, v=1       run boundary,
(V_d,V_f)    a=0, b=0, v=2       rooted through-turn,
(S,S)        a=0, b=1, v=0       owner-factor switch. (297)
```

This is just the rooted budget `a+2b+v=2`, with the two incident state edges
assigned bijectively to the two ports.  Repeated labels `d=f` are allowed in
the third row when the rooted color multigraph has parallel occurrences;
the intermediate ports still distinguish the two tokens.

The `P`-pair at a port has either two `H` endpoints or no `H` endpoint.  The
first alternative occurs exactly for `p in M_e`, since ownership is a
property of the whole factor edge labelled by `p`.  In the unmarked
alternative, its endpoints are decorated by `V` labels or by the adjacent
root switches.  Equal `V_d` endpoints give the straight pairing of Section
93; unequal labels give a color turn; an `S` endpoint records a switch
handoff.

Thus every auxiliary dart cycle is now an unconditional cyclic word over
the alphabet

```text
H, S, and V_d with its unique intermediate port.      (298)
```

The number of `H--H` port pairs in the word is its marked grading
`omega_M`.  Sections 88--93 describe exactly how the labeled `V` atoms
transform under routing/run reversal and how equal labels cancel.  The
remaining kernel theorem (296) is therefore a statement about these closed
H/V/S words: after summing over owner colors, the number of `H--H` port
pairs is even whenever all color-labeled `V` atoms and switch handoffs obey
their simultaneous reversal ledger.

## 100. Mixed dart cycles reduce to labeled gap holonomy

The closed H/V/S words split into two branches.  If every port pair on a
dart cycle is `H--H`, then every corresponding shadow edge is owned by `e`
and every root pair is `(H,H)`.  Contracting the port pairs gives a whole
cycle of `F_e[c]` lying in `A_c`: this is exactly the all-horizontal,
monochromatically owned obstruction already isolated in Sections 16--19.

Otherwise the dart cycle is mixed.  Its `H--H` port pairs form maximal
nonempty runs separated by gaps containing `V` or `S` data.  If their
lengths are

```text
ell_1,...,ell_t,
```

then, by definition of the marked grading,

```text
omega_M(Z) = ell_1+...+ell_t                         (mod 2),
(-1)^(omega_M(Z)) = product_j (-1)^(ell_j).           (299)
```

Each run has two `(H,V_d)` boundary roots.  The alternating profile of
Sections 61 and 76 transports a boundary sign across that run by the factor
`(-1)^(ell_j)`.  The intervening non-H gap is an unconditional word in
`V_d` tokens and `S` switches from (298); straight equal-label passages may
be contracted by (285), leaving only color turns and switch handoffs.

Thus the mixed branch has a precise holonomy terminal.  Construct from each
labeled non-H gap a sign transfer `theta_j` such that

```text
product_j theta_j = 1                                 (300)
```

by route/run-reversal pairing of its privately witnessed tokens, and show
that closing the boundary phase gives

```text
product_j ((-1)^(ell_j) theta_j) = 1.                 (301)
```

Equations (300)--(301) imply `omega_M(Z)=0` by (299).  They are a target,
not yet a construction of `theta_j`: their value is that they separate the
already proved run contribution from the sole missing labeled-gap
contribution.  The all-H branch remains the earlier owner-cycle program;
the mixed branch is now exactly the private-feature/reversal problem shared
with B3, with no closure ambiguity left.

## 101. The naive gap bundle telescopes away all private data

Orient one non-H gap from its left boundary token to its right boundary
token.  Retain the complete dart-symbol sequence from (298), including the
color and intermediate port on every `V` token and a rooted identifier on
every `S` token:

```text
u_0,u_1,...,u_m.
```

In the free abelian group on these token symbols, define the elementary
successor-minus-predecessor bundle

```text
Delta_0(G) := sum_(k=0)^(m-1) ([u_(k+1)]-[u_k]).
```

It telescopes exactly:

```text
Delta_0(G) = [u_m]-[u_0],
Delta_0(reverse G) = -Delta_0(G).                      (302)
```

Thus the naive gap boundary has the desired route-odd character, but it
forgets every internal turn, intermediate port, and switch.  Distinct gaps
with the same endpoint symbols have identical `Delta_0`, even if their
simultaneous routing data are completely different.  No private-feature
rigidity, and hence no canonical transfer `theta_j`, can follow from (302).

This is the exact gap-level analogue of the scalar-compression failures in
Sections 87 and 94.  The required bundle must attach features to the
**transition occurrences**—for example the ordered pair of rooted triangles,
the consumed secondary fiber, or the switch handoff—not merely to the token
states at their ends.  Such a transition bundle may still have endpoint
boundary (302), but its internal tagged rows need not telescope and can
privately witness an unoriented gap.  This is precisely the strengthening
isolated empirically as the private tagged-bundle feature in the B3 lane.

## 102. The missing feature map must be both conserved and private

Let `E_gap` be the free module on oriented local transition occurrences in
the non-H gaps, with route reversal `T`.  Two extreme feature maps are
immediate.

The endpoint boundary

```text
partial : E_gap --> Z[token symbols],
partial(u --> v) = [v]-[u]
```

is conserved around every closed word, but Section 101 shows that it is not
private: all internal information telescopes.  Conversely, the actual
unoriented dart support gives an injective map

```text
iota : E_gap / (t+Tt) --> Z[unoriented transition supports],
```

because two different edges of the dart cycle have different incidence
supports.  This map is perfectly private, but no SRP identity says that the
signed `iota`-sum of an oriented occurrence flow vanishes; an oriented cycle
normally uses every support only one way.

The closing invariant is therefore exactly an intermediate feature map

```text
Phi : E_gap --> F                                    (303)
```

with both properties:

```text
conservation: the realized global gap ledger has total Phi-boundary zero;
privacy:      the induced columns on E_gap/(t+Tt) are independent
              (or at least have a private coordinate).              (304)
```

Conservation plus privacy forces equal weights on every route-reversal pair
by coefficient peeling.  That supplies the gap transfers in (300), after
which (301) kills the mixed marked grading.

Equation (304) distinguishes a genuine invariant from a tautological
occurrence tag.  Endpoint features have conservation without privacy;
literal dart identities have privacy without conservation.  The candidate
`Phi` must use the finest data still controlled by SRP—ordered rooted
triangles, intermediate fibers, and switch roles.  The B3 lane's private
tagged-bundle computation is empirical evidence that precisely such a
middle feature space exists; proving its analogue uniformly is now the
shared algebraic task.

## 103. A single root-marked primitive has only a one-bit cokernel

The canonical primitive (91)--(92) is the finest existing root-marked SRP
identity, but its coboundary statement alone cannot supply the private map
`Phi`.  On a connected cycle of order `n`, let

```text
(delta phi)_i := phi_(i-1) + phi_i
```

over `F_2`.  Then

```text
ker(delta) = span{1},
im(delta)  = {kappa : sum_i kappa_i=0},
dim coker(delta)=1.                                   (305)
```

Indeed `delta phi=0` forces every consecutive pair of values equal, so
`phi` is constant.  Rank-nullity gives rank `n-1`, and every image vector
has even coordinate sum; hence the image is exactly the even-sum
hyperplane.

Thus the conserved information in the bare statement
`kappa=delta phi` is only the already known total parity of `kappa`.  A
one-dimensional cokernel cannot privately distinguish the many unoriented
gap transitions required by (304).  The distinguished formula (91) for
`phi` retains much more routing data, but `phi` itself is not a zero-boundary
feature whose global occurrence sum is known to vanish.

Consequently the candidate `Phi` cannot be obtained by simply reusing one
root-marked coboundary row.  It must consume the **compatibility** of the
distinguished primitives as the third color and target incidence component
vary—the precise compatibility left open after Section 25.  This rules out
another overly coarse conservation map while pointing to the correct
refinement: atomize the cross-color family of primitives before taking its
cycle derivative or total sum.

## 104. Shared reversal-rigidity lemma for tagged bundles

The common algebraic core of the SRP and B3 lanes is independent of their
combinatorial notation.  Let `I` be a finite transition set with a
fixed-point-free involution `T`, let `Delta(t)` lie in a vector space over a
field of characteristic not two, and suppose

```text
Delta(Tt) = -Delta(t).                                (306)
```

Choose one representative from every unordered pair `{t,Tt}`.  If the
representative vectors `Delta(t)` are linearly independent, then every
balanced occurrence weighting

```text
sum_(t in I) x_t Delta(t)=0
```

is route-reversible:

```text
x_t = x_(Tt)     for every t.                         (307)
```

Indeed, grouping the balanced sum by reversal pairs gives

```text
sum_(representatives t) (x_t-x_(Tt)) Delta(t)=0,
```

and independence kills each coefficient.  A private nonzero feature
coordinate for every representative is a sufficient triangular certificate
for that independence.

To apply this lemma to a non-H dart gap, the transition atom must contain
more than its endpoint symbols.  The shared **tagged-bundle schema** is:

```text
endpoint signature,
multiset of consumed secondary-fiber states with role tags,
switch/deletion role when present.                    (308)
```

Its boundary `Delta=B^+-B^-` must satisfy three lane-specific facts:

```text
route oddness:  reversal swaps B^+ and B^-;
conservation:   the realized global occurrence ledger has total Delta zero;
privacy:        every unoriented Delta column owns a feature row
                (or the columns are otherwise independent).              (309)
```

Then (307) gives the reversible weights needed for the gap transfers
`theta_j`.  In B3, route oddness is proved and privacy is supported by the
private secondary-fiber audits; conservation comes from the Farkas ledger.
In the present SRP lane, route oddness is supplied by Sections 88--92, while
the exact conserved choice of the secondary-fiber multiset and its privacy
remain open.  Equations (306)--(309) are therefore a single reusable theorem
interface, not an assertion that the SRP bundle has already been built.

## 105. Even varying tests of the full SRP transport collapse

The proposed tagged-test construction has a necessary noncommutation.  Let
`P_ce` denote the three-family transport on the left side of (243), so that

```text
P_ce(1_u-1_v)=0
```

whenever `u,v` are consecutive `B_ec` ports.  On an oriented non-H gap
`p_0,...,p_m`, put `w_i=1_(p_i)-1_(p_(i+1))`.  For any **fixed** linear test
functional `ell`, linearity and (244) give

```text
sum_(i=0)^(m-1) ell(P_ce w_i)
  = ell(P_ce(1_(p_0)-1_(p_m))) = 0.                  (310)
```

Thus replacing a vertex indicator by one fixed fiber-census indicator does
not evade Section 101: every such observation still factors through the two
gap endpoints and forgets all internal transition occurrences.

To retain those occurrences, the test must vary with the step.  For
functionals `ell_i`, discrete summation by parts gives the exact identity

```text
sum_(i=0)^(m-1) ell_i(P_ce w_i)
  = ell_0(P_ce 1_(p_0)) - ell_(m-1)(P_ce 1_(p_m))
    + sum_(i=1)^(m-1)
        (ell_i-ell_(i-1))(P_ce 1_(p_i)) = 0.          (311)
```

The last sum is the formal commutator between transition-dependent tagging
and the cycle derivative.  However the full SRP operator is exactly `J`, so
`P_ce 1_(p_i)=1_c` for every port `p_i`.  Therefore (311) reduces further to

```text
ell_0(1_c) - ell_(m-1)(1_c)
  + sum_(i=1)^(m-1) (ell_i-ell_(i-1))(1_c) = 0,        (312)
```

which is a scalar telescoping tautology.  Even transition-dependent tests
of the **combined** SRP transport cannot record an ordered rooted triangle,
a consumed secondary-fiber state, or a switch handoff.

Consequently an SRP tagged bundle cannot come from any projection of the
full left side of (243), fixed or varying.  The summands must remain resolved
by endpoint/third color and intermediate fiber *before* the identity is
tested.  The cross-color compatibility of the distinguished primitives
must then prove cancellation only after those resolved defects are assembled.
This separates the two remaining obligations cleanly:

```text
conservation = cancellation across the resolved SRP layers;
privacy      = injectivity of their nonzero state-change defects.        (313)
```

Equations (311)--(312) are the smallest-window test for any candidate
`Phi`: a proposal that first replaces the resolved routing partition by
`P_ce=J` has already lost the required tags.  A viable proposal must exhibit
which individual `Q_d` layer carries each feature and a genuine global
identity cancelling the resulting layer-resolved defects.

## 106. The maximal one-port route lift still telescopes

Keeping the `Q_d` layers resolved is necessary but not sufficient.  For a
third color `d`, every occupied entry of

```text
Q_d = R_cd R_de
```

has its unique intermediate `d`-port by the four-cycle argument of Section
88.  Hence a port `p in e` has a canonical maximal route-incidence lift

```text
Psi_d(p)
  := sum_({x in c, y in d : x--y--p}) [x,y,p]          (314)
```

in the free module on labeled two-step paths.  Projecting `[x,y,p]` to
`[x]` recovers the column `Q_d 1_p`; thus (314) retains strictly more data
than any vertex-valued test of the individual layer.

Nevertheless, on a gap `p_0,...,p_m`, even this finest **one-port** lift
has

```text
sum_(i=0)^(m-1)
  (Psi_d(p_i)-Psi_d(p_(i+1)))
    = Psi_d(p_0)-Psi_d(p_m).                           (315)
```

The cancellation is formal and occurs before any projection or sum over
`d`.  The same argument applies to every feature of the form `Psi(p)` in
any abelian group, including a port decorated by all of its colors,
intermediate fibers, rooted triangles, and incidence classes.

Therefore the feature required by (309) cannot be a difference of
independently decorated port states.  It must be genuinely **two-local**:

```text
Gamma(p_i,p_(i+1)) != Psi(p_i)-Psi(p_(i+1))            (316)
```

for every possible one-port potential `Psi`.  Its extra coordinate must
record data consumed jointly by the transition—such as the ordered pair of
rooted routes or the secondary-fiber census left after their common part is
removed.  This is exactly the structural distinction in the B3 private
bundle: endpoint signatures are one-local and insufficient, whereas the
consumed secondary-fiber state belongs to the unordered transition.

Equations (314)--(316) narrow the SRP construction target further.  Layer
resolution avoids the `P_ce=J` collapse of Section 105, but privacy can only
come from a nonseparable transition feature.  Conservation must therefore
be proved directly for the global sum of those two-local features; it cannot
be inherited from telescoping a port potential.

## 107. Two-local information is a defect between the two dart matchings

The dart set `D_ce` of Section 98 has two canonical perfect matchings: the
root matching `R` and the port matching `P`.  Let `L` be any set of fully
labeled dart states (including color, intermediate port, and switch role),
and let `lambda:D_ce -> L` be the state decoration from Section 99.  For a
function `Gamma` on unordered pairs of labels define the pairing defect

```text
D_Gamma
  := sum_({a,b} in R) Gamma(lambda(a),lambda(b))
     - sum_({a,b} in P) Gamma(lambda(a),lambda(b)).     (317)
```

Every one-local feature is invisible to this defect.  If

```text
Gamma(s,t)=psi(s)+psi(t),
```

then both perfect matchings use every dart exactly once, so `D_Gamma=0`.
This is the matching-level form of the telescoping in Sections 101 and 106.
Conversely, after quotienting pair features by these one-local potentials,
`D_Gamma` is the universal genuinely two-local statistic of the two
pairings: it records how the same labeled darts are coupled at roots versus
at ports, not merely their common marginal census.

For scalar dart observables `f,g`, the polarized pair feature

```text
Gamma_(f,g)(s,t)=f(s)g(t)+f(t)g(s)
```

has defect

```text
D_(f,g)
  = sum_({a,b} in R) (f_a g_b+f_b g_a)
    - sum_({a,b} in P) (f_a g_b+f_b g_a).              (318)
```

Thus the first viable SRP tagged bundle is necessarily a family of
root-versus-port **correlation identities** (318).  Taking `f,g` to be
indicators of fully labeled transition states makes the resulting pair
coordinates as fine as possible and supplies the candidate private rows.
What is not automatic is their conservation: an arbitrary pair feature has
nonzero (317), exactly as the abstract two-factor counterprofile of Section
84 permits.

This identifies the remaining SRP obligation without an unspecified
feature map:

```text
find an SRP-controlled subspace W of labeled dart observables such that
  D_(f,g)=0 for the required f,g in W,                       (319)
and the surviving pair-correlation columns separate reversal classes.
```

The root-marked primitives (91) are natural candidates for `W`, but Section
103 shows that one primitive at one target has insufficient rank.  Their
cross-color and target-incidence compatibility must prove the bilinear
root/port correlation equality (319).  In B3 language, (317) is exactly the
new information created by cross-tagging a target bundle with its source
signature: the two endpoint marginals balance, while the source--consumed-
fiber correlation need not.

## 108. Universal correlation conservation collapses to two-periodicity

There is one more sharp distinction inside (319).  Let `M_R,M_P` be the
permutation matrices of the root and port involutions on one dart cycle and
put

```text
K := M_R-M_P.
```

For dart functions `f,g`, the polarized defect (318) is exactly

```text
D_(f,g)=f^T K g.                                      (320)
```

Indeed each matching edge `{a,b}` contributes `f_a g_b+f_b g_a` to the
corresponding matrix product.

The right kernel of `K` is elementary.  Number the darts cyclically so the
`R` and `P` edges alternate.  Then `Kg=0` says at every dart that the values
of `g` on its two cycle neighbors agree:

```text
g_(i-1)=g_(i+1).
```

Hence

```text
ker K = {functions constant on each parity class of the dart cycle}.     (321)
```

In particular, if conservation is demanded in the overly strong form

```text
D_(f,g)=0 for every dart test f,
```

then `g` is only two-periodic.  Such a `g` cannot distinguish the many
rooted transition labels or supply private rows for (309).  This recovers,
at the correlation level, the alternating one-mode collapse of Section 76.

Therefore the desired SRP theorem cannot prove that one tagged observable
is orthogonal to **all** dart functions.  It must prove a restricted
bilinear identity

```text
f^T K g=0 only for jointly SRP-generated pairs (f,g),                  (322)
```

while leaving enough independent correlations to separate transition
classes.  Equations (320)--(322) turn the remaining compatibility problem
into a concrete isotropy question for `K`: construct a sufficiently rich
SRP-generated subspace that is totally isotropic for the root-minus-port
matching form, without forcing that subspace into the two-dimensional
kernel (321).

## 109. Per-layer transpose is covariance, not conservation

The most immediate proposed source for the isotropic space in (322) is the
per-layer reciprocity (269).  But for a third-color block `K_d` that identity
is simply

```text
mu^T K_d w = w^T K_d^T mu,                            (323)
```

which holds for **every** matrix `K_d`.  It relates a routed occurrence to
the formally transposed block; it imposes no linear equation on the block
and no equality between the weights with which the two orientations occur
in the global dart ledger.

The Hadamard characters (278) have the same status.  Under transpose,
`alpha_d` is even and `beta_d` is odd, so an equal-weight pair of transposed
occurrences cancels `beta_d`.  But the existence of that equal-weight pair
is exactly the route-reversibility conclusion (307), not an input supplied
by (323).  In particular a single occupied diagonal cell has nonzero
`alpha_d` and is fixed by transpose; all transpose formulas hold while its
correlation residue survives.

Therefore the span of the formal transpose relations cannot be inserted as
`W` in (322).  Doing so would turn covariance of labels into equality of
occurrence weights and make the reversal-rigidity argument circular.  The
same warning applies to the run-reversal character `C`: reorienting a word
changes its description but does not create a second realized occurrence.

What is still needed is an **occurrence-level self-indexing identity**:

```text
an SRP-derived balance on the realized root/port pair ledger whose terms
are individually resolved by third color and intermediate fiber.        (324)
```

Only (324) can prove a nontrivial instance of `f^T K g=0`; (269), (278), and
(283) then identify how its resolved columns transform under reversal and
can be used for privacy.  Section 84's abstract counterprofile is consistent
with every covariance law above and violates the desired parity, confirming
that covariance alone is insufficient.

## 110. The dart correlation defect is a row--column Gram difference

There is nevertheless an exact occurrence-level identity once the dart
observables themselves are fixed.  Identify `D_ce` with the support of the
incidence matrix `B=R_ce`.  For functions `f,g` on its darts, write

```text
r_f(x)=sum_(p:B_xp=1) f(x,p),    c_f(p)=sum_(x:B_xp=1) f(x,p),
```

and similarly for `g`.  Expanding the two matchings in (318) gives

```text
D_(f,g) = <r_f,r_g> - <c_f,c_g>.                       (325)
```

Indeed the row product `<r_f,r_g>` contains the root-matching cross terms
plus `sum_(x,p) f(x,p)g(x,p)`.  The column product contains the port-matching
cross terms plus the identical diagonal sum, which cancels.  Equation (325)
holds over the integers and uses only that every row and column of `B` has
degree two.

For a third color `d != c,e` and a specific intermediate port `y in d`,
define the triangle-incidence observable

```text
F_(d,y)^(c,e)(x,p)
  := R_ce(x,p) R_cd(x,y) R_de(y,p).                    (326)
```

Its value at a dart `(x,p)` is one exactly when the incidence edge `x--p`
belongs to the rooted `c--d--e` triangle with intermediate `y`.  Summing
over `y in d` recovers `R_ce hadamard (R_cd R_de)`, and uniqueness ensures
the summands have disjoint support.  Thus (325) applied to
`F_(d,y),F_(f,z)` is a fully color- and intermediate-resolved
two-local SRP correlation, not a one-port potential.

Component-pair reversal transposes every ingredient:

```text
F_(d,y)^(e,c) = (F_(d,y)^(c,e))^T.
```

It swaps row and column degree profiles, so

```text
D_(F_(d,y),F_(f,z))^(e,c)
  = -D_(F_(d,y),F_(f,z))^(c,e).                       (327)
```

Consequently the complete ordered-component ledger has the genuine
conservation law

```text
sum_(c != e) D_(F_(d,y),F_(f,z))^(c,e) = 0            (328)
```

whenever the labels `d,f` are retained under the reversal (with terms absent
when a label is an endpoint component).

This is the first nonseparable conserved correlation on the **doubled
ordered-component ledger** in the SRP lane.  Its scope is also exact: (328)
pairs the `(c,e)` ledger with the reversed
`(e,c)` ledger globally.  The marked-parity target is localized to one fixed
owner pair and one projected cycle, so global antisymmetry alone may cancel
the desired residue against a different component-pair ledger.  The next
localization problem is to refine (325)--(328) by the root-marked primitive
or target-incidence component so that the reversed term is forced back into
the same realized reversal class rather than merely another ordered pair.

## 111. Triangle-correlation conservation is dart-cyclewise dual

The localization loss in (328) is smaller than it first appears.  A cycle
`Z` of the two involutions on `D_ce` is a connected component of the
incidence support `R_ce`.  Transposition sends each dart `(x,p)` to `(p,x)`
and identifies it with a cycle `Z^T` in `D_ec`; under this identification the
root and port matchings exchange:

```text
R_(ec)|_(Z^T) = P_(ce)|_Z,
P_(ec)|_(Z^T) = R_(ce)|_Z.                             (329)
```

Restrict the triangle indicators (326) and their row/column degree profiles
to one such component.  The proof of (325) is componentwise, so (327)
sharpens to

```text
D_(F_(d,y),F_(f,z))^(e,c)[Z^T]
  = -D_(F_(d,y),F_(f,z))^(c,e)[Z].                    (330)
```

Both sides are available in the same ambient routing partition: they are the
two shore descriptions of one physical incidence cycle, not unrelated
matrices.  Thus the doubled resolved triangle-correlation ledger has exact
**cyclewise dual conservation**.  As in Section 109, this dual
re-description alone does not impose an equation on either one-sided
ledger.

What (330) does not prove is one-sided vanishing.  Contracting `R` describes
the `c`-root owner cycle `F_e[c]`, while contracting `P` describes its
port-shadow cycle in `B_ec` (equivalently the dual `e`-root description
after transposition).  The original parity target grades marked `P`-pairs
as edges of the first contraction; transposition turns them into marked
`R`-pairs in the second.
Their residues may be equal and opposite without either being zero.

The remaining localization theorem is therefore a self-duality statement,
not a search for a second occurrence:

```text
on each dart cycle Z, identify the marked-grading correlation extracted
from the R-contraction with the corresponding correlation extracted from
the P-contraction.                                      (331)
```

Combining (331) with the sign reversal (330) over a field of characteristic
not two would force that correlation to vanish.  The cross-color compatible
root-marked primitives are now needed precisely to prove (331): they must
show that the two contractions assign the same resolved triangle-census
value to the physical cycle.  This is strictly narrower than constructing
an arbitrary conserved `Phi` and avoids the circular occurrence-pairing
problem of Section 109.

## 112. Double aggregation returns to the old symmetric blind spot

One might try to use the ordered-pair conservation (328) by summing the
target (296) over every root component `c`.  This cannot close the directed
parity.  The resulting owner count is

```text
sum_c sum_(e != c) p_ce
  = sum_({c,e}) (p_ce+p_ec).                           (332)
```

But the unordered summands on the right are exactly those in the first SRP
trace contraction (48):

```text
2(p_ce+p_ec)+sum_(d != c,e) tau_ced=4q.
```

Thus the parity of (332) is already determined by the unoriented
three-component triangle inventory.  Section 10 identified this as the
precise blind spot: symmetric pair sums do not imply the directed row
parity

```text
sum_(e != c) p_ce = 0                                  (333)
```

required for each fixed `c`.  Different directed rows may carry odd residues
that cancel in (332).

Consequently the doubled conservation (328), although genuinely
two-local and intermediate-resolved, is not load-bearing until it is
localized before the `(c,e)+(e,c)` symmetrization.  The self-duality target
(331) must operate at fixed `c` (and ultimately on the fixed projected
obstruction cycle), or an equivalent nonsymmetric root-marked contraction
must retain the direction of owner transfer.  Summing (296) further would
only reproduce a theorem already available from (48).

## 113. Intermediate-pair correlations are private but not one-sided conserved

The fully resolved triangle coordinates of Section 110 have the strongest
possible local privacy.  Fix an intermediate port `y`.  The support of
`F_(d,y)^(c,e)` is a partial matching between `c` and `e`: two supported
entries in one row would give two common neighbors of the adjacent pair
`x,y`, and two in one column would give two common neighbors of the adjacent
pair `p,y`, in either case producing a four-cycle.  Hence its row and column
degree profiles are binary.

For two distinct intermediate ports `y,z`, equation (325) becomes

```text
D_(y,z)
  = |{x in c : r_y(x)=r_z(x)=1}|
    - |{p in e : c_y(p)=c_z(p)=1}|.                   (334)
```

Each set has order at most one, since its element is a common neighbor of
`y,z`.  They cannot both be nonempty: a root `x in c` and a port `p in e`
would be two distinct common neighbors of the same pair.  Therefore

```text
D_(y,z) in {-1,0,1},                                  (335)
```

and every nonzero value has a unique rooted (`+`) or port (`-`) witness.
The pair `{y,z}` is thus a private coordinate for that two-local transition;
the opposite sign occurs only in the transposed shore description of the
same witness.

This proves the privacy half of (309) for the `V--V` triangle-pair sector at
maximal intermediate resolution.  It also shows why conservation cannot
hold coordinatewise on the one-sided fixed-`c` ledger.  A rooted through-turn
with intermediates `y,z` contributes `D_(y,z)=+1`; a port turn contributes
`-1`.  Such locally permitted states would be individually forbidden by a
claim that every coordinate (334) vanishes.

Accordingly the self-duality target (331) must concern the particular
**linear combinations** of pair coordinates selected by the marked grading
and the compatible root primitives, not equality of the entire maximally
resolved vector.  The tension is now explicit:

```text
maximal intermediate resolution gives private rows but no fixed-c balance;
SRP-compatible combinations may balance but must retain enough of (334)
to separate the reversal classes relevant to omega_M.                  (336)
```

Switch handoffs and `H--V` boundaries are not covered by (334); they require
their own two-local coordinates.  Thus (334)--(336) close the privacy audit
for genuine triangle turns while isolating both remaining sectors and the
exact conservation-versus-resolution tradeoff.

## 114. The H marginal gives a fixed-cycle boundary correlation identity

Let `H` be the zero--one observable of H-decorated darts on one mixed dart
cycle `Z`, and let

```text
V := sum_(d,y) F_(d,y)
```

be its intermediate-resolved triangle observable.  The Section 99 alphabet
is exclusive, so `H` and `V` have disjoint dart support.  More strongly, a
port pair is either `H--H` or contains no H dart; hence the port-matching
cross correlation of `H` and `V` is zero.  The root-matching cross
correlation is exactly the number `b_HV(Z)` of `(H,V_(d,y))` boundary roots.
Therefore

```text
D_(H,V)[Z] = b_HV(Z),
D_(H,F_(d,y))[Z]
  = number of H--V boundaries with intermediate (d,y). (337)
```

Let `h_R(Z)` and `h_P(Z)` be the numbers of `H--H` root and port pairs.
The parity of the latter is `omega_M(Z)`.  Polarization with `f=g=H`
gives

```text
D_(H,H)[Z] = 2(h_R(Z)-h_P(Z)).                        (338)
```

Count H darts through the two matchings.  Every port H-pair contributes two;
on the root side an H-pair contributes two and an H--V boundary contributes
one.  Thus

```text
2h_P(Z)=2h_R(Z)+b_HV(Z),
D_(H,H)[Z]+D_(H,V)[Z]=0.                              (339)
```

Equation (339) is an exact, one-sided, fixed-cycle correlation balance.  It
does not use the transposed component ledger and therefore supplies a first
nontrivial instance of the occurrence-level identity (324).  Moreover (337)
retains the full intermediate label at each boundary before the final sum.

The identity is not yet the parity theorem: it rewrites the marked count as

```text
h_P(Z)=h_R(Z)+b_HV(Z)/2,                              (340)
```

so the parity still depends on the number of run-interior root pairs and on
half the boundary count.  But it connects exactly the two sectors separated
in Section 100: the H-run grading and the labeled gap endpoints.  Switches
do not occur in (339), because an H dart is root-paired only with H or V and
port-paired only with H.  Their contribution remains confined to transport
inside the non-H gaps.

## 115. The S marginal gives the dual switch-handoff balance

Let `S` be the switch-dart indicator on the same mixed cycle.  At a root,
an S dart occurs only in an `S--S` pair, so the root-matching cross
correlation of `S` and `V` is zero.  At a port, an S dart is paired with S or
with a labeled V dart.  Therefore

```text
D_(S,V)[Z] = -b_SV(Z),
D_(S,F_(d,y))[Z]
  = - number of port S--V handoffs with intermediate (d,y), (341)
```

where `b_SV(Z)` is the total number of S--V port pairs.

Let `s_R(Z)` count S--S root pairs (the rooted switches) and `s_P(Z)` count
S--S port pairs.  Then

```text
D_(S,S)[Z] = 2(s_R(Z)-s_P(Z)).                        (342)
```

Counting S darts through the two matchings gives

```text
2s_R(Z)=2s_P(Z)+b_SV(Z),
D_(S,S)[Z]+D_(S,V)[Z]=0.                              (343)
```

Thus switch handoffs also satisfy an exact one-sided, fixed-cycle
correlation balance, with their intermediate labels retained in (341).
Together, (339) and (343) account for every mixed pair involving H or S:
H never meets S under either matching, H meets V only at roots, and S meets
V only at ports.  The only correlations not reduced to a marginal identity
are the genuinely two-local V--V turns of Section 113.

Equivalently, the full H/V/S pairing-defect matrix has zero row sums because
the root and port matchings have the same one-dart marginals.  Sections 114
and 115 make the H and S rows explicit; the V row is their negative.  Hence
any new conserved/private invariant must refine the internal labels of the
V--V block rather than introduce another unlabeled alphabet count.

## 116. The V--V residual is a signed one-chain with explicit boundary

Let `L` be the set of fully resolved V labels `ell=(d,y)`.  On a fixed dart
cycle `Z`, form an integer one-chain in the free module on unordered pairs
of distinct labels:

```text
C_V(Z)
  := sum_(V_ell--V_m root pairs) [ell,m]
     - sum_(V_ell--V_m port pairs) [ell,m].            (344)
```

The labels in a pair are distinct: two triangles through the same
intermediate port would give the corresponding adjacent endpoint pair two
common neighbors.  By Section 113, the coefficient of `[ell,m]` in (344) is
exactly the private correlation coordinate
`D_(F_ell,F_m)[Z]`.

Give an unoriented label edge the incidence boundary

```text
partial[ell,m] := [ell]+[m].
```

For each label `ell`, let `h_ell(Z)` count root H--V_ell boundaries and let
`s_ell(Z)` count port S--V_ell handoffs.  Count V_ell darts through the two
matchings:

```text
deg_R^V(ell)+h_ell(Z)
  = deg_P^V(ell)+s_ell(Z).
```

Therefore the V--V correlation chain has the exact boundary

```text
partial C_V(Z)
  = sum_(ell in L) (s_ell(Z)-h_ell(Z))[ell].           (345)
```

Summing coordinates in (345) recovers the unlabeled marginal balances of
Sections 114--115, but (345) retains every third color and intermediate
port.  It shows that the V--V block is not an arbitrary family of private
residues: it is a signed label flow whose only sources are switch handoffs
and whose only sinks are marked-run boundaries.

The gap-holonomy target can now be stated without an unspecified transfer.
Construct a boundary-transfer chain `T(Z)` from the labeled non-H gaps such
that

```text
partial T(Z)
  = sum_ell (h_ell(Z)-s_ell(Z))[ell].                  (346)
```

Then `C_V(Z)+T(Z)` is a closed label-chain.  Route reversal negates `C_V`,
and the desired `theta_j` are precisely the signs obtained by transporting
along the components of this closed chain.  The remaining compatibility
theorem must ensure that `T` is canonical and has trivial total holonomy;
existence of some abstract chain with boundary (346) is not enough.

Equations (344)--(346) combine the two halves of the live problem:
intermediate-pair coordinates give private edges, while the H/S marginal
identities give their exact conservation defect.  No additional unlabeled
count can refine this boundary; the missing datum is the canonical
root-marked routing of each labeled source to a labeled sink.

## 117. H-runs and S-paths supply the canonical closing transfer

The transfer chain requested in (346) already exists combinatorially.  Keep
only H darts and the matching edges whose two endpoints are H.  On a mixed
dart cycle its components are the maximal H-runs; each is a path with two
root H--V boundary darts.  If their resolved V labels are `ell,ell'`, attach
the label edge `[ell,ell']`.  Summing these edges over the H-runs gives

```text
T_H(Z),       partial T_H(Z)=sum_ell h_ell(Z)[ell].    (347)
```

Likewise keep only S darts and S--S matching edges.  Every nontrivial path
component has two port S--V handoffs; S-only cycle components have no
boundary and contribute nothing.  Joining the two resolved V labels at the
ends of each S-path gives

```text
T_S(Z),       partial T_S(Z)=sum_ell s_ell(Z)[ell].    (348)
```

Both pairings are canonical subgraphs of the one realized dart cycle—no
choice of path decomposition or formal reverse occurrence is involved.
Therefore

```text
T(Z):=T_H(Z)-T_S(Z),
partial T(Z)=sum_ell(h_ell(Z)-s_ell(Z))[ell],
partial(C_V(Z)+T(Z))=0.                               (349)
```

This upgrades Section 116: existence and canonicity of the closing transfer
are proved.  The closed chain

```text
Xi(Z):=C_V(Z)+T_H(Z)-T_S(Z)                           (350)
```

retains every intermediate pair on V--V turns, every pair of marked-run
boundary labels, and every pair of switch-handoff labels.

Here the pair module is enlarged to allow a diagonal generator `[ell,ell]`
with boundary `2[ell]`, since the two ends of an H-run or S-path may carry
the same resolved label.  Equivalently one may first distinguish the two
endpoint occurrences and then project to labels.  No injectivity is claimed
for the transfer edges; privacy remains supplied by the V--V coordinates of
Section 113.

The remaining gap theorem is now precisely:

```text
the canonical closed chain Xi(Z) has trivial signed holonomy in the
marked-grading character.                              (351)
```

The root-marked primitive compatibility is no longer needed to manufacture
or close a transfer chain.  Its sole job is to evaluate the homology class
of the explicit chain (350) and prove (351).  This is the narrowest
direction-sensitive formulation reached so far.

## 118. Holonomy vanishes if the marked primitive descends to labels

Let `E_Xi` denote the occurrences of the four edge types in (350): root and
port V--V pairs, H-run transfers, and S-path transfers.  The run/routing
calculus assigns each occurrence an additive phase

```text
a:E_Xi -> F_2,
```

with an H-run of length `ell` carrying `ell mod 2` and the other edge types
carrying their resolved route/switch characters from Sections 88--93.  The
marked holonomy in (351) is the pairing `<a,Xi(Z)>`.

A sufficient closing datum is now completely explicit: a function on
resolved intermediate labels

```text
chi:L -> F_2                                           (352)
```

such that, with the coefficient sign of the corresponding edge in (350),

```text
a[ell,m] = chi(ell)+chi(m)                             (353)
```

for every edge occurrence.  Since `partial Xi=0`, incidence duality gives

```text
<a,Xi> = <delta chi,Xi> = <chi,partial Xi> = 0.        (354)
```

Thus (352)--(353) imply (351), and then the Section 100 phase equation forces
`omega_M(Z)=0`.

There is also a branch restriction: the canonical primitives (91) were
constructed for the odd closed owner run of Sections 21--27, an entire
`A_c` cycle.  A mixed dart cycle `Z` need not be such a run.  Even in their
native all-horizontal setting, the primitives do **not** assign values at full
resolution: they are indexed by routing color `d` and target incidence
component `V_j`, and sum over the intermediate ports `y in d`.  They provide
the required aggregate occurrence values but not a value for each `(d,y)`.
The compatibility task therefore has two exact stages:

```text
atomization: lift phi^(d,j) to intermediate-resolved occurrence values;
descent:     equal (d,y) occurrences receive the same normalized value.
```

If both hold, that common value is a candidate `chi(d,y)`.  One must still
identify the atomized version of (92) with the phase cochain in (353); that
identification is an additional requirement, not a formal consequence of
atomization.

This also identifies the obstruction sharply.  A primitive may satisfy all
local coboundary equations and still fail to descend because two occurrences
of the same `(d,y)` receive different values.  The target-component sum
(94) and routing-color aggregate (97) constrain those disagreements, while
Section 27 shows that their component compression is alternating with zero
row sums.  Its surviving within-component fluctuation is precisely the
aggregate shadow of non-descent; scalar component tests cannot remove it.

Consequently the final compatibility lemma is not another parity sum:

```text
ATOMIZED LABEL DESCENT: the canonical primitive admits an
intermediate-resolved lift constant on every fiber
{V occurrences on Z} -> {(d,y)}.                       (355)
```

Equation (355), together with a verified phase identification for (92),
would be a direct and checkable route to the holonomy theorem.  It may be
weakened to descent only modulo the annihilator of the particular closed
chain `Xi`, but full fiber constancy is the clean uniform target.

There is an immediate falsification checkpoint.  On a diagonal transfer
edge `[ell,ell]`, every label coboundary has value
`chi(ell)+chi(ell)=0`.  Hence (353) requires any H-run or S-path whose two
ends have the same resolved label to carry trivial phase.  An odd-phase
same-label transfer would refute full descent and force the weaker
annihilator formulation.  This condition is not asserted here; it is the
smallest concrete test of (355).

## 119. In the closed-owner-run branch, the primitive atomizes explicitly

Within the closed-owner-run context of Section 25, the first stage of (355)
can be carried out directly.  Fix `d,j` and, for every `y in d`, put

```text
t_y := (R_de V_j)(y)                                  (356)
```

over `F_2`.  Define the intermediate-resolved pieces

```text
r_(i,y) := R_cd(x_i,y) t_y,
w_y(z)  := R_ed(z,y) t_y,
phi_(i,y)
  := r_(i,y)+r_(i+1,y)+w_y(z_i).                      (357)
```

Then

```text
sum_(y in d) r_(i,y)=r_i^d.
```

Also `F_d[e]=R_ed R_de-2I` over the integers, so modulo two

```text
sum_(y in d) w_y = R_ed R_de V_j = F_d[e]V_j=w^d.
```

Consequently (357) is an exact atomization of (91):

```text
sum_(y in d) phi_(i,y)=phi_i^(d,j).                   (358)
```

Taking the adjacent derivative before summing defines

```text
kappa_(i,y):=phi_(i-1,y)+phi_(i,y),
sum_y kappa_(i,y)=kappa_i^(d,j),                       (359)
```

where the last equality is (92).  Thus this intermediate lift and its local
coboundary law exist canonically; no choice of how to distribute the
displayed matrix products among the `y` labels remains.  Whether these atoms
evaluate the desired phase is separate.

This calculation does not extend (91) to a mixed dart cycle; it only exposes
the local formula that such an extension would have to refine.  The behavior
of this atomization on owner-run occurrences is concrete.  Formula
(357) says that

```text
t_y times the parity of the three incidences
x_i--y, x_(i+1)--y, z_i--y.                           (360)
```

The multiplier `t_y` depends only on `(d,y)` and the target component
`V_j`; variation lies in the displayed three-incidence parity.  The next
necessary check is its value when `(d,y)` is the actual triangle label of
the occurrence, before attempting any descent argument.

## 120. The direct owner-run atom vanishes on its own routed triangle

Suppose `(d,y)` labels the V dart `(x_i,z_i)`.  Then

```text
R_cd(x_i,y)=1,       R_ed(z_i,y)=1.
```

The other root `x_(i+1)` of the port `z_i` cannot also be adjacent to `y`:
otherwise `z_i` and `y` would be two common neighbors of the consecutive
owner-cycle roots `x_i,x_(i+1)`, producing a four-cycle.  Hence

```text
R_cd(x_(i+1),y)=0,
phi_(i,y)=t_y(1+0+1)=0.                               (361)
```

The symmetric statement holds when the labeled dart is `(x_(i+1),z_i)`.
Thus every atom (357) evaluated on the very routed triangle whose label it
was meant to distinguish is zero.

This is a decisive scope correction.  The atomization (356)--(359) is an
exact decomposition of the aggregate canonical primitive, but its diagonal
on-occurrence restriction cannot be the nontrivial label potential `chi` in
(352).  Nonzero aggregate values come from **off-occurrence** intermediates,
and the identity (92) mixes those off-route atoms before summing over `y`.

Consequently, even in the native owner-run branch, the holonomy character
cannot be obtained by assigning
`chi(d,y)=phi_(i,y)` at the occurrence carrying `(d,y)`.  A viable use of
the primitive must instead retain an off-occurrence secondary-fiber census
and cross-tag it with the actual route—the same source/consumed-feature
structure as the B3 bundle (12rb).  Equation (361) explains why the
secondary fiber, rather than the routed intermediate itself, is essential.

## 121. The mixed branch has a local off-occurrence census candidate

The local wedge formula exposed by Section 120 makes sense on any mixed dart
cycle even though the global primitive (91) does not.  Fix a secondary
routing color `d`.  For **every incidence dart** `o=(x,z)` whose port mate
has other root `x'`, define

```text
f_ell(o) := [the actual resolved route label of o is ell],
q_u(o)   := t_u (R_cd(x,u)+R_cd(x',u)+R_ed(z,u)).       (362)
```

for every intermediate atom `u` in the relevant routing color.  This is a
canonical **local candidate**, not a value supplied by (91) on the mixed
cycle.  The observable `q_u` is therefore defined on H, S, and V darts; the
source indicator `f_ell` is supported only on V darts.  This full-domain
extension is what is used in Sections 128--132.  Formula (362) is symmetric
in `x,x'`, so the extension remains constant on port pairs.  On a V dart,
equation (361) still says `q_ell(o)=0` for its actual route label; nonzero
entries of `q(o)` are off-occurrence secondary-fiber atoms.

For a matching pair `{o,o'}`, define the cross-tagged feature coordinate

```text
Gamma_(ell,u)(o,o')
  := f_ell(o) q_u(o') + f_ell(o') q_u(o).              (363)
```

This records the actual route label on one endpoint together with the
secondary census exposed at the other endpoint.  It is genuinely two-local:
neither marginal determines the product.  It is also the literal SRP
analogue of (12rb), where a source signature tags the bundle consumed by its
transition partner.

Summing (363) over root pairs and subtracting the port-pair sum gives

```text
Delta_(ell,u)(Z)
  = D_(f_ell,q_u)[Z]
  = <r_(f_ell),r_(q_u)>-<c_(f_ell),c_(q_u)>.           (364)
```

Thus the entire cross-tagged bundle boundary is an instance of the exact
Gram identity (325).  Shore transpose exchanges the two matching sums and
negates every coordinate, so route oddness is automatic.  Unlike the direct
atom, (363) can be nonzero precisely because it evaluates `q_u` away from
the route carrying `ell`.

Equation (364) supplies a concrete finite feature matrix for the two open
tests in (309):

```text
conservation: the primitive identities force the realized Delta-ledger
              to vanish in the marked-character quotient;
privacy:      the nonzero columns Delta(o,o') are independent, or each
              owns a source-label/secondary-atom coordinate.             (365)
```

Neither assertion in (365) is claimed yet.  The gain is that all coarser
and diagonal candidates have been eliminated, while (362)--(364) define the
unique surviving cross-tag shape directly from existing SRP data.  A
counterexample to privacy must now exhibit two distinct transitions with
the same actual route label and the same off-occurrence primitive census;
a conservation proof must produce a mixed-cycle identity analogous to (92)
before the `u`-sum erases those tags; (92) itself is not available here.

## 122. Secondary atoms are exactly singly incident off-route fibers

Formula (360) has a direct combinatorial classification.  Fix the port edge
with roots `x_i,x_(i+1)` and port `z_i`.  For an intermediate `u`, C4
freeness forbids adjacency to both roots: they already have the common
neighbor `z_i`.  It also forbids adjacency to all three vertices.  Hence the
incidence count of `u` on

```text
{x_i,x_(i+1),z_i}
```

is zero, one, or two.  The two-incidence case consists of `z_i` and exactly
one root, so it is precisely a routed triangle through that dart.  Modulo
two, (360) therefore says

```text
q_u(o)=1
iff t_u=1 and u is adjacent to exactly one of
    x_i,x_(i+1),z_i.                                  (366)
```

Zero-incidence atoms contribute nothing, and routed two-incidence atoms
cancel.  Thus `q(o)` is literally the census of target-active intermediates
which touch the occurrence wedge exactly once—the off-route secondary
fibers predicted in Section 120.

The cross-tag coordinate `(ell,u)` in (363) now has a concrete meaning:
the transition uses actual rooted route `ell` at one endpoint and exposes a
singly incident target-active secondary fiber `u` at the other.  A privacy
collision can occur only if two distinct transitions use the same actual
route label and expose the same singleton secondary incidence.  Proving
that C4/linearity forbids such a collision (or classifying its exceptional
forms) is the exact SRP counterpart of the private-external-row theorem
suggested after (12rh).

## 123. Privacy collisions are confined to opposite-root exposures

Fix an actual route label `ell=(d,y)` on a dart `(a,p)`, and let `b` be the
other root of the same port.  The occurrence wedge is `{a,b,p}` with

```text
y adjacent to a and p,       y not adjacent to b.      (367)
```

Let `u` be a secondary atom with `q_u=1`, so by (366) it is adjacent to a
unique wedge vertex `v`.  Call the exposure **endpoint** when
`v in {a,p}` and **opposite-root** when `v=b`.

Suppose two distinct occurrences with the same actual label `y` and the same
secondary `u` are both endpoint exposures, at vertices `v_1,v_2`.  The
partial-matching property of `F_(d,y)` makes the two actual roots distinct
and the two actual ports distinct, so `v_1 != v_2` (cross-shore vertices are
also distinct).  But both `v_1,v_2` are adjacent to `y` by (367) and to `u`
by the exposure assumption.  They therefore have the two common neighbors
`y,u`, a four-cycle contradiction.

Hence

```text
every coordinate (ell,u) occurring only through endpoint exposures is
inter-occurrence private; any such collision has an opposite-root
exposure.                                                               (368)
```

More generally, among repeated occurrences of one coordinate, at most one
can be endpoint-exposed; all others must be opposite-root-exposed.

This proves the generic **inter-occurrence** part of the privacy obligation
in (365).  It does not exclude two transition columns sharing the same
actual-route occurrence but using its two different matching mates; those
have `v_1=v_2` and require a separate same-source comparison.  Among
distinct occurrences, the sole exceptional sector is the crossed secondary
incidence `u--b`, where the
actual label `y` uses the other root `a` and the shared port `p`.  Its
position is analogous to the crossed Hadamard channel of Sections 89--92,
but `u--b` alone is not an occupied crossed two-step route, so no `beta_d`
cancellation is claimed.  The remaining privacy audit is exactly the
classification of these opposite-root collisions.

## 124. Every exceptional privacy collision contains a labeled six-cycle

Consider two distinct opposite-root exposures of the same coordinate
`(ell,u)`, with `ell=(d,y)`.  Write their actual ports and opposite roots as
`p_1,b_1` and `p_2,b_2`.  By definition the ambient edges include

```text
y--p_k--b_k--u       for k=1,2.                       (369)
```

The ports are distinct by the column-matching property of `F_(d,y)`.  The
opposite roots are also distinct: if `b_1=b_2`, then the pair `y,b_1` would
have the two common neighbors `p_1,p_2`, a four-cycle.  Cross-shore vertices
cannot coincide.  Therefore the two paths in (369) form the simple cycle

```text
y--p_1--b_1--u--b_2--p_2--y.                         (370)
```

Its component pattern is `d--e--c--d--c--e--d`, and its two length-three
halves are precisely the two collided singleton exposures.  Thus the
distinct-occurrence collision classification is now

```text
inter-occurrence-private endpoint-exposed coordinate,
or a repeated opposite-root coordinate carrying a labeled ambient C6.   (371)
```

No contradiction follows from C4-freeness alone because six-cycles are
allowed.  But (370) moves the exceptional sector out of an abstract feature
collision and into the established sixth-moment/cycle inventory: any
failure of inter-occurrence private-row peeling must be witnessed by a repeated
`d-e-c-d-c-e` cycle with the target-activity tag `t_u=1`.  A uniform privacy
proof may therefore either exclude this labeled C6 pattern by simultaneous
routing, or treat its columns as a separate block controlled by the generic
sixth-moment identities.

## 125. The mate-decoration tag removes same-source collisions

The unresolved same-source case in Section 123 has a canonical role tag.
For a V dart `o` with actual label `ell`, let

```text
sigma_R(o) := full decoration of its root mate,
sigma_P(o) := full decoration of its port mate,
```

where a V decoration includes its resolved `(d,y)` label and H/S remain
distinct symbols.  The Section 99 alphabet gives

```text
sigma_R(o) in {H,V_m},       sigma_P(o) in {S,V_n}.    (372)
```

These two decorations are always different.  The H/S cases are immediate.
If both were the same V label `m`, then the pair of triangle indicators
`F_ell,F_m` would have both a common root (the R-pair) and a common port (the
P-pair).  Section 113 proved those two witnesses mutually exclusive by C4.

Refine (363) by retaining the mate decoration:

```text
Gamma_(ell,sigma,u)(o,o')
  := f_ell(o) [decoration(o')=sigma] q_u(o')
     + f_ell(o') [decoration(o)=sigma] q_u(o).         (373)
```

For the two transition columns incident to one fixed source occurrence `o`,
the tags are `sigma_R(o)` and `sigma_P(o)`, hence distinct by (372).  Thus
no same-source privacy collision survives in the refined bundle.

Combining Sections 123--125 gives the exact privacy split for (373):

```text
same source:       separated by the mate-decoration tag;
distinct sources: separated by C4 for endpoint exposures;
remaining case:   repeated opposite-root exposures carrying the C6 (370).
                                                                  (374)
```

The refinement is route-natural: reversing an ordered transition exchanges
the source and mate decorations, so the corresponding signed bundle
boundary remains route-odd.  Conservation is still open—the mate tag cannot
be added after summation—but the only possible failure of private-row
peeling is now the explicit labeled six-cycle sector.

## 126. A collision C6 saturates two fibers and has a 2-to-1 target profile

Retain the repeated opposite-root collision of Section 124 inside the fixed
target incidence component `V_j`.  The intermediate `y` has cross degree two
into `e`.  Since its two distinct actual ports are `p_1,p_2 in V_j`, they
exhaust that fiber:

```text
N_e(y)={p_1,p_2},       t_y=(R_de V_j)(y)=0.           (375)
```

Similarly `u` has cross degree two into `c`, and the two distinct opposite
roots on the C6 exhaust its `c`-fiber:

```text
N_c(u)={b_1,b_2}.                                      (376)
```

But `u` is a secondary atom only when `t_u=1`.  Therefore exactly one of its
two `e`-neighbors lies in `V_j`; call it `r`.  It is distinct from
`p_1,p_2`, because the opposite-root exposure says `u` is adjacent only to
`b_k` on each collision wedge.  Hence the collision carries the exact
target-component profile

```text
y uses two target ports p_1,p_2 and has target parity zero;
u uses one target port r and has target parity one.     (377)
```

Thus an exceptional repeated coordinate is a saturated block: it consumes
the full `e`-fiber of its actual label and the full `c`-fiber of its
secondary label.  In particular the same coordinate `(y,u)` cannot have a
third occurrence: the two `e`-ports of `y` are exhausted.  The privacy
failure has multiplicity exactly two and a forced `2 versus 1`
target-capacity mismatch, not an unbounded repeated column.  Different
coordinates may still reuse `u`; no label-disjointness between collision
blocks is claimed.

No contradiction from (375)--(377) is asserted.  They identify the data a
conservation proof must price: the even two-port actual bundle against the
odd one-port secondary bundle.  This is the SRP form of the one-slot
capacity-transfer deficit appearing in the exact B3 certificates
(12rm)--(12rp).

## 127. Collision blocks form stars of order at most four

For fixed `(c,e,V_j)`, form the bipartite collision graph `G_col`.  Its left
vertices are actual intermediate labels `y`, its right vertices are
secondary labels `u`, and `y--u` records that `(y,u)` is a repeated C6
coordinate of Section 126.

Every left degree is at most one.  Indeed a collision exhausts the two
`e`-ports of `y` and fixes their two opposite roots `b_1,b_2`.  If both
`y--u` and `y--u'` occurred, then `u,u'` would each be adjacent to both
`b_1,b_2`, giving that root pair two common neighbors unless `u=u'`.

Fix a right vertex `u`.  Its two `c`-neighbors `b_1,b_2` are fixed by the
degree-two fiber.  A collision neighbor `y` chooses one target port

```text
p_1 in N_e(b_1) intersect V_j,
p_2 in N_e(b_2) intersect V_j,                         (378)
```

and `y` is the common `d`-neighbor of `p_1,p_2`.  For one ordered port pair
there is at most one such `y`, by C4-freeness.  Each displayed port set has
order at most two, so

```text
deg_(G_col)(u) <=
  |N_e(b_1) intersect V_j| |N_e(b_2) intersect V_j| <= 4. (379)
```

Since every left degree is at most one, each nontrivial component of
`G_col` is therefore

```text
K_(1,s) with 1 <= s <= 4,                              (380)
```

centered at a secondary label `u`.  The exceptional privacy sector has no
cycles or higher-depth interaction: it is a disjoint union of bounded
capacity stars, each edge representing a multiplicity-two coordinate with
the 2-to-1 profile (377).

This is the precise finite residual for private-row peeling.  A uniform
argument need only price the four possible star sizes and their target-port
occupancies; no arbitrary collision hypergraph remains.  The bound four is
also the same local scale as the four-leaf switch table in the Baer lane,
where the parallel C6 collision was found.

## 128. The cross-tag boundary has a formal local derivative

The secondary observable `q_u` in (362) is indexed by the port edge, not by
one of its two darts.  Hence it is constant on every port pair:

```text
M_P q_u = q_u.                                        (381)
```

At a root, the root mate carries the value from the other incident port.
Define the adjacent root derivative, lifted to darts, by

```text
tilde_kappa_u := (I+M_R)q_u.                           (382)
```

over `F_2`.  With `K=M_R-M_P` from Section 108, subtraction equals addition
and (381)--(382) give

```text
K q_u = (M_R-M_P)q_u = (M_R+I)q_u = tilde_kappa_u.    (383)
```

Therefore the unrefined cross-tag boundary (364) has the exact local form

```text
Delta_(ell,u)(Z)
  = D_(f_ell,q_u)[Z]
  = f_ell^T K q_u
  = <f_ell,tilde_kappa_u>_Z.                          (384)
```

The bundle imbalance for actual route label `ell` and secondary atom `u` is
exactly this local derivative evaluated on the occurrences carrying `ell`.
In the closed-owner-run specialization of Sections 119--120 it agrees with
the atomized derivative (359).  On a general mixed dart cycle it is only the
formal derivative of the local candidate (362): summing it over `u` is not
known to recover the marked curvature `kappa^(d,j)` from (92).

Equation (384) identifies the remaining conservation theorem precisely:

```text
the marked-character combination of the route-selected local derivative
evaluations <f_ell,tilde_kappa_u> vanishes on Xi.       (385)
```

The mate-decoration refinement (373) must be inserted before this final
sum; (384) proves the base source-label/secondary-atom identity but does not
by itself show that every `sigma`-resolved subledger vanishes.  Nor does
(359) prove (385) outside the all-horizontal owner-run branch.  The privacy
side has only the bounded C6 stars of Section 127 left, while the mixed-cycle
conservation side remains a new SRP identity rather than a consequence of
the old primitive.

## 129. Full source-decoration resolution has exact mixed-cycle conservation

Although (92) is unavailable on a mixed dart cycle, the H/V/S partition
supplies a genuine occurrence-level balance for every local secondary atom.
Let `f_H,f_S`, and `f_ell` be the indicators of the exclusive dart
decorations.  Then

```text
f_H+f_S+sum_ell f_ell = 1_D.                           (386)
```

Both matching matrices have row and column sums one, so for every dart
observable `q_u`,

```text
D_(1_D,q_u)=1_D^T(M_R-M_P)q_u=0.                      (387)
```

By linearity, (386)--(387) give the intermediate-resolved conservation law

```text
D_(f_H,q_u)+D_(f_S,q_u)+sum_ell D_(f_ell,q_u)=0
                                                    for every u. (388)
```

The V terms in (388) are exactly the cross-tag boundaries (364).  The H and
S terms are the corresponding secondary-census correlations in the sectors
whose unlabeled marginals produced the H-run and S-path transfers of
Sections 114--117; identifying their mate-resolved pieces with those
canonical transfers is part of the marked refinement.  The **complete
decorated source ledger is conserved on every mixed dart cycle**, with no
appeal to the closed-owner-run primitive.

Equation (388) is a marginal identity and does not prove marked holonomy:
the marked character weights the H/V/S transition types differently, and
the mate-decoration refinement (373) splits terms that (388) still sums.
But it cleanly separates the remaining tasks:

```text
base conservation: proved by (388);
marked conservation: show the character-weighted and mate-resolved
                     refinement remains in the conserved subspace.       (389)
```

This is the correct mixed-branch replacement for the invalid use of (92).

## 130. Marked conservation has an exact root-transition commutator

The gap between (388) and marked holonomy can be written without choosing a
primitive.  Let `w` be any `F_2`-valued weight on darts; in the application,
`w` is constant on each fully decorated H/V/S source cell, including the
route and mate tags.  Since `M_P q_u=q_u`, its weighted secondary-census
defect is

```text
D_(w,q_u)=w^T(M_R-M_P)q_u=w^T(M_R+I)q_u.             (390)
```

Group the last expression by the unordered root pairs `{o,M_R o}`.  Each
pair contributes

```text
(w(o)+w(M_R o)) (q_u(o)+q_u(M_R o)),
```

and therefore

```text
D_(w,q_u)=sum_{root pairs {o,o'}}
             (w(o)+w(o'))(q_u(o)+q_u(o')).           (391)
```

Thus a marked weight can lose the marginal conservation of (388) only at a
root transition on which **both** its decorated source value and the local
secondary census change.  In particular, root pairs internal to one marked
source cell contribute zero, as do root pairs on which `q_u` is constant.
The unresolved contribution is supported exactly on the finite set of
H/V/S source transitions crossed by the mate-resolved labeling.

Equivalently, with the root coboundary

```text
delta_R a(o):=a(o)+a(M_R o),
```

equation (391) is the commutator identity

```text
D_(w,q_u)=sum_{{o,o'} in E_R} delta_R w(o) delta_R q_u(o). (392)
```

This identifies the correct pre-sum object suggested by all three lanes:
the joint state is not a scalar source census, but a decorated transition
type together with the secondary label `u`.  The base choice `w=1_D` has
`delta_R w=0` and recovers (387).  For the desired character weight, (392)
does not assert vanishing; it reduces marked conservation to a finite
transition ledger whose nonzero cells are precisely the ones that must be
paired with the private C4 cells or priced inside the bounded C6 stars of
Section 127.

## 131. The primary marked character is supported only at H--V boundaries

First forget the mate tag and let a primary weight have values

```text
alpha_H, alpha_S, and alpha_ell on V_ell.              (393)
```

The exhaustive root-pair list (297) consists only of `H--H`, `H--V_ell`,
`V_ell--V_m`, and `S--S`.  Substituting that list into (391), the equal-type
`H--H` and `S--S` pairs have zero weight jump.  Hence

```text
D_(alpha,q_u)
 = sum_(H--V_ell roots)
     (alpha_H+alpha_ell) delta_R q_u
   + sum_(V_ell--V_m roots)
     (alpha_ell+alpha_m) delta_R q_u.                 (394)
```

There is no primary switch term: an `S` dart is root-paired only with `S`.
In particular, for the binary marked-source character

```text
alpha_H=1,    alpha_S=alpha_ell=0,
```

equation (394) reduces to

```text
D_(1_H,q_u)=sum_(H--V roots) delta_R q_u.             (395)
```

Thus the primary marked defect is a run-boundary census.  Internal H roots,
switch roots, and all V--V turns vanish before any global summation.  This
is the secondary-resolved version of the H-row balance (339), now expressed
as an exact root coboundary rather than an unlabeled boundary count.

The distinction from the fully private ledger is important.  If a desired
weight `w` also depends on route labels or on the root/port mate decorations,
write

```text
w=1_H+r.
```

Then (392) gives the exact split

```text
D_(w,q_u)
 = sum_(H--V roots) delta_R q_u
   + sum_(root pairs) delta_R r delta_R q_u.          (396)
```

Consequently the bounded V--V C6 stars of Section 127 are not an obstruction
to the primary marked grading itself.  They enter only through the refinement
correction `r`, where route or mate labels distinguish the two root darts.
The remaining theorem therefore has two separately visible pieces: pair the
H--V boundary census in (395) with the H-run transfer, and price the genuinely
joint refinement commutator in the second term of (396).  Neither cancellation
is asserted here.

## 132. The H-run transfer needs a secondary-census connection

Equation (395) can be grouped canonically by the maximal H-runs used to
define `T_H` in Section 117.  Let a run `A` have boundary root pairs
`{v_-,h_-}` and `{h_+,v_+}`, where the `v` darts are V-labeled and the `h`
darts are the endpoint H darts.  Define its secondary-resolved boundary
charge by

```text
tau_u(A)
 := q_u(v_-)+q_u(h_-)+q_u(h_+)+q_u(v_+).             (397)
```

Then (395) is exactly

```text
D_(1_H,q_u)=sum_(H-runs A) tau_u(A).                  (398)
```

There is a useful transport form of the same charge.  Traverse the H-run
from `h_-` to `h_+` through its alternating root and port matching edges.
The port increments vanish because `M_P q_u=q_u`.  Telescoping the remaining
root increments therefore gives

```text
q_u(h_-)+q_u(h_+)
 = sum_(internal H--H root pairs E in A) delta_R q_u(E). (399)
```

Substitution into (397) yields

```text
tau_u(A)
 = q_u(v_-)+q_u(v_+)
   + sum_(internal H--H roots E in A) delta_R q_u(E). (400)
```

Thus the canonical label edge `[ell_-,ell_+]` contributed by `A` to
`T_H` has a canonical `q_u`-parallel transport, but its value is not in
general a function of the two endpoint labels alone.  It also carries the
integrated root derivative of the local secondary census through the run.
This is the exact mixed-cycle analogue of a connection on the transfer
edge.

Consequently the endpoint chain `T_H` from (347) closes the **label**
boundary, while the secondary-resolved marked ledger requires the enriched
edge

```text
(ell_-,ell_+; tau_u(A)).                              (401)
```

Any proof that pairs (395) using only the undecorated endpoint edge discards
the correction in (400).  In the all-horizontal owner-run branch the old
primitive can evaluate this transport, but on a mixed dart cycle (397)--
(400) are the native definition.  The remaining H-run task is therefore to
pair or price these enriched transfer edges jointly in `(A,u)`, consistent
with the transition-potential requirement found in the Baer and B3 lanes.

## 133. The internal H connection is a four-incidence atom

The full-domain convention in (362) makes the correction in (400) entirely
local.  Let an internal H--H root pair at root `x` have ports `z_1,z_2`,
and let `x_1,x_2` be their respective other roots.  Expanding (362) on its
two darts gives

```text
q_u(x,z_1)=t_u(R_cd(x,u)+R_cd(x_1,u)+R_ed(z_1,u)),
q_u(x,z_2)=t_u(R_cd(x,u)+R_cd(x_2,u)+R_ed(z_2,u)).
```

The common-root term occurs twice and cancels over `F_2`.  Hence

```text
delta_R q_u(x;z_1,z_2)
 = t_u( R_cd(x_1,u)+R_ed(z_1,u)
       +R_cd(x_2,u)+R_ed(z_2,u) ).                    (402)
```

Define the displayed four-incidence parity to be the internal connection
atom `eta_u(x;z_1,z_2)`.  Equation (400) becomes

```text
tau_u(A)=q_u(v_-)+q_u(v_+)
         +sum_(internal H roots E in A) eta_u(E).     (403)
```

Thus no unbounded run word is hidden in the primary transfer: after its two
endpoint wedge values, it is a sum of identical four-incidence local cells.
The atom is symmetric under exchanging the two ports and their opposite
roots, so it is attached to the unordered H--H root pair rather than to an
orientation of the run.

Equation (402) does **not** say `eta_u=0`.  C4-freeness constrains which of
its four incidences can coexist, but a separate classification is required
before any cancellation or privacy claim.  The remaining primary problem
is now finite and explicit: classify the nonzero `(H--H root,u)` cells of
(402), then match their sum and the two endpoint wedge values against the
joint run transfer in (403).

## 134. C4 reduces an internal connection cell to twelve raw states

Retain the notation of Section 133.  The two distinct ports `z_1,z_2`
already have the common neighbor `x`.  Therefore `u` cannot be adjacent to
both of them: otherwise `x,u` would be two common neighbors of the port
pair, producing a four-cycle.  Hence

```text
R_ed(z_1,u)+R_ed(z_2,u) is represented by at most one
actual port exposure.                                 (404)
```

Separate the four-incidence atom into

```text
rho_u(E):=R_cd(x_1,u)+R_cd(x_2,u),
pi_u(E) :=R_ed(z_1,u)+R_ed(z_2,u).
```

Here `pi_u(E)` is not merely a parity: by (404), when it is one it has a
unique side `1` or `2`.  Equation (402) becomes

```text
eta_u(E)=t_u(rho_u(E)+pi_u(E)).                       (405)
```

Before using any further incidence restrictions, the full cell is therefore
encoded by

```text
( R_cd(x_1,u), R_cd(x_2,u), port-state ),
port-state in {none, z_1, z_2}.                       (406)
```

There are at most `4*3=12` raw states, and only the states with
`t_u=1` and `rho_u(E) != pi_u(E)` contribute to the connection parity.
This is an upper-bound classification, not a realizability assertion: some
of the twelve states may be excluded by the owner/H geometry or by further
C4 constraints.

The important point is that the primary H-run correction now has the same
finite joint-label form as the other residual ledgers.  Its state records
two opposite-root incidences together with a uniquely sided port exposure;
forgetting the side collapses information in exactly the way that scalar
aggregation collapses the Baer pivot pairing and the B3 joint potential.

## 135. The six contributing H-connection states have three profiles

For a contributing atom `t_u=1`.  Because `u` has cross degree two into
`e`, this means exactly one of its two `e`-neighbors lies in the fixed target
component `V_j`.  The ports of the lifted dart cycle, including `z_1,z_2`,
lie in that component.  Thus if `pi_u(E)=1`, its uniquely exposed side is
also the unique target-component port of `u`; if `pi_u(E)=0`, that target
port lies elsewhere in `V_j`.

Let

```text
a_u(E):=R_cd(x_1,u)+R_cd(x_2,u) as an integer count in {0,1,2},
p_u(E):=number of exposed ports among {z_1,z_2} in {0,1}.
```

Equation (405) says that `eta_u(E)=1` exactly when these two counts have
opposite parity.  Among the twelve raw states of (406), the six contributing
states therefore have exactly the profiles

```text
(a_u(E),p_u(E)) in {(1,0),(0,1),(2,1)},               (407)
```

with two sided versions in each case: the unique root in the first profile,
or the unique exposed port in the last two profiles, may be on side `1` or
side `2`.  The other six raw states have `eta_u(E)=0`.

The three profiles have distinct capacity meanings:

```text
(1,0): one opposite-root incidence, target port elsewhere;
(0,1): one target port here, no opposite-root incidence;
(2,1): both c-neighbors of u are x_1,x_2 and its unique target port is here.
                                                                    (408)
```

In the last profile the two root incidences exhaust the full `c`-fiber of
`u`, while the exposed port is its unique `V_j` incidence.  It is exactly
the saturated `2 versus 1` capacity shape of the exceptional C6 block
(376)--(377), now occurring inside the primary H-run connection.  This is
an equality of local profiles, not an assertion that every `(2,1)` H cell
belongs to the C6 collision graph of Section 127.

Thus only two unsaturated singleton-transfer profiles and one saturated
profile remain.  Any uniform pricing can treat `(1,0)` and `(0,1)` as
oppositely directed unit transfers and reserve the bounded-star correction
for `(2,1)`; constructing that pairing is still open.

## 136. A saturated H-connection cell is private in its secondary label

Fix a secondary atom `u` with `t_u=1`.  Let `r` be its unique `e`-neighbor
in `V_j`, and write its two `c`-neighbors as `b_1,b_2`.  Suppose `u` occurs
in a saturated `(2,1)` cell.  Its exposed H port must be `r`; after choosing
the exposed side, the opposite root on that side is one of `b_1,b_2`, say
`b_1`.  Thus `r` is adjacent to both `u` and `b_1`.

At most one of `b_1,b_2` can be adjacent to `r`.  Otherwise the distinct
pair `u,r` would have the two common neighbors `b_1,b_2`, contradicting
C4-freeness.  Hence the exposed opposite root is uniquely determined by
`u`.  The other `c`-neighbor of `r` is then the center root `x`, so `x` is
also uniquely determined by `u`.

The unexposed side must join this fixed `x` to the remaining c-neighbor
`b_2` through an `e` port `z_2`.  There is at most one such port: two would
be two common neighbors of the pair `x,b_2`.  Therefore the whole unordered
H--H root cell is forced.  In particular,

```text
for fixed u, at most one internal H--H root E
has profile (a_u(E),p_u(E))=(2,1).                   (409)
```

The apparent left/right alternatives in (407) are only two descriptions of
the same forced unordered cell; the unique exposed port chooses its side.
Thus the saturated primary-connection sector has genuine secondary-label
privacy, stronger than the degree-at-most-four star bound for the V--V C6
sector.  This does not yet cancel its contribution: it supplies a private
unit that a conservation or capacity argument may price without collision.

## 137. The six-profile atom applies directly at every H--V boundary

Nothing in the expansion (402) used the H decoration.  For an arbitrary
root pair at `x`, with ports `z_1,z_2` and opposite roots `x_1,x_2`, the two
copies of `R_cd(x,u)` still cancel.  Consequently

```text
delta_R q_u(E)
 = t_u( R_cd(x_1,u)+R_ed(z_1,u)
       +R_cd(x_2,u)+R_ed(z_2,u) )                    (410)
```

for **every** root pair `E` on the lifted dart cycle.  Since its ports lie
in `V_j` and share `x`, the C4 and degree-two arguments of Sections 134--135
apply verbatim: every nonzero root derivative has one of the six sided
profiles (407).

Apply this directly to the H--V support in (395).  If
`N_10(u),N_01(u),N_21(u)` denote the H--V boundary root cells of the three
profiles, counted modulo two with their side retained before the count, then

```text
D_(1_H,q_u)
 = |N_10(u)|+|N_01(u)|+|N_21(u)|.                   (411)
```

This is a profile resolution of the primary marked defect itself, not only
of the auxiliary internal connection used in (400).

The privacy proof of Section 136 also did not use that the root pair was
H--H.  It used only the `(2,1)` incidences, the two degree-two fibers, and
C4.  Hence, for fixed `u`, at most one H--V boundary cell belongs to
`N_21(u)`.  The primary ledger therefore has the exact form

```text
two unsaturated sided unit-transfer families N_10,N_01,
plus one private saturated boundary unit N_21 per u.  (412)
```

The H-run transport remains useful for assembling these boundary cells into
the canonical chain `T_H`, but no classification of its internal word is
needed to know the local type of the primary defect.  The open conservation
problem is now the parity relation among the two unsaturated families and
the private saturated units in (411), followed by the separate refinement
commutator from (396).

## 138. Every secondary primary-boundary fiber has order at most seven

The two unsaturated families in (412) also have uniform fiber bounds.  Fix
`u` and consider a `(1,0)` H--V root cell.  Its unique incident opposite root
`b` is one of the two elements of `N_c(u)`.  The port `z` on that side is
one of the two elements of `N_e(b)`.  Once `(b,z)` is chosen, the other
`c`-neighbor of `z` is the center root `x`; the other `e`-neighbor of `x`
is the second port of the root pair, and that port's other root is fixed.
Thus `(b,z)` determines the whole unordered root cell, if it has the required
H--V decoration and `(1,0)` profile.  Hence

```text
|N_10(u)| <= |N_c(u)| * 2 <= 4.                      (413)
```

For a `(0,1)` cell, the exposed port is the unique target port `r` of `u`.
Choose which of the two `c`-neighbors of `r` is the center `x`.  The other
neighbor is the exposed-side opposite root; the second port at `x` and its
opposite root are then forced by the degree-two fibers.  Therefore

```text
|N_01(u)| <= 2.                                      (414)
```

Finally Section 136, applied through Section 137, gives

```text
|N_21(u)| <= 1.                                      (415)
```

Combining (413)--(415),

```text
|N_10(u)|+|N_01(u)|+|N_21(u)| <= 7.                 (416)
```

These are bounds on actual decorated H--V cells, not merely on abstract bit
patterns.  Some of the candidates counted above may fail the H--V decoration
or profile tests, so the bounds need not be sharp.  The primary marked
defect is now a disjoint union of secondary fibers of uniformly bounded
order seven, with the only saturated member private.  A terminal argument
may therefore be sought as a finite fiberwise parity/pricing lemma rather
than an unbounded run-holonomy statement.

## 139. Routing-color contraction recovers exactly the marked cubic

The contraction over all secondary atoms can be evaluated exactly.  For a
fixed third color `d`, sum (362) over `u in d`.  With `z` having roots
`x,x'`, the definitions (87), (91), and (356) give the port observable

```text
Q_d(z):=sum_(u in d) q_u(x,z)
       =r_x^d+r_(x')^d+w^d(z).                       (417)
```

It is independent of the choice of dart over `z`, as it must be from
P-invariance.  Now sum over all `d != c,e`.  Applying the rootwise identity
(95) at `x,x'`, the two copies of `s_j` and the two evaluations at `z`
cancel.  The remaining neighboring-port evaluations give
`F_c[e]A_eV_j` at `z`; (96) supplies the sum of the `w^d` terms.  Therefore

```text
sum_(d != c,e) Q_d = Theta_(c,e) V_j,                (418)
```

with `Theta_(c,e)` exactly the marked operator (98).

By bilinearity, the full secondary/color contraction of the primary defect
is consequently

```text
sum_(d != c,e) sum_(u in d) D_(1_H,q_u)
 =D_(1_H, lift_P(Theta_(c,e)V_j)).                    (419)
```

Here `lift_P` assigns the port value to both of its darts.  Using (391), the
right side is the H--V boundary sum of the root differences of
`Theta_(c,e)V_j`.

Thus the contraction suggested by the trace ledger is not a new automatic
conservation law.  It vanishes if `Theta_(c,e)V_j` is constant on the owner
port component; on an odd component, Sections 27--28 identify that
constancy with

```text
(F_c[e](F_c[e]+A_e)A_eV_j)|_Z=0,                    (420)
```

the marked cubic target (107).  Section 29 shows that the local two-shore
algebra alone does not force this condition.

Equations (417)--(420) identify the relation between the two formulations:
the seven-cell fibers of Section 138 are the fully secondary-resolved atoms
whose unweighted routing-color sum is the old marked-cubic fluctuation.
Hence summing them before applying a joint weight loses precisely the data
needed to escape the cubic counterprofiles.  A terminal must prove (420)
from the full simultaneous geometry or cancel the finer fiber cells before
this contraction; another scalar trace sum cannot suffice.

## 140. Every active secondary coordinate has a separator-or-potential dichotomy

Keep the secondary weights instead of setting all of them to one.  For a
fixed third color `d`, let `T_j` be the diagonal matrix with
`(T_j)_(u,u)=t_u`, and define the port connection operator

```text
L_d := R_ec R_cd + R_ed : F_2^d -> F_2^e.             (421)
```

For a coefficient vector `beta` on the `d`-atoms, summing the local
observables with these coefficients gives

```text
Q_beta:=sum_u beta_u q_u=L_d T_j beta.                (422)
```

Indeed the first term evaluates `R_cd(T_j beta)` at the two roots of each
port, while the second evaluates `R_ed(T_j beta)` at the port itself,
exactly as in (362).

Let `Z` be the odd target port component and put

```text
C_(d,j):= restriction_Z F_c[e] L_d T_j.              (423)
```

On an odd cycle, `C_(d,j) beta=0` says that `Q_beta` is constant on `Z`, by
the kernel calculation of Section 28.  Hence every such `beta` supplies the
genuine conserved primary relation

```text
sum_u beta_u D_(1_H,q_u)=D_(1_H,Q_beta)=0.            (424)
```

Restrict the coefficient space to the active atoms `U_j={u:t_u=1}`.  Fix
`u_0 in U_j`.  Elementary finite-dimensional duality gives exactly one of
the following alternatives:

```text
(separator)  some beta in ker C_(d,j) has beta_(u_0)=1;

(potential)  e_(u_0) lies in im C_(d,j)^T, so there is lambda on Z with
             C_(d,j)^T lambda=e_(u_0).                (425)
```

To see exhaustiveness, if no separator exists then the coordinate functional
`e_(u_0)^T` annihilates `ker C_(d,j)`, and therefore belongs to
`(ker C_(d,j))^perp=im C_(d,j)^T`.  Conversely a displayed potential makes
`beta_(u_0)=lambda^T C_(d,j)beta=0` for every kernel vector, excluding a
separator.

In the separator branch, (424) is a conserved joint-weight ledger in which
the chosen secondary fiber has coefficient one; if that fiber contains the
private saturated cell of Section 136, the relation sees it before any
routing-color aggregation.  In the potential branch, `lambda` is an explicit
dual certificate expressing that coordinate as marked connection curvature.
It can be expanded against the at-most-seven local cells of Section 138.

This dichotomy does not by itself contradict an odd marked defect: other
weighted fibers occur in the separator relation, and the potential may have
large or sign-indefinite support.  It replaces the unsupported demand for a
universal conserved weight with a guaranteed case split, exactly parallel
to the kernel-separator/two-pole-potential dichotomy in the Baer lane.  The
remaining task is to use C4 privacy and capacity to control the additional
fibers in the first branch or the support of `lambda` in the second.

## 141. A single active connection column has odd support at most five

The columns of the operator in Section 140 have a concrete sparse form.
Fix `u in U_j`, let `r` be its unique `e`-neighbor in `Z=V_j`, and write
`N_c(u)={b_1,b_2}`.  For a root `b`, its two `e`-neighbors form one edge of
the shadow cycle `F_c[e]`, so

```text
E_b:=N_e(b) intersect Z
```

has order zero or two.  Restricting the `u` column of (422) to `Z` gives

```text
Q_u|_Z = 1_(E_(b_1)) + 1_(E_(b_2)) + e_r.            (426)
```

The two root pairs `E_(b_1),E_(b_2)` are disjoint.  If a port belonged to
both, then it and `u` would have the two common c-neighbors `b_1,b_2`, a
four-cycle.  Also `r` belongs to at most one of them, by the same argument.
Therefore cancellations in (426) can only remove `r` together with its one
occurrence in a single root pair.  In particular,

```text
|supp(Q_u|_Z)| is one of 1,3,5.                       (427)
```

The corresponding connection-curvature column is

```text
C_(d,j)e_u = (F_c[e] Q_u)|_Z.                         (428)
```

Since the cycle adjacency sends each support point to two neighbors,

```text
|supp(C_(d,j)e_u)| <= 10,                             (429)
```

before possible cancellations.  Its total mass is even.

On an odd cycle the curvature column is zero exactly when `Q_u|_Z` is
constant.  The vector in (427) has odd, nonzero mass, so the only constant
possibility is `1_Z`.  Consequently

```text
C_(d,j)e_u=0  implies |Z|<=5 and Q_u|_Z=1_Z.          (430)
```

Thus on every odd target component of order at least seven, no active atom
is flat by itself: a separator in (425) must combine at least two secondary
fibers.  On the short components of orders three or five, a flat atom is
possible only in the completely classified covering case `Q_u=1_Z`, where
`beta=e_u` already gives the one-fiber conservation law (424).

This sharply localizes the two branches of (425).  The separator branch is
either a short, explicit flat column or a genuinely multi-atom dependency;
the potential branch is a parity system whose every column tests at most ten
port positions.  No bound on the total support of `lambda` is claimed.

## 142. The potential branch is an even test on the sparse port columns

Write `P_Z` for the adjacency of the odd cycle `Z`, and let `Q` be the
matrix whose active columns are the vectors `Q_u|_Z` from (426).  On the
active space, (423) is simply

```text
C_(d,j)=P_Z Q.                                        (431)
```

The kernel of the symmetric matrix `P_Z` is the constant line.  Therefore

```text
im P_Z=(ker P_Z)^perp
      ={mu in F_2^Z : sum_(z in Z) mu(z)=0}.          (432)
```

Suppose the potential alternative in (425) holds, and put
`mu:=P_Z lambda`.  Then `mu` has even mass and

```text
<mu,Q_v>=1 if v=u_0,
<mu,Q_v>=0 for every other active v.                  (433)
```

Conversely, every even vector `mu` has the form `P_Z lambda` by (432), so
any test satisfying (433) yields `C_(d,j)^T lambda=e_(u_0)`.  Thus (433) is
equivalent to the potential branch, with no loss from replacing `lambda` by
`mu`.

Using (426), each equation in (433) is the explicit five-position-or-fewer
test

```text
mu(r_v)
 + sum_(z in E_(b_1(v))) mu(z)
 + sum_(z in E_(b_2(v))) mu(z)
 = [v=u_0].                                           (434)
```

The separator branch has the dual port form

```text
sum_v beta_v Q_v is constant on Z,
beta_(u_0)=1.                                         (435)
```

Indeed (435) is exactly `P_Z Q beta=0`.  Hence (425) is the standard
circuit/cocircuit alternative for the family of sparse odd columns `Q_v`,
taken in the quotient of `F_2^Z` by the constant line:

```text
either u_0 belongs to a dependency modulo constants,
or an even port test separates Q_(u_0) from all other columns. (436)
```

This is now a purely finite incidence problem.  Every column is a target
singleton plus at most two disjoint cycle edges, while the separating test
has even total mass.  The remaining geometric input must show that either
the dependency in (435) yields a capacity-compatible conserved ledger or
the test in (434) can be supported/priced on the private boundary cells.
No such support bound is asserted here.

## 143. A saturated boundary unit has four-port localized curvature

Suppose the active atom `u` supports its private saturated H--V cell from
Section 137.  Use the notation of Section 136: the exposed target port is
`r`, its opposite root is `b_1`, the center is `x`, and the unexposed port
`z` has opposite root `b_2`.  Let `s` be the other e-neighbor of `b_1` and
let `t` be the other e-neighbor of `b_2`.  In the shadow cycle `Z`,

```text
s--r--z--t                                             (437)
```

is a four-vertex path: the three edges come respectively from the roots
`b_1,x,b_2`.  Its vertices are distinct because the two root-pair supports
in (426) are disjoint.

For this atom, both `E_(b_1)` and `E_(b_2)` lie in `Z`, and `r` belongs to
the first.  Formula (426) therefore becomes

```text
Q_u|_Z=(e_s+e_r)+(e_z+e_t)+e_r=e_s+e_z+e_t.          (438)
```

In particular every saturated atom has support exactly three; neither the
one-point nor the five-point column type of Section 141 can carry a
saturated boundary cell.

Assume first `|Z|>=7`.  Let `a` be the other cycle neighbor of `s` and `v`
the other cycle neighbor of `t`.  These are distinct from the path (437)
and from each other.  Applying the cycle adjacency to (438) gives

```text
C_(d,j)e_u=P_Z Q_u=e_a+e_z+e_t+e_v.                 (439)
```

Indeed the two contributions at `r` cancel, while the support at `s,z,t`
propagates only to the four displayed positions.  Thus the curvature of a
private saturated unit has support **exactly four**, not merely the general
upper bound ten from (429).

On a five-cycle, `a=v` and those two contributions cancel, leaving

```text
C_(d,j)e_u=e_z+e_t.                                  (440)
```

A three-cycle cannot contain the four distinct ports in (437).  Therefore
the saturated curvature is always nonzero and is localized on two ports for
`|Z|=5` or four ports for `|Z|>=7`.

This is the SRP identity-plus-localized-exception form: away from the short
neighborhood (439), the saturated column is flat, and its exceptional
support is canonically labeled by the private atom `u` and its forced H--V
cell.  Cancellation with other columns is still possible; no independence
of these curvature supports is claimed.

## 144. A saturated curvature has a private-row-or-bounded-overlap split

Let `u` be saturated and let

```text
S_u:=supp(C_(d,j)e_u),
```

so `|S_u|=2` on a five-cycle and `|S_u|=4` on every longer odd cycle by
(439)--(440).  Suppose first that some `y in S_u` belongs to no other active
curvature column:

```text
(C_(d,j)e_v)(y)=0 for every active v != u.             (441)
```

Since `(C_(d,j)e_u)(y)=1`, the singleton row potential `lambda=e_y`
satisfies

```text
C_(d,j)^T lambda=e_u.                                 (442)
```

Thus the potential branch of (425) holds with a completely local
certificate.  In the even-test formulation of Section 142,

```text
mu=P_Z e_y                                             (443)
```

is supported on exactly the two cycle neighbors of `y` and separates `Q_u`
from every other active column.

Otherwise every `y in S_u` is covered by at least one other active column.
Choose one witness `v_y != u` for each position.  Then

```text
S_u subset union_(y in S_u) supp(C_(d,j)e_(v_y)),     (444)
```

using at most four witness atoms (at most two on a five-cycle).  Each witness
comes from a `Q_(v_y)` of support at most five and a curvature column of
support at most ten by Section 141.  Hence failure of the private-row test is
confined to a bounded overlap cluster consisting of `u` and at most four
other secondary atoms.

This is not a bound on the size of a general separator circuit or dual
potential: the selected witness columns can interact with further columns
away from `S_u`.  It is an exact first localization around the private
saturated unit.  Either that unit has a two-port separating test immediately,
or every one of its exceptional curvature ports carries an explicit competing
secondary label, producing the bounded joint-label configuration that a C4
capacity argument must analyze.

## 145. The connection incidence matrix is bounded-degree on both sides

Section 141 bounds every column of `C_(d,j)` by ten.  There is also a
uniform row bound.  A row is indexed by a port `y in Z`; let `y_-,y_+` be
its two neighbors in the shadow cycle.  From `C=P_ZQ`,

```text
(C e_u)(y)=Q_u(y_-)+Q_u(y_+).                         (445)
```

For a fixed port `p`, formula (362) shows that `Q_u(p)=1` only if `u` is
adjacent to at least one member of the three-element wedge consisting of
`p` and its two c-roots.  Each of those three vertices has exactly two
neighbors in the fixed secondary component `d`.  Therefore

```text
|{u in U_j:Q_u(p)=1}| <= 6.                           (446)
```

Applying (446) to `p=y_-` and `p=y_+`, every nonzero entry in row `y` lies
in the symmetric difference of two sets of order at most six.  Hence

```text
|{u in U_j:(C e_u)(y)=1}| <= 12.                      (447)
```

This count is deliberately coarse: C4 exclusions and overlaps between the
two wedges can only lower it.  Together with (429), the bipartite incidence
graph of connection rows and active secondary columns has

```text
column degree <=10,       row degree <=12,            (448)
```

while a saturated column has degree two or four by Section 143.  Thus the
bounded-overlap alternative of Section 144 is not hiding an unbounded fan
at any exceptional port: each of its rows has at most eleven competitors
besides the saturated atom.  Connected overlap clusters can still grow by
propagation through successive rows, so (448) is not a bound on component
order or circuit length.

## 146. Every separator is an Eulerian curvature-incidence system

Each column of `C_(d,j)=P_ZQ` has even mass, because the cycle adjacency has
column sum two.  Thus every active column vertex in the bipartite incidence
graph of `C_(d,j)` has even degree (at most ten).

Let `beta` realize the separator branch of (425), and keep precisely the
column vertices with `beta_u=1`, together with all their incident row edges.
The kernel equation

```text
C_(d,j) beta=0                                        (449)
```

says that every row vertex also has even degree in this selected subgraph.
Therefore

```text
the selected row--atom incidence graph is Eulerian.   (450)
```

It decomposes into closed alternating trails.  If the distinguished atom
`u_0` is saturated, its degree in this graph is two or four by Section 143,
so it lies on a nontrivial closed-trail component; this recovers the overlap
forced by the failure of the private-row alternative in Section 144.

Moreover a support-minimal separator containing `u_0` may be taken connected.
Indeed, if the selected Eulerian graph had several components, the column
indicator of the component containing `u_0` would itself satisfy (449) and
would give a smaller separator.  Hence the minimal separator problem is a
connected Eulerian bounded-degree incidence problem, not an arbitrary linear
dependency.

One may pair the incident row edges at each atom vertex and contract that
atom to transitions between curvature rows.  Degree-two atoms give canonical
transitions; atoms of degree four or more introduce pairing choices.  Changing
those choices is a gauge transformation of the resulting closed row trails,
exactly as pairing a degree-four pivot changes the Baer quotient by a cycle.
No pairing-independent holonomy is asserted here.

Equations (448)--(450) supply the topology missing from the separator branch:
bounded local degree plus Eulerian closure.  What remains is to attach the
profile/mate labels to these closed trails and show that either their marked
holonomy cancels or a private capacity unit is consumed.

## 147. Separator parity determines the lost constant and forces coverage

For a separator `beta`, equation (435) says

```text
Q beta=c 1_Z                                           (451)
```

for some `c in F_2`.  Every active column `Q_u` has odd mass by (427), and
`Z` has odd order.  Taking total mass in (451) therefore gives

```text
c=sum_u beta_u=|supp(beta)|  (mod 2).                 (452)
```

Thus the constant killed by the curvature operator is not ambiguous:

```text
even separator support  => Q beta=0,
odd separator support   => Q beta=1_Z.               (453)
```

In the odd case, the selected column supports must cover every port of `Z`.
Since each has order at most five,

```text
|supp(beta)| >= ceil(|Z|/5).                          (454)
```

If the distinguished selected atom `u_0` is saturated, its support has order
exactly three by (438).  The remaining selected columns cover at most five
new ports each, so the sharper bound is

```text
|supp(beta)| >= 1+ceil((|Z|-3)/5)                    (455)
```

for every odd separator containing `u_0`.

Even separators are genuine zero-sum dependencies among the sparse columns;
they need not cover the cycle, so no analogous size bound follows.  Hence
the separator branch itself splits into two geometrically different
topologies: a local even circuit with `Q beta=0`, or a global odd cover with
`Q beta=1_Z`.  Both give Eulerian curvature incidence by Section 146, but
the support parity records which constant class their closed trails carry.

## 148. A two-row syndrome is a pole-to-pole trail with one parity bit

The Eulerian description extends canonically to a nonzero even syndrome.
Let `beta` be any selected active-column vector with

```text
C_(d,j) beta=e_a+e_b,             a != b in Z.         (456)
```

Every selected atom vertex still has even degree.  Equation (456) says that
the row vertices `a,b` have odd degree and every other row has even degree.
Therefore the selected incidence graph decomposes into

```text
one a--b alternating trail plus closed alternating trails. (457)
```

Equivalently, adjoining one formal edge between the two row vertices makes
the whole system Eulerian.  Pairing gauges at higher-degree atoms act only
on the choice of trail decomposition, not on the two-row boundary.

Put `q:=Q beta`.  Since `C=P_ZQ`, equation (456) is

```text
P_Z q=e_a+e_b.                                        (458)
```

The right side has even mass and hence lies in `im P_Z`.  Because
`ker P_Z=<1_Z>`, (458) has exactly two solutions, differing by the constant
vector `1_Z`.  Their total masses have opposite parity because `|Z|` is odd.
But every column of `Q` has odd mass, so

```text
sum_(z in Z) q(z)=|supp(beta)|  (mod 2).              (459)
```

Thus the parity of the selected atom support chooses uniquely between the
two possible pole-to-pole port transports.  This is the two-source analogue
of (452): after adjoining the formal pole edge, the gauge-invariant bit is
still the support parity.

No existence of a geometrically desired `beta` with syndrome (456) is
asserted.  The statement identifies its exact topology if it occurs and
provides the direct dictionary to a pair of odd boundary ledgers in the Baer
lane: two odd rows, one joining trail, Eulerian closure after one formal
edge, and one surviving parity class.

## 149. The secondary connection still needs an activation bridge from the grading

The connection theory of Sections 129--148 is conditional on a nonzero
secondary-resolved source defect.  It must not be confused with the original
marked grading.  Recall that

```text
omega_M(Z)=number of H--H port pairs  (mod 2),
```

whereas the primary connection coordinate is

```text
D_(1_H,q_u)=sum_(H--V roots) delta_R q_u.             (460)
```

The H-row identity (339) relates the **unlabeled** H--V boundary count to
the H--H root/port imbalance, but it contains no secondary observable `q_u`.
Conversely, the routing-color contraction (419) identifies the sum of (460)
with the marked-cubic fluctuation `Theta V_j`, not with `omega_M(Z)`.  No
proved equation currently gives

```text
omega_M(Z)=1  implies D_(1_H,q_u)=1 for some d,u.     (461)
```

Even if a nonzero coordinate in (461) is supplied, (411) gives three
possibilities for that fiber.  Since `|N_21(u)|` is zero or one by privacy,
an odd defect has either

```text
|N_21(u)|=1,  with arbitrary unsaturated parity; or
|N_21(u)|=0,  and |N_10(u)|+|N_01(u)| is odd.         (462)
```

Thus saturation is not forced merely by nonvanishing.

The unresolved activation alternatives for an odd-graded mixed cycle are
therefore:

```text
A0: every secondary coordinate (460) vanishes;
A1: some coordinate is nonzero only through an odd unsaturated imbalance;
A2: some coordinate contains the private saturated unit.               (463)
```

Sections 140--148 give strong separator/potential and trail structure in A2,
and their linear machinery also applies to an A1 coordinate once a chosen
source fiber is specified.  They do not exclude A0 or show that A2 occurs.

A complete terminal must now do one of two things: construct a marked/mate-
resolved character identity that sends odd `omega_M` into the secondary
connection ledger and handles all three cases, or prove directly that A0 and
A1 have even marked grading, leaving A2 as the only source.  This activation
bridge is logically prior to using the private saturated capacity unit as a
contradiction.

## 150. Activation is an explicit boundary-column span problem

The weakest bridge needed to rule out A0 can be stated linearly.  Choose an
orientation of the mixed dart cycle.  For each maximal H-run `A` of length
`ell(A)`, call its two H--V root pairs the entry and exit boundaries.  Define
a binary vector on the H--V boundary set by

```text
alpha_Z(entry(A)):=0,
alpha_Z(exit(A)) :=ell(A) mod 2.                       (464)
```

Then, directly from (299),

```text
sum_(H--V boundaries E) alpha_Z(E)=omega_M(Z).        (465)
```

Let `B_Z` be the boundary-by-secondary matrix whose `(E,(d,u))` entry is

```text
B_Z(E,(d,u)):=delta_R q_u(E).                         (466)
```

Its column sum is exactly `D_(1_H,q_u)` by (395).  Therefore the span
statement

```text
alpha_Z=B_Z beta                                      (467)
```

for some coefficient vector `beta` would imply

```text
omega_M(Z)=sum_(d,u) beta_(d,u) D_(1_H,q_u).          (468)
```

In particular, odd `omega_M` would force at least one nonzero secondary
coordinate, excluding A0 and proving the missing implication (461).

Equation (467) is not orientation-free.  Reversing the cycle exchanges the
entry and exit of each run.  If `alpha_Z^rev` is the reversed choice, then

```text
alpha_Z+alpha_Z^rev
 =sum_(H-runs A) (ell(A) mod 2)
    (e_(entry(A))+e_(exit(A))).                       (469)
```

The right side is the weighted incidence boundary of the canonical H-run
transfer edges in `T_H`.  Thus the reversal ambiguity is itself a known
run-endpoint boundary; it is not an arbitrary choice, but it cannot be
discarded by an untagged scalar sum.  The mate/orientation refinement from
(373) is exactly the natural enlargement of `B_Z` in which to seek a
reversal-compatible version of (467).

No span inclusion is proved here.  It is a concrete activation target:
either show the oriented run-phase vector lies in the secondary boundary
column span (with the reversal change absorbed by `T_H`), or exhibit a dual
boundary test annihilating every secondary column but detecting `alpha_Z`.
The latter would be a rigorous obstruction showing that the present
secondary alphabet is insufficient and must be enlarged.

## 151. Quotienting by H-run boundaries makes activation orientation-free

Let `partial_H` be the boundary-by-run incidence matrix of the canonical
H-run transfer graph:

```text
partial_H e_A=e_(entry(A))+e_(exit(A)).               (470)
```

Changing which endpoint of one run is called its exit changes the vector
`alpha_Z` by `(ell(A) mod 2) partial_H e_A`.  In particular (469) says that
global reversal changes `alpha_Z` by an element of `im partial_H`.
Therefore the quotient class

```text
[alpha_Z] in F_2^(H--V boundaries) / im partial_H     (471)
```

is independent of all endpoint-orientation choices.

The natural activation target is consequently the weaker, invariant span
condition

```text
alpha_Z=B_Z beta+partial_H gamma                      (472)
```

for some secondary weights `beta` and run weights `gamma`, equivalently
`[alpha_Z] in im [B_Z]` in the quotient (471).  Every column of `partial_H`
has mass two, so summing (472) still gives exactly

```text
omega_M(Z)=sum_(d,u) beta_(d,u) D_(1_H,q_u).          (473)
```

Thus (472), just like the stronger (467), excludes A0 when the grading is
odd, but it does not require an arbitrary orientation convention to be
encoded by the secondary atoms.

The dual obstruction is also explicit.  Condition (472) fails exactly when
there is a boundary test `lambda` such that

```text
partial_H^T lambda=0,
B_Z^T lambda=0,
<lambda,alpha_Z>=1.                                   (474)
```

The first equation says `lambda` takes equal values at the two ends of every
H-run; hence it is itself reversal-insensitive.  The second says it kills
every current secondary boundary column, while the last says it detects the
marked run-phase class.  Such a test would prove that even the present
mate-unrefined secondary alphabet cannot activate `omega_M` modulo canonical
endpoint payments, pinpointing exactly where the mate decoration (373) must
enlarge `B_Z`.

No claim is made that (472) always holds or that a test (474) exists.  The
gain is a canonical, orientation-free primal/dual formulation of the single
gating statement identified in Section 149.

## 152. Decoration projections give a canonical noncommuting activation alphabet

The mate refinement suggested after (469) has an exact operator form.  For
each dart decoration `tau` in the H/S/V alphabet of Section 125, let `P_tau`
be the diagonal projection onto darts carrying `tau`.  For a secondary atom
`q_u`, define its decoration-resolved root derivative by

```text
widehat_kappa_(tau,u):=(I+M_R)P_tau q_u.              (475)
```

This is genuinely a projected, noncommuting derivative: in general
`M_R P_tau != P_tau M_R`, because root mates need not have the same
decoration.  On a root pair `E={o,M_R o}`, its common value is

```text
widehat_kappa_(tau,u)(E)
 =[decoration(o)=tau]q_u(o)
  +[decoration(M_R o)=tau]q_u(M_R o).                 (476)
```

Thus (476) retains exactly which endpoint decoration supplied the old
unresolved difference.  At an H--V boundary only `tau=H` and the actual V
decorations can occur; from the viewpoint of either endpoint these are its
root-mate decoration tags from (372)--(373).

Let the refined boundary matrix have columns `(d,u,tau)` and entries

```text
widehat B_Z(E,(d,u,tau))
 :=widehat_kappa_(tau,u)(E).                          (477)
```

Since the decoration projections partition the dart space,

```text
sum_tau widehat B_Z(E,(d,u,tau))
 =delta_R q_u(E)=B_Z(E,(d,u)).                        (478)
```

Consequently `im B_Z` is contained in `im widehat B_Z`: the refinement
cannot lose an activation available to the old alphabet, but it can split a
privately cancelling old column into owner-distinguished pieces.  This is
the precise SRP counterpart of inserting an owner projection inside the
Baer commutator.

The mass of a refined column is also exact.  Define the decoration-resolved
root activation

```text
A_(tau,u)
 :=1_H^T(I+M_R)P_tau q_u
 =sum_(H--V boundaries E) widehat B_Z(E,(d,u,tau)).   (479)
```

The second equality holds because `(I+M_R)P_tau q_u` is constant on each
root pair and `1_H` selects exactly one dart of every H--V pair.  It is
important not to rename (479) as `D_(1_H,P_tau q_u)`: unlike `q_u`, the
projected vector `P_tau q_u` need not be constant on port pairs, so the
`M_P` term in `D` is not represented by (479).  Only after summing the decorations do
the port terms recombine, and (478) gives

```text
sum_tau A_(tau,u)=D_(1_H,q_u).                        (480)
```

Hence the refined quotient-span statement

```text
alpha_Z=widehat B_Z widehat_beta+partial_H gamma      (481)
```

would imply

```text
omega_M(Z)
 =sum_(d,u,tau) widehat_beta_(d,u,tau)
    A_(tau,u).                                        (482)
```

Odd grading would therefore force a nonzero **decoration-resolved**
secondary defect even when every unresolved `D_(1_H,q_u)` cancels.  This is
exactly the activation observable missing from case A0 in Section 149; it
does not yet couple that observable to the capacity pricing of Sections
136--148.

The remaining question is again a finite span test.  The refined alphabet
still fails precisely when some `lambda` satisfies

```text
partial_H^T lambda=0,
widehat B_Z^T lambda=0,
<lambda,alpha_Z>=1.                                   (483)
```

Because of (478), every refined obstruction is automatically an old
obstruction (474), while the converse can fail.  Thus (483) cleanly tests
whether the mate/owner projection already suffices; if it does not, the
required enlargement must retain still finer source-occurrence data such as
the full cross-tag `(ell,tau,u)` of (373).  No assertion that (481) always
holds is made here.

## 153. A two-projection operator realizes the full H--V cross-tag

Section 152 still puts every H-end contribution into the single `tau=H`
column.  The V decoration of its root mate supplies the missing source tag.
Let `P_ell` project onto V darts with resolved route decoration `ell`, and
retain `P_H` for H darts.  Define two root-pair-constant channels

```text
K_(ell,u;V):=(I+M_R)P_ell q_u,
K_(ell,u;H):=(I+M_R)P_ell M_R P_H q_u.                (484)
```

The order of the factors in the second operator is essential.  First
`P_H q_u` retains the H-end census, `M_R` transports it to its V mate,
`P_ell` tests the mate's actual route decoration, and `I+M_R` copies the
tagged value back across the root pair.  Thus, on an H--V boundary
`E={o_H,o_V}` whose V dart has decoration `ell(E)`,

```text
K_(ell,u;V)(E)=[ell(E)=ell] q_u(o_V),
K_(ell,u;H)(E)=[ell(E)=ell] q_u(o_H).                 (485)
```

The H channel is the literal `(ell,H,u)` cross-term of (373) on this root
pair.  The V channel retains the complementary same-end secondary value
with the same route tag.  Together they give the complete route-tagged
endpoint split of the old H--V difference, written as noncommuting
projection words; only the H channel was present in the strictly
cross-endpoint definition (373).

Let `bar B_Z` have the columns `(d,ell,u;s)` for `s in {H,V}` given by
(485).  Every H--V boundary has exactly one V route decoration, so

```text
sum_(ell,s in {H,V}) bar B_Z(E,(d,ell,u;s))
 =q_u(o_H)+q_u(o_V)
 =B_Z(E,(d,u)).                                       (486)
```

Moreover the `V` columns in (485) are exactly the `tau=ell` columns of
`widehat B_Z`, while

```text
sum_ell bar B_Z(-,(d,ell,u;H))
 =widehat B_Z(-,(d,u,H)).                             (487)
```

Therefore

```text
im B_Z subseteq im widehat B_Z subseteq im bar B_Z.  (488)
```

The second inclusion is the formal benefit of retaining the source route
on the H-side mate payment: two H contributions with different V owners can
no longer cancel inside one column.

Write `A_(ell,u;s)` for the mass of the corresponding `bar B_Z` column.
The fully cross-tagged activation target is

```text
alpha_Z=bar B_Z beta_bar+partial_H gamma.             (489)
```

If (489) holds, summing rows gives

```text
omega_M(Z)
 =sum_(d,ell,u,s) beta_bar_(d,ell,u;s) A_(ell,u;s).   (490)
```

Hence odd grading forces a nonzero source-route/mate-side-resolved atom.
The exact obstruction is

```text
partial_H^T lambda=0,
bar B_Z^T lambda=0,
<lambda,alpha_Z>=1.                                  (491)
```

By (488), any obstruction (491) survives every coarser alphabet already
tested.  Conversely, failure of an obstruction from (474) or (483) after
the two-projection split identifies cancellation between distinct V-owner
tags as the whole reason the coarser activation failed.  No claim that
(489) always holds is made; (484)--(491) identify the finest pair-local
route/side cross-tag available from the existing local atom `q_u` before
introducing new features.

## 154. The fully tagged dual is an odd-length selected-run census

The obstruction (491) has a direct combinatorial form.  Every H--V boundary
is an endpoint of a unique maximal H-run.  The equation
`partial_H^T lambda=0` therefore says that there is one bit `epsilon_A` for
each H-run `A` such that

```text
lambda(E)=epsilon_A for both endpoints E of A.         (492)
```

For a boundary `E={o_H,o_V}`, write

```text
q_u^H(E):=q_u(o_H),       q_u^V(E):=q_u(o_V),
ell(E):=the resolved route decoration of o_V.          (493)
```

Substituting (485) and (492), the equations
`bar B_Z^T lambda=0` become the completely separated census laws

```text
for every (d,ell,u,s), s in {H,V}:
sum_(H-run endpoints E with ell(E)=ell)
  epsilon_(A(E)) q_u^s(E)=0.                           (494)
```

Finally, `lambda` has the same value at the entry and exit of each run, so
the definition (464) gives

```text
<lambda,alpha_Z>
 =sum_(H-runs A) epsilon_A (ell(A) mod 2).             (495)
```

Consequently the fully tagged activation statement (489) is equivalent to
the following parity assertion:

```text
Every selection of H-runs whose total selected length is odd has, for
some route ell, secondary atom u, and side s, an odd number of selected
ell-boundary endpoints exposing q_u on side s.         (496)
```

Equivalently, a counterexample is exactly a selected family of H-runs of
odd total length for which **all** route/atom/side endpoint censuses are
even.  There is no remaining linear-algebra ambiguity in this formulation:
the run variables are `epsilon_A`, (494) is the full cross-tag parity
ledger, and (495) is the marked grading it must detect.

Statement (496) is not proved.  It is, however, strictly sharper than the
old scalar activation request: it identifies the only possible private
payment after both endpoint orientation and owner/mate cancellation have
been quotiented out.  A uniform proof must show that an odd-length selected
run family cannot close all the censuses (494); a finite falsifier need only
find such a family.

## 155. A minimal activation obstruction is an odd-graded run circuit

Package the two endpoint censuses of one H-run into a single feature
column.  Let

```text
s(E):=(q_u^H(E),q_u^V(E))_u,
g_A:=e_(ell(E_-)) tensor s(E_-)
    +e_(ell(E_+)) tensor s(E_+),                       (497)
```

where `E_-,E_+` are the two boundaries of `A`; the first tensor coordinate
places signatures with different route labels in disjoint blocks.  Then
(494)--(495) say that a dual obstruction is exactly a coefficient vector
`epsilon` satisfying

```text
sum_A epsilon_A g_A=0,
sum_A epsilon_A (ell(A) mod 2)=1.                     (498)
```

Choose an obstruction of inclusion-minimal run support.  No nonempty proper
subfamily of its selected columns can sum to zero.  Indeed, if such a
subfamily had odd total run length it would itself be a smaller obstruction;
if it had even total run length, deleting it would leave a smaller
obstruction.  Hence the selected `g_A` form a binary matroid circuit, and
the run-length grading of that circuit is odd.

There is one degenerate circuit case, now completely explicit.  A single
odd run `A` is an obstruction exactly when `g_A=0`.  From (497):

```text
if ell(E_-) != ell(E_+):
    s(E_-)=s(E_+)=0;
if ell(E_-)=ell(E_+):
    s(E_-)=s(E_+).                                    (499)
```

Thus the base case of (496) is not automatic.  It reduces to excluding an
odd H-run whose differently labeled ends are both secondary-silent, or
whose equally labeled ends have identical full side-resolved secondary
signatures.  Any proposed local activation proof must address precisely
these two patterns.

For a nondegenerate minimal obstruction, every feature coordinate appearing
in one selected run column appears in at least one other selected run
column; otherwise that coordinate would survive in the sum (498).  The
privacy and collision analysis of Sections 123--127 can therefore be aimed
directly at these circuit repetitions: private coordinates peel a run,
while every surviving repeated coordinate must be assigned to the bounded
labeled-collision sector.  This does not yet prove that the resulting
circuit has even run-length grading, but it removes arbitrary selected-run
families from consideration: only the zero-column patterns (499) and
support-minimal collision circuits can obstruct activation.

## 156. A singleton obstruction is internally connection-even

Suppose the degenerate circuit (499) occurs.  In either label case its two
endpoint signatures agree side by side:

```text
q_u(h_-)=q_u(h_+),       q_u(v_-)=q_u(v_+)            (500)
```

for every `u`.  When the route labels differ, (499) makes all four values
zero; when they agree, equality is exactly the two coordinates of
`s(E_-)=s(E_+)`.

The H-run telescoping identity (399) now gives

```text
sum_(internal H--H roots E in A) eta_u(E)=0           (501)
```

for every secondary atom `u`.  Equivalently, each `u` occurs in an even
number of the six contributing connection states (407) along the run.
Equation (397) also gives

```text
tau_u(A)=0                                            (502)
```

for every `u`, consistently with the zero run-signature column.

This reaches the capacity classification.  If a secondary label `u`
supports a saturated `(2,1)` cell inside a singleton obstruction, its total
number of contributing cells is even by (501).  Hence it is accompanied by
an odd number of unsaturated `(1,0)` or `(0,1)` cells with the same `u`.
The saturated cell is unique for that label by Section 136, so it cannot be
privately closed by another saturated payment.

Thus an odd singleton obstruction has only two possible internal profiles:

```text
no saturated cell at all; or
each saturated private unit launches an odd unsaturated same-u relay.    (503)
```

This does not exclude either profile.  It does show that the degenerate
activation failure is already coupled to the pricing ledger: the private
capacity unit cannot remain isolated, and the remaining no-saturation
branch consists entirely of the two directed singleton-transfer profiles.

## 157. Capacity constraints alone cannot exclude the silent odd run

There is a formal zero model of every connection and capacity statement in
Sections 132--138.  Take one abstract H-run of arbitrary odd length and set

```text
q_u(v_-)=q_u(h_-)=q_u(h_+)=q_u(v_+)=0,
eta_u(E)=0 for every internal cell E,
tau_u(A)=0                                               (504)
```

for every `u`.  Then the transport identities (397)--(403) hold, the list
of nonzero profiles (407) is empty, the saturated privacy statement is
vacuous, and all fiber bounds are satisfied.  If the two endpoint route
labels differ, (504) is exactly the first singleton obstruction in (499);
if they agree, it is a special case of the second.

This is an abstract ledger model, not a claim that an SRP incidence graph
realizes it.  Its consequence is nevertheless rigorous: no argument using
only the displayed transport equalities, the six-state profile list, and
the capacity/privacy bounds can prove (496), because those constraints
admit (504).  Excluding the silent odd run requires one additional geometric
input that forces some endpoint or internal secondary incidence from the
primary odd grading.

Thus capacity pricing can finish the branch after activation, and (501)--
(503) constrain how a saturated unit relays, but capacity cannot create the
first nonzero atom.  The missing statement is now irreducibly an incidence
realizability lemma for (362): an odd H-run cannot have the zero/matched
endpoint signatures (499) while all of its internal secondary connections
close evenly.  This identifies the exact place where the original marked
run geometry, rather than the abstract connection ledger, must re-enter.

## 158. A silent endpoint wedge has only four active connector states

Let `o` be any incidence dart with occurrence wedge

```text
W(o)={x,x',z},                                       (505)
```

where `x,x'` are the two roots of its port and `z` is the port.  Let
`U_1={u:t_u=1}` be the target-active secondary labels.  By (366), the full
secondary signature at `o` vanishes exactly when no `u in U_1` meets
`W(o)` in an odd number of vertices.  Three incidences would be odd, so

```text
q_u(o)=0 for every u
iff every u in U_1 meets W(o) in zero or two vertices. (506)
```

C4-freeness makes the two-incidence part rigid.  The root pair `{x,x'}`
already has the common neighbor `z`, so no secondary label can meet both
roots.  For either root--port pair there is at most one `u` adjacent to
both: two such labels would be two common neighbors of that pair.  Hence
the target-active incidence pattern of a silent wedge is specified by a
subset of the two pair types

```text
{x,z}, {x',z},                                       (507)
```

with at most one connector label on each selected pair.  There are only
`2^2=4` underlying connector states (before recording the labels).

For a V occurrence with actual route label `y`, the routed triangle already
puts `y` on one root--port pair, say `{x,z}`.  If `t_y=1`, then `y` is
exactly the unique active connector of that pair in (507); if `t_y=0`, it
is invisible to the active connector state.  Thus even the on-occurrence
route, which vanished from `q_y` in (361), re-enters the realizability audit
through whether its target parity is active.

This classification does not exclude a silent endpoint.  It replaces the
formal all-zero assignment (504) by four locally admissible templates (not
an assertion that every template extends to a global graph).
To eliminate the differently labeled singleton pattern in (499), it now
suffices to show that the two silent boundary wedges of an odd H-run cannot
choose compatible templates (507) while the internal four-incidence cells
close as in (501).  That is a finite connector-propagation problem rather
than an unrestricted secondary-census problem.

## 159. Every silent routed endpoint is active or spends a second target port

Let the V dart at a boundary have actual route label `ell=(d,y)` and port
`z in V_j`.  The `d--e` fiber of `y` has order two and already contains
`z`.  Therefore

```text
t_y=1 iff the other e-neighbor of y lies outside V_j,
t_y=0 iff both e-neighbors of y lie in V_j.            (508)
```

In the first case Section 158 shows that `y` is the unique active connector
on its routed root--port pair.  In the second case the route label is absent
from the active signature, but it spends its entire two-port fiber inside
the target component.

Now suppose the two ends of one H-run have the same actual route label `y`.
They are distinct route occurrences and use distinct ports: the partial-
matching property of `F_(d,y)` forbids reuse of a port, and Section 120 also
forbids `y` from routing both darts of one port.  Both ports lie in `V_j`,
so they exhaust the `e`-fiber of `y`.  Hence

```text
ell(E_-)=ell(E_+)=y  implies  t_y=0,                  (509)
```

and those are the only two target ports of `y`.

Thus the two singleton patterns in (499) have a sharper route-level form:

```text
equal endpoint labels: the common actual label is a saturated target-even
                       two-port owner;
different labels:     each endpoint label either appears as its unique
                       active routed connector or commits a second target
                       port elsewhere in V_j.         (510)
```

This is an exact activation-or-capacity dichotomy for the **actual** route
labels, independent of the off-route atoms `u`.  It does not yet contradict
the matched/zero secondary signatures.  It does ensure that a silent
endpoint cannot make its routed owner disappear for free: it is visible in
the active connector template or consumes the full two-port target fiber.

## 160. Silence on an H dart means complete active-fiber avoidance

The four templates of Section 158 simplify further on the H side of a run
boundary.  If an intermediate `u` is adjacent to a root and the shared port
of an incidence dart, it resolves a rooted triangle through that dart.  The
dart is then V-decorated by the port bijection of Section 99.  The same
argument for the other root is the V decoration of the port mate.  Hence an
H-decorated port admits neither root--port connector in (507).  The
root--root connector was already excluded by C4.

Thus every secondary label meets the wedge of an H dart in at most one
vertex, and (366) sharpens to

```text
q_u(h)=1 iff t_u=1 and u meets the H wedge once;
q_u(h)=0 for every u iff no target-active u meets the H wedge. (511)
```

In particular, the differently labeled singleton obstruction of (499)
forces complete target-active avoidance at both H boundary darts, not just
an even connector pattern.  Its V boundary darts may still use the four
templates (507), including the actual active route connector from (508).

For an internal H--H root pair, both incident ports are H-decorated.  The
same exclusion forbids an opposite root from sharing its own port exposure:

```text
R_cd(x_i,u) R_ed(z_i,u)=0 for i in {1,2}.             (512)
```

In particular, the saturated `(2,1)` profile would contain such an aligned
root--port pair on whichever side exposes the port, so it is impossible.
The contributing internal states (407) reduce to the two unsaturated
profiles

```text
(a_u(E),p_u(E)) in {(1,0),(0,1)}.                     (513)
```

So the saturated `(2,1)` alternative in (503) cannot occur inside a genuine
H-run at all; it belonged to the raw four-incidence classification before
the H decoration was reapplied.  A singleton obstruction is therefore a
pure chain of root-only and port-only singleton transfers, with complete
active-fiber avoidance at a silent H endpoint.  This is a substantial
reduction, but it does not yet exclude such a chain.

## 161. Each secondary label decomposes canonically into run intervals

Order the H port pairs of a run `A` from its entry to its exit and, for a
fixed `u`, let `b_i` be the common value of `q_u` on the two darts of the
`i`-th port pair.  Port constancy is (381).  Between consecutive H ports,
the intervening H--H root pair has connection atom

```text
eta_u(E_i)=b_i+b_(i+1).                               (514)
```

This is the local form of the telescoping identity (399): a contributing
cell is exactly a flip of the binary word `b_1,...,b_m`.

For a singleton obstruction, (500) says the endpoint values agree.  Adjoin
a formal no-flip edge between the two ends and view the word cyclically.
Its `1`-support is then a disjoint union of cyclic intervals.  Every proper
interval has exactly two boundary flips, paired canonically by their order
along the run; if the word is identically one, it is one boundary-spanning
channel with no internal flips.  In the different-route-label singleton
case the H endpoint signatures vanish, so no interval crosses the formal
edge.

By (513), every actual flip is one of the two unsaturated profiles

```text
(1,0): root-only endpoint,
(0,1): port-only endpoint.                            (515)
```

Thus the internal connection ledger of a singleton obstruction is already
a family of two-ended `u`-labeled relay intervals, plus possible constant
channels.  There is no pairing gauge on a linear run: consecutive flips of
the same `u` determine the intervals uniquely.  This is the SRP analogue of
the two-ended chain decomposition in the Baer cut branch.

The interval decomposition does not determine the marked run-length parity.
The remaining task is to price the four possible endpoint-type pairs
`RR,RP,PR,PP` in (515), together with the constant channel, against the
actual-owner expenditure (510).  Any successful price must be invariant
under inserting or deleting a length-two subinterval, so only an odd
run-length holonomy can survive.

## 162. Saturation survives only as a V-port-mate route at a boundary

Section 160 eliminates `(2,1)` cells internal to an H-run, but the boundary
theory of Sections 137--144 has one nonvacuous saturated channel.  Let an
H--V root pair at center root `x` have H port `z_H`, V port `z_V`, and
opposite roots `x_H,x_V`.  A saturated cell for `u` has

```text
u adjacent to x_H and x_V, and to exactly one of z_H,z_V. (516)
```

It cannot expose `z_H`: then `u` would meet the aligned H dart
`(x_H,z_H)` in both its root and port, contradicting Section 160.  Therefore
the exposed port is `z_V`.  Since `u` is also adjacent to `x_V`, the port-
mate dart `(x_V,z_V)` is a rooted V triangle whose unique intermediate is
`u`.  In the complete decoration alphabet,

```text
(2,1) at an H--V boundary
implies the V port mate is decorated V_u.             (517)
```

Conversely, if the V port mate is `V_u`, `t_u=1`, and `u` is adjacent to
the H-side opposite root `x_H`, then `u` is adjacent to both opposite roots
and to `z_V`; these exhaust its two `c`-neighbors and its unique target
port, so the cell is saturated.  Thus, with those explicit incidence and
activity conditions, (517) is an equivalence.

The V dart at the boundary itself has some actual label `ell`.  Necessarily
`ell != u`: equality would make `u` adjacent to both roots `x,x_V` of
`z_V`, while those roots already have common neighbor `z_V`, violating C4.
Hence every surviving saturated boundary is the resolved color-turn port
pair

```text
(V_ell,V_u),  ell != u,                              (518)
```

seen from an adjacent H--V root transition, together with the extra crossed
incidence `u--x_H`.

This sharply scopes the private-curvature theory of Sections 143--144.  Its
saturated source is not a generic `(2,1)` connection state: it is exactly a
V-port-mate owner occurrence of the form (518).  All internal run relays are
unsaturated by Section 160, while every saturated boundary unit already
carries the actual secondary route label needed for owner-sensitive
pricing.

## 163. Port-only interval endpoints are pinned to one H port

Fix a target-active secondary label `u`.  Since its `d--e` fiber has order
two and `t_u=1`, it has a unique neighbor

```text
r_u in V_j.                                           (519)
```

Every port of the lifted dart cycle lies in `V_j`.  Therefore an internal
`(0,1)` connection cell for `u` must expose `r_u`; no other H port can be a
port-only endpoint of a `u`-interval.

The H--H port pair at `r_u` has two root endpoints.  Along the alternating
dart cycle, the only internal root transitions whose four-incidence cells
contain `r_u` are the transitions at those two roots.  Consequently

```text
number of P-type flips for u along one H-run <= 2,     (520)
```

and when both occur they flank the single port-pair state `b(r_u)` in the
ordered word of Section 161.  If `r_u` is an endpoint port of the maximal
run, only the internal flank is present.

This makes the local endpoint geometry almost rigid.  When both P flips are
present and `b(r_u)=1`, they delimit the one-port interval supported at
`r_u`.  When `b(r_u)=0`, they delimit the one-port zero gap and their outer
sides continue into the remaining interval decomposition.  With one P flip,
it pairs with an R flip; with no P flips, all proper intervals are R--R.
There cannot be two disjoint P--P relay intervals for the same `u`.

Root-only flips are likewise supported on the two `c`-neighbors of `u`, but
a root can occur in more than one adjacent four-incidence cell, so no
analogous count of two R flips is asserted.  The rigorous reduction is only
the unique-port localization (519)--(520): the `RR/RP/PR/PP` table from
Section 161 has at most two P-bearing interval endpoints per secondary
label, and at most one P--P interval.

## 164. Each secondary label has at most three proper run intervals

The root-only endpoints also have a uniform bound.  A `(1,0)` flip for `u`
selects exactly one opposite root `b` adjacent to `u` and one H port `z`
incident to `b`; the internal root cell is the unique transition at the
other root of `z` containing that dart.  The `d--c` fiber of `u` has two
roots, and each such root has two `e`-neighbors.  Therefore there are at
most four possible `(b,z)` incidences and

```text
number of R-type flips for u along one H-run <= 4.     (521)
```

There is no double counting issue for a contributing `(1,0)` cell: its
unique exposed opposite root determines `(b,z)`, and one incidence dart
belongs to one root transition on the auxiliary cycle.

Combining (520)--(521), the closed binary word for `u` has at most six
flips.  Its flip count is even, so it belongs to

```text
{0,2,4,6}.                                            (522)
```

Consequently its `1`-support has at most three proper relay intervals,
apart from the zero-flip constant channel.  This bound is independent of
the length of the H-run.

The singleton transfer problem is therefore finite at each secondary
label: at most four root endpoints, at most two endpoints pinned to one
target port, and at most three canonically paired intervals.  What remains
unbounded is only the number of different labels `u` appearing along a
long run, not the state complexity of any one label.  A global price may
sum the per-`u` interval contributions; it need not solve an unbounded
pairing problem within a fiber.

## 165. The interval endpoint ledger has only eight count sectors

For a fixed active `u`, let `n_R(u)` and `n_P(u)` be the numbers of
root-only and port-only flips along the run.  Closure of the binary word
means their sum is even.  Hence

```text
n_R(u)=n_P(u) mod 2.                                  (523)
```

Together with (520)--(521), the complete count list is

```text
(n_R,n_P) in {
  (0,0),(2,0),(4,0),
  (1,1),(3,1),
  (0,2),(2,2),(4,2)
}.                                                    (524)
```

The zero-flip all-zero word and the zero-flip constant-one channel are two
geometrically different realizations of the same count sector `(0,0)`;
the latter must be retained as an extra state.

Equation (523) is the elementary capacity transfer carried by the interval
decomposition.  A single occurrence of the unique target port `r_u`
forces an odd number (one or three) of root-only endpoints on the two
`c`-neighbors of `u`.  Zero or two port occurrences force an even root
census.  Thus a one-ended target-port payment cannot remain private: it
launches an odd root-side relay demand for the same secondary label.

This is exactly the finite endpoint table needed before assigning prices.
Ordering data still distinguishes interval types inside one sector, but no
new endpoint counts occur.  Any proposed invariant may therefore be checked
on the eight sectors (524), the constant channel, and the bounded orderings
of at most six flips; no `q`-dependent family of count cases remains.

## 166. Endpoint prices split into a potential or a four-relay holonomy

Forget interval orientation for the moment and assign binary prices

```text
w_RR, w_RP=w_PR, w_PP                              (525)
```

to the three endpoint-type pairs.  The only nontrivial reassociation of two
R and two P endpoints replaces one `RR` and one `PP` interval by two `RP`
intervals.  The price change is

```text
h_4:=w_RR+w_PP,                                      (526)
```

because the two `w_RP` terms cancel over `F_2`.

Thus there are exactly two branches.  If `h_4=1`, the four endpoints carry
a localized four-relay holonomy: the two pairings have opposite price.  If
`h_4=0`, then `w_RR=w_PP`, and the price has the additive normal form

```text
w_XY=p_X+p_Y+c,
c=w_RR,
p_R=0,
p_P=w_RP+w_RR.                                      (527)
```

Conversely (527) makes every four-endpoint switch price-neutral.  Hence
(526) is the complete pairing-gauge obstruction for the R/P endpoint
alphabet, exactly parallel to the quadrilateral identity in the Baer relay
stars.

On a single H-run the interval pairing is canonical, so no choice is needed.
The dichotomy becomes relevant when gluing interval chains across owner
occurrences or comparing collision-circuit decompositions.  A nonzero
`h_4` is already a bounded four-relay object to price directly; in the
zero-holonomy branch every glued-chain price reduces to endpoint potentials
plus `c` times the number of intervals.  The remaining marked information
can therefore enter only through exposed boundary potentials, interval-
count parity, or the constant-one channel—not through an unbounded pairing
gauge.

## 167. Gauge-independent interval prices depend on only two bits

In the zero-holonomy branch of Section 166, define

```text
pi_u:=n_P(u) mod 2,
nu_u:=(n_R(u)+n_P(u))/2 mod 2.                        (528)
```

The division by two is an integer operation: the numerator is even by
(523).  The bit `nu_u` records whether the total flip count is `2 mod 4`,
equivalently the parity of the number of proper intervals.

Summing the additive price (527) over all intervals gives

```text
Price_u
 =p_R n_R+p_P n_P+c (number of intervals)
 =(w_RP+w_RR) pi_u+w_RR nu_u.                        (529)
```

Here `p_R=0`, `p_P=w_RP+w_RR`, and `c=w_RR`; only the endpoint-count
parities enter.  Thus all eight sectors (524) collapse to the two-bit table

```text
(n_R,n_P): (0,0) (2,0) (4,0) (1,1)
(pi,nu):    (0,0) (0,1) (0,0) (1,1)

(n_R,n_P): (3,1) (0,2) (2,2) (4,2)
(pi,nu):    (1,0) (0,1) (0,0) (0,1).                (530)
```

The zero-flip constant-one channel is not counted by (528): it has no
proper interval endpoints but can carry a separate bit `zeta_u`.  Therefore
the full gauge-independent per-label state is exactly

```text
(pi_u,nu_u,zeta_u) in F_2^3.                          (531)
```

No endpoint price can see more than these three bits once four-relay
holonomy is absent.  The final singleton calculation may consequently be
organized as an eight-state table per active label, rather than the raw
ordered word.  A terminal must either price the explicit `h_4=1` holonomy
or express the marked run grading through the aggregate of the states
(531) and the actual-owner capacity data (510).

## 168. The port-parity bit is a local defect around one forced `1`

Suppose the unique target port `r_u` from (519) is an H port of the run.
Then `u` meets its H wedge at the port.  By Section 160 it meets no other
vertex of that wedge, so the corresponding word state is forced:

```text
b(r_u)=1.                                             (532)
```

Thus the `b(r_u)=0` zero-gap alternative mentioned in Section 163 is not
realizable for an active `u`; when both P flips occur, they delimit the
one-port `1` interval at `r_u`.

If `r_u` is internal to the run, let `b_L,b_R` be the neighboring H-port
states on its two flanks.  The transition on a flank is port-only exactly
when that neighboring state is zero: the `r_u` side contributes the unique
port incidence, while a neighboring value one supplies a second incidence
and makes the connection parity even.  Therefore

```text
n_P(u)=[b_L=0]+[b_R=0],
pi_u=b_L+b_R.                                         (533)
```

If `r_u` is an endpoint H port, the same statement holds for its one
internal flank; if `r_u` is not an H port of `A`, then `n_P(u)=pi_u=0`.

Consequently `pi_u=1` is not an abstract endpoint-count bit.  It says that
the forced `1` at the unique target port has unequal continuation on its
two sides (or terminates against a zero internal neighbor at a run end).
By (523), this local one-sided port defect launches an odd root-side demand.
The remaining bits `nu_u,zeta_u` record global interval parity and the
constant channel; only they remain invisible to this local target-port
test.

## 169. A constant-one channel has run length at most five

Suppose `zeta_u=1`, so the word of Section 161 satisfies `b_i=1` at every
H port of the run.  By Section 160, each H wedge then contains exactly one
vertex adjacent to the active label `u`.

There are only five possible H-port witnesses.  The label `u` has two
`c`-neighbors, and each such root is incident to two `e` ports, so root
incidences can witness at most four H port pairs.  Its unique target port
`r_u` can witness at most one further H port pair.  Every `b_i=1` state must
be witnessed by one of these incidences.  Therefore

```text
zeta_u=1 implies ell(A)<=5.                            (534)
```

This is an injection bound, not just a parity count: an H port pair is
identified by its port, a root witness can occur only on one of that root's
two incident ports, and the port witness is the single `r_u`.

Consequently no H-run of length at least six supports a constant-one
secondary channel.  On an odd singleton obstruction the `zeta` branch is
confined to run lengths `1,3,5`; all longer odd runs are controlled entirely
by the `(pi_u,nu_u)` interval states and the four-relay holonomy branch.

This reproduces, at the run level, the order-five cutoff found for flat
singleton columns in Section 141, but it uses only the direct two-by-two
fiber geometry and H-decoration exclusivity.  It leaves the three short
odd lengths for a finite local check rather than treating `zeta_u` as an
unbounded global state.

## 170. Every secondary word has support at most five

The witness count in Section 169 does not require the word to be constant.
Whenever `b_i=1`, the H wedge at the `i`-th port contains exactly one
incidence of `u`, and that incidence is one of the same four root-port
positions or the unique target port.  Hence for every active label

```text
|{i:b_i=1}|<=5.                                       (535)
```

Thus all proper `u`-intervals together occupy at most five H port pairs,
even on an arbitrarily long run.  Long zero gaps carry no secondary state.

The half-flip bit `nu_u` also has a local formula.  Close the word with the
formal endpoint edge from Section 161 and let

```text
S_u:=sum_i b_i,
J_u:=sum_i b_i b_(i+1),                               (536)
```

where the second sum includes that formal edge.  The occupied subgraph is
a disjoint union of paths unless it is the constant-one cycle.  Its number
of proper components has parity `vertices+edges`, so in every case
(including the empty and constant words, where both sides are zero)

```text
nu_u=S_u+J_u mod 2.                                   (537)
```

For a nonconstant word this is the parity of its proper intervals; for the
constant-one word `S_u=J_u=ell(A) mod 2`, so the two terms cancel and
`nu_u=0`, leaving `zeta_u` to distinguish that channel as intended.

Therefore the remaining additive state is supported on at most five
positions and `nu_u` is its mod-two Euler characteristic, not an unbounded
word invariant.  Together with (533), both `pi_u` and `nu_u` are now
explicit local functions of a five-position incidence pattern; only the
actual-owner coupling to the marked run length remains to be supplied.

## 171. A length-five constant channel exhausts a rigid port footprint

Let the two `c`-neighbors of an active label `u` be `b_1,b_2`, and retain
its unique target port `r_u`.  The five potential witnesses from Section
170 are in fact five distinct ports when they are H-decorated.

First, the two `e`-fibers `N_e(b_1)` and `N_e(b_2)` are disjoint: a common
port together with their common neighbor `u` would form a C4.  Second,
`r_u` cannot be incident to either `b_i` when it is an H port, since then
`u` would meet both the root and port of an H dart, contradicting Section
160.  Hence

```text
N_e(b_1), N_e(b_2), {r_u}
are disjoint and have total size five.                (538)
```

If `zeta_u=1` on a run of length five, the injection behind (535) is an
equality.  Therefore its H port set is exactly

```text
Ports(A)=N_e(b_1) union N_e(b_2) union {r_u}.         (539)
```

Moreover, the two ports in each `N_e(b_i)` are consecutive in the H-run:
their darts at `b_i` form an H--H root pair, so the auxiliary cycle passes
directly from one port pair to the other without leaving the maximal run.

Thus a length-five constant channel is not an arbitrary five-letter word.
It consists of two forced adjacent root-witness pairs and one distinguished
target-port state, in some order compatible with the run endpoints.  The
short constant cases of lengths one and three choose proper subsets of the
same five-slot footprint; only the extremal case exhausts it.

This supplies a finite owner-sensitive template for the last `zeta` state.
Any collision with another label must reuse one of the five explicit ports
or roots in (539), where C4 and the two-fiber capacities apply directly.
No contradiction is asserted yet.

## 172. The constant-channel branch has eight short witness templates

Encode the target-port witness `r_u` by `P`.  Encode a port witnessed by the
root `b_i` by `B_i`; each symbol `B_i` has capacity two, and using both
copies forces the adjacent block `B_i B_i` by Section 171.  Symbols cannot
otherwise repeat.

Up to reversal of the H-run and exchange of `b_1,b_2`, the constant-one
templates of odd length are exactly

```text
length 1:
  P,                     B_1;

length 3:
  P B_1 B_2,             B_1 P B_2,
  P B_1 B_1,             B_1 B_1 B_2;

length 5:
  P | B_1 B_1 | B_2 B_2,
  B_1 B_1 | P | B_2 B_2.                             (540)
```

For length three, if `P` and one port from each root are used, `P` is either
at an end or in the middle, giving the first two templates.  If one root
contributes both ports, its block must be adjacent; the third witness is
either `P` or one port of the other root, giving the last two.  For length
five all capacities are exhausted, and the singleton block `P` lies either
at an end or between the two forced root blocks.

This is a list of necessary incidence-order templates, not a claim that
every row is globally realizable.  Actual root identities, the two V
boundary decorations, and collisions with other labels refine the rows.
But there is no remaining unenumerated `zeta` word: the entire constant
branch consists of the eight rows (540).

The finite terminal can now attach owner data to these rows directly.  In
particular, the equal-boundary-label singleton from (509) brings one
saturated two-port actual owner, while (540) records whether the secondary
constant channel uses its target port, a full root block, or both.  Any
capacity collision is visible in this joint row rather than hidden in an
arbitrary run word.

## 173. Only the parity of positive silent gaps remains invisible

Fix a nonempty `u`-word and list its occupied H ports cyclically after the
formal endpoint closure.  Let `g_1,...,g_s` be the numbers of zero states
strictly between consecutive occupied positions, where

```text
s=S_u<=5,
ell(A)=S_u+sum_(a=1)^s g_a.                           (541)
```

A gap has `g_a=0` exactly when its two occupied endpoints contribute one
term to `J_u`.  Hence (537) records

```text
nu_u=S_u+#{a:g_a=0} mod 2.                            (542)
```

But the marked run grading is

```text
ell(A) mod 2
 =S_u+sum_a (g_a mod 2).                              (543)
```

Thus the local state `(pi_u,nu_u,zeta_u)` and every additive endpoint price
see which gaps vanish, but not the parity of the **positive** gaps.  There
are at most five such gaps for each `u`, yet their lengths can be arbitrary.

Every port in a positive `u`-gap has `b_i=0`; by Section 160 its H wedge
contains no target-active incidence of `u`.  Therefore the discrepancy
between (542) and (543) is exactly a silent-transport parity, not another
connection or pairing gauge.

This identifies the last required owner coupling precisely.  A terminal
must show that, after summing the active labels and the actual-owner rows
(540)/(510), the positive silent-gap parities cancel or are detected by a
boundary owner occurrence.  Without such a statement, an odd amount of H
length can remain hidden inside zero gaps while every three-bit secondary
state is unchanged.  The interval and constant-channel enumerations have
exhausted all other degrees of freedom.

## 174. Silent transport has at most three gap-parity bits per label

The support positions of one active `u` are not five unrelated points.
Those witnessed by a fixed `c`-neighbor `b_i` are a subset of its two
incident ports; if both occur, they are consecutive in the H-run and form
the zero-gap block `B_i B_i`.  The target-port witness is the singleton
block `P`.  Hence, after contracting these forced zero gaps, the occupied
word has at most the three blocks

```text
B_1, B_2, P,                                          (544)
```

where each `B_i` has size one or two and any block may be absent.

Consequently there are at most three positive silent gaps in the cyclically
closed word: one when a single block is present, two between two blocks,
and three between three blocks.  Write their length parities as

```text
rho_u=(rho_1,rho_2,rho_3) in F_2^3,                  (545)
```

omitting unused coordinates.  Equation (543) becomes

```text
ell(A) mod 2
 =S_u+sum rho_a                                       (546)
```

for any nonempty word, since the contracted within-block gaps have length
zero.  Thus unbounded gap lengths reduce to at most three binary variables
per label.

Together with the block presence, the two `B_i` sizes, and the cyclic block
order (at most six raw orders, further reduced by reversal and exchange;
the gap crossing the formal endpoint edge may remain distinguished), (545)
is a finite state table independent of `q` and of the run length.  The
constant templates (540) are exactly the rows with no positive gaps.  The
nonconstant rows insert one to three positive gaps and remember only their
parities.

This is the complete per-label enumeration promised after Section 170.
The remaining difficulty is no longer enumeration: it is a cross-label
identity showing that the sums of the `rho` bits are paid by the actual V
owner decorations at the run boundaries.  Without that identity the gap
bits are honest residual degrees of freedom; with it, the singleton
activation obstruction is eliminated.

## 175. A totally silent H port forces two companion target ports

Let an H port `z in V_j` have roots `x,x'`.  For the fixed secondary color
`d`, the three two-element neighbor sets

```text
N_d(x), N_d(x'), N_d(z)                               (547)
```

are pairwise disjoint.  A common label between the two root sets is
forbidden because `z` is already a common neighbor of `x,x'`; a common
label between a root and the port would form a rooted V triangle through
an H dart, forbidden by Section 160.  Thus the H wedge has exactly six
distinct secondary incidences.

Suppose the port state is silent for **every** target-active label:

```text
q_u(h)=0 for all u with t_u=1.                         (548)
```

By (511), none of the six labels in (547) can be active.  In particular,
let `y_1,y_2` be the two `d`-neighbors of the port `z`.  Then `t_(y_k)=0`.
Each `y_k` has exactly two `e`-neighbors and one is `z in V_j`; target
evenness therefore forces its other neighbor `r_k` to lie in `V_j` too.

The two companion ports are distinct.  If `r_1=r_2`, the pair `z,r_1`
would have the two common neighbors `y_1,y_2`, a C4.  Hence

```text
z silent for all active u
implies distinct r_1,r_2 in V_j with
N_e(y_k)={z,r_k}.                                     (549)
```

So a totally silent H port cannot hide without spending capacity: it owns
a canonical three-port target footprint `{z,r_1,r_2}`, with two distinct
secondary labels joining the center port to its companions.  Footprints of
different silent ports may overlap, so no global packing bound is claimed
yet.  Their overlap graph is now the exact object whose parity must pay the
positive silent-gap bits of Section 174.

## 176. Silent footprints have an exact two-regular shadow boundary

Let `G_d^e` be the shore projection on the `e` ports of the bipartite
two-factor `R_de`: a label `y in d` with

```text
N_e(y)={z,r}
```

gives the edge `z--r`, carrying label `y`.  Every `e` port has two
`d`-neighbors, and C4 makes their other endpoints distinct, so `G_d^e` is a
simple two-regular graph, hence a disjoint union of cycles.

The two companions in (549) are exactly the two `G_d^e`-neighbors of the
silent center `z`.  If `s` is the indicator of any family of totally silent
H ports in `V_j`, its summed three-port footprint is

```text
p_s:=(I+A_(G_d^e))s.                                  (550)
```

Every window used in (550) lies in `V_j`, by (549).  Since `G_d^e` has
degree two,

```text
1^T p_s
 =1^T s+1^T A_(G_d^e)s
 =|s|+2|s|
 =|s| mod 2.                                         (551)
```

Therefore an odd family of totally silent H ports has a nonzero, indeed
odd-mass, companion-port footprint ledger.  Its private q-signatures may
all vanish, but its inactive two-port owner labels cannot cancel the three-
port windows completely.

This is the first direct payment of silent-length parity.  The overlap
graph is no longer open-ended: it is the cycle graph `G_d^e`, and adjacent
silent centers combine by the linear operator `I+A_(G_d^e)`.  What remains
is to attach the odd footprint `p_s` to the existing route/owner capacity
ledger without contracting away its edge labels.  At the unlabeled port
level, odd silent parity is already activated exactly by (551).

## 177. The companion ledger is a uniquely labeled shadow-cut boundary

Let `partial_G` be the vertex-edge incidence matrix of `G=G_d^e`, and let
`delta_G s` be the edge cut whose value on `zr` is `s(z)+s(r)`.  Because
every vertex of `G` has degree two, over `F_2`

```text
partial_G(delta_G s)=A_G s.                           (552)
```

Indeed, at a vertex `z` the left side is the sum over its two neighbors
`r` of `s(z)+s(r)`; the two copies of `s(z)` cancel and the remaining sum is
`(A_Gs)(z)`.

Combining (550) and (552) gives the exact cut normal form

```text
p_s=s+partial_G(delta_G s).                           (553)
```

Every edge of `G` carries its unique intermediate label `y in d`, inherited
from the two-factor `R_de`.  Thus the boundary term in (553) is already a
label-preserving chain: only shadow edges crossing between silent and
nonsilent centers survive, and each comes with its actual inactive owner
label.  Edges between two silent centers occur twice and cancel with their
labels intact.

On each shadow-cycle component, the cut has even order; its crossing edges
come in cyclic order and each retains its unique label.  If `s` contains a
whole shadow cycle, its cut vanishes and (553) reduces to `p_s=s` on that
component; otherwise every companion payment is transported to the
boundary of the silent region by actual `y`-labeled crossing edges.

Therefore label aggregation is no longer an obstruction for the companion
part.  The only non-boundary term is the original silent-center indicator
`s`, whose mass is the marked silent parity.  A final owner identity must
attach those H centers to the V boundary decorations of their silent gaps;
all intervening companion transport is now an explicit labeled cut chain.

## 178. Run-path transport sends silent parity to the marked exit

Orient one maximal H-run `A` toward its exit boundary `E_+`.  Augment the
linear graph of its H port pairs by the last H--V transition to `E_+`.  For
each totally silent H port `z`, let `P(z,E_+)` be the unique forward path in
this augmented run graph.  Define the run chain

```text
c_s:=sum_(z:s(z)=1) P(z,E_+).                         (554)
```

Every internal path vertex occurs twice in its own path boundary, so
linearity gives the exact endpoint formula

```text
partial_Hrun c_s=s+(|s| mod 2)e_(E_+).               (555)
```

There is no path-pairing gauge: the oriented H-run supplies the unique path
from every center to the chosen exit.  Reversing the orientation changes
the exit term by the full run-endpoint boundary, exactly the quotient
ambiguity already absorbed in Section 151.

Substitute (555) into the shadow normal form (553).  In the combined chain
space of the run and the port shadow,

```text
p_s
 =partial_G(delta_G s)+partial_Hrun c_s
  +(|s| mod 2)e_(E_+).                                (556)
```

Every edge in the first boundary carries its unique inactive intermediate
label `y`; every edge in the second is an actual H-run transition with its
owner/port data.  Thus (556) is label-preserving on both parts.  Modulo
these two explicit boundary families, the entire silent footprint ledger is
exactly the exit atom with coefficient `|s| mod 2`.

This closes the transport half of silent activation.  An odd number of
totally silent H ports cannot remain in the interior: it reaches the same V
boundary at which the oriented phase vector `alpha_Z` records the run
length.  To finish the singleton identity one must add the complementary
nonsilent H ports—already covered by the active-label states of Sections
161--174—and verify that their exit coefficients sum with `|s|` to
`ell(A) mod 2` without losing the owner tags.

## 179. Nonsilent ports have a canonical degree-six cross-label expansion

For an H port `z`, let `Y(z)` be the six distinct secondary labels in its
wedge from (547).  Section 160 gives, for `y in Y(z)`,

```text
q_y(h_z)=t_y,                                         (557)
```

because `y` meets the H wedge exactly once; every other label has value
zero there.  Let `n(z)` be the indicator that the port is not totally
silent.  The choice-free Boolean identity over `F_2` is

```text
n(z)
 =1+product_(y in Y(z))(1+q_y(h_z))
 =sum_(empty != S subseteq Y(z)) product_(y in S)q_y(h_z). (558)
```

Thus nonsilence is not represented by choosing one active witness.  It has
a canonical expansion into at most `2^6-1=63` cross-label atoms, each tagged
by the actual subset of active wedge incidences.  The degree bound is
uniform in `q` and in the run length.

Let `n` be the indicator of the nonsilent H ports of a run and define, as in
(554), the forward-path chain

```text
c_n:=sum_(z:n(z)=1) P(z,E_+).
```

Then

```text
partial_Hrun c_n=n+(|n| mod 2)e_(E_+).                (559)
```

The silent and nonsilent indicators partition the H ports, so
`|s|+|n|=ell(A) mod 2`.  Adding (556) and (559) yields the exact exit-phase
decomposition

```text
(ell(A) mod 2)e_(E_+)
 =p_s+n+partial_G(delta_G s)
   +partial_Hrun(c_s+c_n).                            (560)
```

Here `p_s` is the odd-footprint activation of the silent sector, while `n`
has the bounded cross-label expansion (558).  All other terms are explicit
labeled boundaries.  Equation (560) is therefore the sought singleton
activation identity in an enlarged, nonlinear but uniformly finite
alphabet: the marked exit phase is generated by silent footprints and
degree-at-most-six active-wedge atoms modulo canonical run/shadow payments.

This does not yet prove the final capacity inequality.  It does close the
linear-span failure diagnosed in Sections 149--157: the missing columns are
now identified exactly as the silent footprint atoms and the nonempty
cross-label monomials (558), with no arbitrary witness selection.

## 180. Odd marked grading unconditionally activates the enlarged ledger

For each maximal H-run `A`, define its port-feature ledger

```text
F_A:=p_(s_A)+n_A,                                     (561)
```

where `s_A,n_A` are its totally silent and nonsilent port indicators.  By
(551), the footprint term has mass `|s_A|`; the nonsilent term has mass
`|n_A|`.  Since these two sets partition the H ports of `A`,

```text
1^T F_A=|s_A|+|n_A|=ell(A) mod 2.                     (562)
```

Sum over all H-runs of the mixed dart cycle and put

```text
F_Z:=sum_A F_A.
```

Equations (299) and (562) give the unconditional activation identity

```text
1^T F_Z=omega_M(Z).                                   (563)
```

Therefore odd marked grading forces `F_Z != 0`.  Cancellation between
different runs cannot erase the ledger, because its total mass is odd.
Every nonzero term is one of two explicit, uniformly bounded types:

```text
silent:    a three-port shadow footprint with labeled cut normal form;
nonsilent: a degree-at-most-six cross-label wedge atom from (558).       (564)
```

Moreover, summing (560) shows that the oriented phase vector `alpha_Z` is
homologous to `F_Z` modulo the labeled shadow cuts and canonical H-run path
boundaries (and orientation changes lie in the old `partial_H` quotient).
Thus the A0 activation gap of Section 149 is closed **for the enlarged
feature alphabet**: an odd component necessarily contains a nonzero
owner-resolved feature ledger.

This is not yet the Erdős 85 contradiction.  The remaining capacity theorem
must show that an odd-mass ledger built from the two atom types (564) cannot
be conserved by the simultaneous route-reversal pairing.  Unlike the old
activation question, that theorem starts with a guaranteed nonzero, fully
located, bounded-degree object.

## 181. The enlarged center alphabet has private full-state tags

For an H port `z` with roots `x,x'`, retain the role-partitioned six-label
tuple

```text
Sigma(z):=(N_d(x),N_d(x'),N_d(z))                    (565)
```

and its active subset

```text
T(z):={y in the six entries of Sigma(z):t_y=1}.       (566)
```

The three pairs in (565) are disjoint by (547).  The last pair
`N_d(z)={y_1,y_2}` uniquely determines the center port `z`: a second port
adjacent to both `y_1,y_2` would give that port pair two common neighbors,
a C4.  Hence the full role-tagged state `(Sigma(z),T(z))` is private to one
H-port occurrence on the dart-cycle decomposition.

Use the 64 one-hot activity states

```text
a_(Sigma,T)(z):=[Sigma(z)=Sigma and T(z)=T],
T subseteq the six role positions.                    (567)
```

The state `T=empty` is total silence.  The other 63 states partition
nonsilence and give a one-hot version of the Boolean expansion (558):

```text
n(z)=sum_(empty != T) a_(Sigma(z),T)(z).              (568)
```

Unlike individual monomials in (558), a one-hot atom retains the inactive
labels too, including the private port-label pair.  Thus distinct centers
cannot collide merely because they share one active secondary label.

The silent footprint atom also carries the state `(Sigma,empty)` and its
two uniquely labeled shadow edges.  Therefore both atom types in (564) fit
one finite, private center alphabet:

```text
nonempty T: one center unit with its full six-label activity state;
empty T:    one center plus its two inactive labeled companions.         (569)
```

This settles the privacy side of the enlarged activation ledger at the
center level.  It does not prove conservation under route reversal: the
next theorem must show how the private states (569) are paired or priced by
the simultaneous owner ledger.  Any failure can no longer be blamed on a
collision of coarse secondary labels.

## 182. Odd grading forces an odd fixed-point-free reversal orbit

Use the orientation of each H-run to order the two roots of an H port as
incoming and outgoing.  Write a center state as

```text
tau=((Y_-,Y_+,Y_P),T),                               (570)
```

where `Y_-,Y_+` are the two-element `d`-neighbor sets of the ordered roots,
`Y_P` is the two-element port-label set, and `T` records the active role
positions.  Reversing the run acts by

```text
rho(tau)=((Y_+,Y_-,Y_P),rho(T)),                      (571)
```

with `rho(T)` swapping the two root-position pairs and fixing the port
positions.

This involution has no fixed center state.  By (547), `Y_-` and `Y_+` are
disjoint nonempty sets, so they cannot be equal.  Thus every one of the
private 64-state occurrences belongs to a two-element reversal orbit
`{tau,rho(tau)}`.  For a silent state, the three-port footprint is unchanged
as an untagged vector, but its oriented private tag still moves to the other
member of the orbit.

Each H port contributes exactly one center atom: its nonempty activity state
when nonsilent, or its empty-state footprint when silent.  Therefore the
parity of the total number of center atoms is the number of H ports, and
over all runs of `Z` it is

```text
sum_(reversal orbits O) #atoms in O
 =omega_M(Z) mod 2.                                   (572)
```

If `omega_M(Z)=1`, at least one fixed-point-free reversal orbit has odd
occupancy.  This conclusion is stronger than merely `F_Z != 0`: it locates
an unpaired **oriented private state**, even if its port-vector support
overlaps other footprints.

The final conservation theorem can now be stated without matrices or
pricing ambiguity:

```text
simultaneous route reversal makes every orbit
{tau,rho(tau)} have even occupancy.                   (573)
```

Equation (573) is not proved here.  If established with the shadow/run
boundary payments of Sections 177--179 attached, it contradicts (572)
immediately and completes the mixed-cycle kernel theorem.

**Scope correction (Section 227).**  At the fully private resolution used
here, (573) is in fact overstrong: the private port state pins one physical
H occurrence, so its reversed state cannot be supplied by a distinct
occurrence with the same full tag.  The valid terminal must be a coarser
route quotient or price retaining the marked character, not literal even
occupancy of every orbit in (573).  Equation (572) remains a correct
localization identity.

## 183. Center states form a directed root-state path with private edge labels

For a root `x`, define its secondary activity state

```text
R_d(x):=(N_d(x), (t_y)_(y in N_d(x))).                (574)
```

For a port `z`, define the analogous port state `P_d(z)`.  The oriented
center state (570) factors exactly as

```text
tau(z)=(R_d(x_-), P_d(z), R_d(x_+)),                  (575)
```

where `x_-,x_+` are the ordered roots of the H port.  The middle state
contains the private port-label pair, while the two endpoint states are the
root-role parts of `Sigma,T`.

Successive H port pairs in one run meet at a common root.  Therefore the
target root state of one directed edge (575) is literally the source root
state of the next.  If `C_A` is the sum of the directed center edges of a
run, its coarse incidence boundary telescopes:

```text
partial_R C_A=[R_d(x_exit)]-[R_d(x_entry)].           (576)
```

Over `F_2` the sign is immaterial, but retaining the orientation identifies
which endpoint is which.  All internal 64-state occurrences cancel at the
root-state boundary level, with their private port states retained on the
edges.

The non-H port pairs in the intervening gaps also connect consecutive roots
of the same auxiliary dart cycle.  Forgetting their V/S decorations and
keeping only endpoint root states makes the full directed port-edge flow
closed.  Hence the coarse endpoint conservation needed for (573) is
automatic; the only possible obstruction is a directed cycle holonomy in
the private edge labels `P_d(z)` and the V/S gap decorations.

This also shows why (573) is stronger than ordinary flow conservation.  A
closed directed cycle can use every private edge only in one orientation.
The terminal theorem must price or cancel that labeled holonomy using the
simultaneous route-reversal data of the non-H gaps; endpoint telescoping
alone cannot make reversal-orbit occupancies even.

## 184. The non-H gaps lift to the same private directed-edge alphabet

For every port pair `z` of the auxiliary dart cycle, not only an H port,
orient its roots as `x_-,x_+` and let `D_-(z),D_+(z)` be the complete dart
decorations at the two ends.  Each decoration is `H`, `S` with its switch
identifier, or `V_ell` with its resolved route label.  Define the full
port-edge state

```text
epsilon(z):=(R_d(x_-),D_-(z),P_d(z),D_+(z),R_d(x_+)). (577)
```

The port activity state `P_d(z)` contains the two-label set `N_d(z)`, which
pins `z` uniquely by C4 as in Section 181.  Hence (577) is a private edge
tag.  Reversal acts without choices by

```text
rho(epsilon)
 =(R_d(x_+),D_+(z),P_d(z),D_-(z),R_d(x_-)).           (578)
```

Again there are no fixed states because the two root-label sets are
disjoint nonempty sets.

At a common root, consecutive port edges have exactly the same root state,
including its two activity bits.  Therefore the complete sequence of
states (577) around an auxiliary dart component is a closed directed cycle
in the root-state graph, with private labeled edges.  The H center alphabet
of Sections 181--183 is precisely the subalphabet

```text
D_-=D_+=H.                                            (579)
```

All V/S gap data now live on the complementary edge states of the **same**
closed flow; there is no longer a separate endpoint-lifting problem.

This is an exact finite formulation of the remaining holonomy theorem:
among closed state cycles (577) realizable by the simultaneous routing
identities, every reversal orbit of H--H edges must have even occupancy.
Arbitrary closed labeled cycles do not satisfy this, so closure and privacy
alone are insufficient.  The final input must be the route/switch algebra
on the non-H edge decorations in (577), which is now the only data not yet
used by (576).

## 185. The exact decoration automaton has paired switch excursions

The rooted budget classification (297) gives the complete compatibility
rule for two consecutive port edges at a root.  Ignoring the resolved
labels but retaining decoration type, the unordered pair of incident dart
decorations is exactly one of

```text
HH, HV, VV, SS.                                       (580)
```

In particular, H meets a non-H edge only through V, never S, and a root
transition never changes V to S.  A type change V--S can occur only across
a **port edge** whose two endpoint decorations are V and S.

Every maximal non-H gap lies between two H-runs, so (580) makes its first
and last root-side decorations V.  Traversing the gap, each mixed V--S port
edge toggles the current type and root transitions preserve it.  Therefore

```text
number of mixed V--S port edges in each gap is even.  (581)
```

They pair canonically in traversal order into switch excursions: enter an
S segment across one mixed port edge and leave it across the next.  Inside
an S segment every root transition is S--S; outside, every root transition
is V--V, with the two gap endpoints supplied by H--V transitions.

Thus switch parity itself cannot carry the odd H holonomy.  After each
paired S excursion is contracted to a labeled V-to-V transfer, a gap is a
directed path of resolved V-route states from its entry label to its exit
label.  The remaining conservation problem is entirely the holonomy of
these V-route turns together with the internal labels of the paired switch
excursions; there is no unpaired switch endpoint to absorb an odd H state.

Equation (581) is only the type-level automaton.  It does not assert that a
paired switch excursion has trivial private price—its rooted identifiers
must remain in the edge state (577).  It removes one possible escape and
reduces the final problem to V-turns plus two-ended S excursions.

## 186. Each switch excursion is a unique unoriented transfer path

Restrict the auxiliary dart structure to S-decorated darts.  At an S root,
the rooted budget state is `(S,S)`, and the root involution pairs the two
darts by the unique `A_e` fiber switch.  At a port, the port involution
either pairs two S darts internally or pairs an S dart with a V dart at one
of the mixed edges counted in (581).

Therefore the graph on S darts with root-switch and internal S--S port
pairings has maximum degree two.  Its components are cycles and paths; the
path endpoints are exactly the S sides of mixed V--S port edges.  The
consecutive pairing from Section 185 selects one such path for every switch
excursion.

There is no choice of route through the component.  Retain on the path its
ordered list of rooted switch identifiers and internal port states.  Run
reversal reads the same physical path backward, so after forgetting its
endpoint orientation the full internal label is unchanged.  Thus an
excursion has a canonical unoriented transfer tag

```text
U_S={mixed endpoint 1 -- labeled S path -- mixed endpoint 2}. (582)
```

Closed S-only components never meet an H-run and contribute no endpoint to
a mixed gap; they may be audited separately but cannot absorb one member of
an H reversal orbit.

Contracting (582) loses no internal switch information and introduces no
pairing gauge.  Any reversal-odd character of an S excursion is entirely
the orientation of its two V-side endpoints; the internal S path itself is
an unoriented label.  Hence the final holonomy table can replace arbitrary
S words by private two-ended transfers and concentrate on how their V
endpoints join the resolved V-route turns.

## 187. Contracting the full state cycle recovers the canonical chain `Xi`

Apply three canonical contractions to the closed edge-state cycle (577).

```text
maximal H--H subpath:
  contract to its two V boundary labels, retaining the H-run word;

maximal S excursion:
  contract its unique path (582) to its two V handoff labels;

remaining V sector:
  retain every V--V root turn and V--V port passage with its sign.        (583)
```

After forgetting the root activity states and the internal private words,
the three outputs are exactly the previously defined chains

```text
T_H(Z),       T_S(Z),       C_V(Z),                   (584)
```

respectively.  Therefore the coarse quotient of the full state cycle is

```text
Xi(Z)=C_V(Z)+T_H(Z)-T_S(Z)                            (585)
```

from (350).  Its closure is not a new assertion: it is the image of the
literal root-state closure of Section 184.

The refinement retains precisely the data discarded in Section 117:

```text
on T_H: the ordered private center states and run-length parity;
on T_S: the full unoriented switch-path tag;
on C_V: the ordered rooted triangle labels and port activity states.     (586)
```

The odd reversal orbit from (572) lives on the refined `T_H` edges and
projects to the marked-grading character of `Xi`.  Consequently the open
statement (573) is exactly the full-state lift of the old holonomy target
(351), not a different conjecture.

This identification prevents a false shortcut.  Closure of `Xi` proves
only endpoint conservation, already captured by (576); it does not control
the private words in (586).  The final theorem must show that the marked
character vanishes on the **realized refined lift** of `Xi`, using the
route-reversal identities on `C_V` and the canonical two-ended nature of
`T_S`.  All combinatorial transfers required to state that theorem are now
constructed and audited.

## 188. Odd grading localizes to one refined `Xi` cycle

Reduce the canonical closed chain `Xi(Z)` modulo two, retaining a distinct
copy of every private occurrence label from (586).  Its incidence boundary
is zero, so the resulting V-label multigraph is Eulerian.  Pair incident
half-edges arbitrarily at every label vertex and decompose the edge set into
closed trails.

Give a refined `T_H` edge the weight

```text
weight(A)=ell(A) mod 2,                               (587)
```

and give every `C_V` and `T_S` edge weight zero.  The total edge weight is

```text
sum_(edges of Xi) weight
 =sum_(H-runs A) ell(A)
 =omega_M(Z).                                        (588)
```

Therefore, when `omega_M(Z)=1`, every cycle decomposition contains at least
one closed trail of odd weight.  Choose an inclusion-minimal odd closed
subchain.  It is connected and contains no proper nonempty closed odd
subchain; all edge occurrences still carry their full H-center word,
unoriented S-path tag, or rooted V-turn tag.

This extraction is pairing-gauge independent at the existence level.  A
different half-edge pairing can change the chosen trail but cannot make all
trails even, because their weights always sum to (588).  Thus the final
conservation theorem may focus on one support-minimal refined cycle selected
from the realized chain, with an odd total of H-run parities.

No contradiction follows from Eulerianity alone—arbitrary labeled
multigraphs admit such cycles.  The remaining task is now maximally local:
use route reversal on the ambient `C_V` edges and the canonical unoriented
`T_S` transfers to show that no circuit selected from a simultaneously
realized refined chain can have odd weight (587).

## 189. The minimal odd subchain is a graphic circuit

Let `K` be an inclusion-minimal odd closed subchain supplied by Section 188,
with containment understood on the distinct refined edge occurrences.  In
fact `K` has no proper nonempty closed subchain of either parity.  Indeed, if
`J` were such a subchain, then

```text
weight(J)=1  => J is a smaller odd closed subchain;
weight(J)=0  => K+J is a smaller odd closed subchain.             (589)
```

Both alternatives contradict the choice of `K`.  Thus `K` is a circuit of
the binary cycle matroid of the V-label multigraph.

Equivalently, after retaining multiplicities and private occurrence tags,
the support of `K` is one graph-theoretic cycle: a loop, a pair of parallel
edges, or a connected simple cycle of length at least three.  To see this
directly, every vertex of `K` has even degree.  If some vertex had degree at
least four, pairing two incident half-edges and following the finite
Eulerian support until the first return would produce a proper nonempty
closed subchain, contrary to (589).  Hence every incident vertex has degree
two, and connectedness gives the stated circuit classification.

Consequently `K` has a unique cyclic traversal up to rotation and reversal.
There is no remaining half-edge-pairing gauge and no repeated coarse V
label on a circuit of length at least three: two distinct visits would force
degree at least four at that label vertex.  In particular the odd identity
becomes

```text
sum_(A in K cap T_H) ell(A) = 1.                    (590)
```

The terminal character may therefore be evaluated on a single oriented
refined circuit and compared with the same circuit in the reverse
orientation.  Its only orientation-sensitive data are the rooted `C_V`
turns and the V-side ordering of the unoriented `T_S` transfers; all H words
and S interiors are carried unchanged.

This is a support reduction, not a new realization theorem.  Although every
edge of `K` comes from the one realized ambient dart cycle, an arbitrary
subset selected by (589) need not itself be closed under the physical root
and port matchings.  Thus route identities may be restricted to `K` only
when they are edge-local or after their complementary ambient terms have
been shown to cancel.  The final proof must not treat `K` as an independently
realized routing component.

## 190. Circuit exclusion is exactly a cut-space theorem

Let `G_Xi` be the finite V-label multigraph containing the distinct refined
edge occurrences of the realized chain, and let `w` be the edge cochain
from (587).  Over `F_2`, the following are equivalent:

```text
(i)  every closed subchain J of G_Xi has <w,J>=0;
(ii) every graphic circuit K of G_Xi has <w,K>=0;
(iii) there is chi:V(G_Xi)->F_2 with
      w[ell,m]=chi(ell)+chi(m) on every refined edge occurrence. (591)
```

The equivalence of (i) and (ii) follows because graphic circuits generate
the binary cycle space.  For (iii), choose one base vertex in each connected
component and define `chi(v)` as the sum of `w` along any path from the base
to `v`.  Circuit vanishing makes this path-independent, and the edge formula
follows.  Conversely that formula telescopes on every closed subchain.

Thus Sections 188--189 do not by themselves make the holonomy theorem
edge-local.  They identify the exact dual form of the **circuit-exclusion
strategy**: the simultaneous route and switch identities would have to
prove that the realized H-parity cochain `w` lies in the cut space of
`G_Xi`.  This is the mod-two refined version of the label
potential criterion (352)--(354), with `chi` allowed initially only on the
vertices actually present in the realized support.

The two smallest falsification checkpoints are immediate from (591):

```text
an H-transfer loop [ell,ell] must have even run length;
two parallel refined edges with the same endpoints must have equal w.   (592)
```

Either failure is already an odd graphic circuit.  For a simple circuit of
length at least three, (591) asks that the edge phases integrate consistently
around its distinct V labels.  The private H words and S paths may be used
to prove these equalities, but they cannot be hidden by projecting to the
coarse label graph.

Accordingly this route to the remaining geometric theorem has a precise
output: construct the potential `chi` in (591), or equivalently prove the
loop, parallel-edge, and simple-circuit exclusions, from the realized `C_V`
route reversals and the two-ended `T_S` transfers.  A proof may instead use
an ambient cancellation special to `Xi` without annihilating the whole cycle
space; the circuit reduction alone does not justify that stronger step.  No
purely graphic argument can supply either conclusion.

## 191. The loop checkpoint lies entirely in the target-even channel

The first condition in (592) is not a formal consequence of the current
local geometry.  Section 159 gives the exact classification instead.  If an
H-run has the same resolved route label `ell=(d,y)` at both boundaries, its
two route occurrences use the two distinct target ports in the `d--e` fiber
of `y`; hence

```text
T_H edge [ell,ell]  =>  t_y=0,
                         N_e(y) is exhausted by the two boundary ports. (593)
```

Nothing in (509) forces the run length to be even.  Therefore the active
connector channel cannot by itself prove the loop clause of (592): the
actual route label is absent from the target-active signature at both ends.
An odd same-label run, if globally realizable, is precisely an odd loop for
`w` and refutes the full cut-space potential (591).

This does not refute the desired ambient identity `<w,Xi>=0`.  It identifies
the payment that identity must retain.  The two consumed target ports in
(593) form a private target-even capacity unit; an ambient proof must either
pair such units with another odd H transfer or transport them through the
silent-footprint/boundary ledger of Sections 176--180.  Projecting only to
active V connectors discards the sole visible trace of the loop.

Thus the cut-space strategy has a clean branch test:

```text
prove odd same-label H runs impossible; or
abandon full label descent and prove their target-even capacity units
cancel in the particular ambient chain Xi.                           (594)
```

The second branch is the current honest default.  Its structural analogy
with the zero-price inactive channel in the Baer lane is suggestive, but no
coordinate identification between those two ledgers is asserted.

## 192. The constant-channel rows do not locally exclude the odd loop

It is tempting to combine the saturated owner in (593) with the finite
constant-channel templates (540) and claim an immediate capacity collision.
That inference is not valid.  The two constructions use different labels
and different port sectors.

The common route owner `y` in (593) is target-even: `t_y=0`.  By contrast,
the word and templates of Sections 161--172 are defined for a target-active
secondary label `u`, so `t_u=1` and necessarily `u!=y`.  The distinguished
port `P=r_u` in (540) is the unique target port of this active `u` inside
`V_j`; it is not one of the two ports of `y` by owner identity alone.

There is also a type separation.  The two ports consumed by `y` are the
V-side ports of the two H--V boundary root pairs.  The positions in the
constant word (540) are H--H port pairs internal to the run (with a possible
endpoint H port still distinct from its V mate).  Thus the raw fiber bounds

```text
|N_e(y) cap V_j|=2,          |N_e(u) cap V_j|=1       (595)
```

do not compete for a common labeled capacity.  They can coexist in the
finite local incidence table unless an additional cross-label C4 or owner
matching condition couples `u` to `y`.

Consequently (509) plus (540) alone cannot prove that an odd same-label
transfer is impossible.  Any successful local exclusion must add at least
one of the following genuinely simultaneous data:

```text
an incidence joining an active witness u to a y-owned boundary mate;
a collision between their resolved owner factors;
or the ambient labeled boundary equations coupling this run to its gaps. (596)
```

This leaves the finite rows useful but correctly scoped: they classify the
active secondary channel surrounding a target-even owner; they do not price
that owner's two-port unit by themselves.  The ambient silent-footprint
transport is a candidate mechanism with the right inactive character, but
no proved identity yet attaches the boundary owner's two-port unit to that
ledger.

## 193. A diagonal H transfer is invisible to every label boundary

For a same-label H transfer `e=[ell,ell]`, the mod-two incidence boundary is

```text
partial e=[ell]+[ell]=0.                              (597)
```

Consequently every endpoint potential, and every identity obtained only by
applying the V-label incidence boundary, evaluates trivially on `e`:

```text
<delta chi,e>=<chi,partial e>=0.                      (598)
```

This remains true after adjoining arbitrary `C_V` turns or `T_S` transfers;
their endpoint conservation can close the ambient chain but cannot reveal
the parity carried by a diagonal H edge.  In particular, the coarse closure
of `Xi` and the boundary identities (345)--(349) contain no term capable of
distinguishing an even same-label run from an odd one.

Therefore the second branch of (594) cannot be completed by another
V-label boundary calculation.  It requires a genuinely refined equation
whose state space remembers at least the target-even owner occurrence in
(593).  Equivalently, if `b_y(A)` denotes the private bit that the two
boundary ports exhaust the `y` fiber, the needed local-to-ambient transport
has the form

```text
(ell(A) mod 2) [ell,ell]
   --> b_y(A) + private C_V/T_S owner-state payments,                (599)
```

where the right-hand side must then cancel in the realized ambient cycle.
Equation (599) is a target statement, not an asserted identity.

This separates the two residual mechanisms cleanly.  Non-diagonal circuit
weight may in principle be killed by a label potential; diagonal weight can
only be killed by private capacity conservation.  The full-state lift of
Sections 181--184 retains enough data to state that conservation law, while
the coarse chain (585) provably does not.

## 194. The diagonal obstruction disappears on full boundary states

The loop in (597) is a loop only after projecting a boundary occurrence to
its coarse resolved label `ell=(d,y)`.  Before that projection, retain at an
H--V boundary the incident data already present in the full edge state
(577): the rooted V state, its V-side port state, and the side decoration.
This is the state of the actual V-dart occurrence at which two contracted
pieces meet, not merely an isomorphism type of that state.  Write it as

```text
hat(ell)=(ell,R_d(x),P_d(z_V),side).                  (600)
```

The two ends of a same-label H run have distinct V-side ports by (509).
Since `P_d(z_V)` retains the port identity, their full states are distinct:

```text
ell(E_-)=ell(E_+),   but   hat(ell)(E_-) != hat(ell)(E_+). (601)
```

Thus the corresponding refined H transfer is an ordinary edge between two
different full-state vertices.  It becomes the diagonal generator
`[ell,ell]` only under the forgetful projection
`hat(ell) -> ell`.

Contract the full state cycle of Section 184 as in Section 187 while keeping
the endpoint occurrences (600).  Adjacent contracted pieces meet at the
same V dart, so they receive literally the same endpoint occurrence.  This
produces a full-state multigraph
`G_hatXi` mapping onto `G_Xi`; its H, S, and V edges retain exactly the data
in (586), and its incidence closure is inherited from the literal state
closure (579).  On `G_hatXi`, an endpoint potential is allowed to distinguish
the two saturated ports of the target-even owner:

```text
w(E_-,E_+)=hatChi(hat(ell)(E_-))+hatChi(hat(ell)(E_+)). (602)
```

Equation (602) is again a target, not a proved potential.  Its importance is
that odd same-label runs do not formally refute **full-state** descent; they
refute only descent through the coarse label projection.  The private
capacity bit demanded by (599) is precisely the information separating the
two vertices in (601).

Because occurrence identities are retained, existence of `hatChi` on an
entire component is equivalent to vanishing of the ambient holonomy on that
component; this lift does not make the theorem tautologically true or give
a reusable potential depending only on a bounded state type.  Its gain is
only to locate the information that coarse projection erased.

The remaining theorem can therefore be stated without demanding the false
coarse loop condition: show that the H-parity cochain lies in the cut space
of `G_hatXi`, or prove the weaker ambient cancellation there, using the
root/port transition algebra.  Only after that cancellation may one project
to the canonical coarse chain `Xi`.

## 195. The Baer potential reaches `C_V` only through a pairing gauge

There is a natural but noncanonical comparison with the paired-star graph
used in the Baer lane.  A `C_V` edge joins two resolved route labels
`y_1,y_2` whose V darts are paired at a common root or port witness `r`.
Thus `y_1,y_2` are two neighbors of `r`, exactly the local vertex domain on
which the Baer star pairing acts.

However, the two pairings are defined independently:

```text
C_V: the actual root/port matching of the realized dart cycle;
P_r: the canonical iota_r pairing on the 00 sector plus an
     owner-adapted completion on the broken-T sector.                 (603)
```

Sections 113--116 prove distinctness and privacy of the `C_V` labels, but
they do not prove that an actual V--V pair is an edge of `P_r`.  Therefore
the Baer vertex potential `lambda` from (73rnz_cjibkq) cannot simply be
pulled back along `C_V`.

When two admissible pairings use the same finite endpoint set, their
symmetric difference is a union of alternating even cycles, and one is
obtained from the other by four-endpoint switches

```text
{a--b,c--d} <--> {a--c,b--d}.                         (604)
```

Hence on any star sector where the actual V pairing can first be completed
to the same endpoint set as `P_r`, transporting `lambda` to `C_V` is
equivalent to the local quadrilateral price identity (73rnz_cjibd).  A
failure produces the localized four-relay holonomy; success gives the
additive form (73rnz_cjibe).

This is a conditional gauge dictionary, not yet a bridge theorem.  Two
inputs remain to be proved before importing the Baer potential:

```text
(a) compatible completion: include every realized V--V pair in a full
    star pairing with the same typed endpoint population as P_r;
(b) price invariance: verify (604) for every typed switch used in passing
    between that completion and P_r.                                  (605)
```

The H/S decorations in the full state (577) are precisely the data needed
to audit (a); the bounded four-relay state table of Section 166 is the local
obstruction to (b).  Until both are discharged, the SRP and Baer potentials
share an exact cycle--cut mechanism but not a canonical coordinate map.

## 196. Scalar full-state cancellation is enough for SRP

The orbit statement (573) is a sufficient terminal, but it is stronger than
the contradiction actually required.  If `n_O` is the occupancy parity of a
reversal orbit `O`, then (572) says only

```text
omega_M(Z)=sum_O n_O.                                 (606)
```

Proving every `n_O=0` certainly forces `omega_M(Z)=0`, but the mixed-cycle
kernel theorem needs only the latter scalar equality.  Equivalently, for the
full-state graph of Section 194 it suffices to prove

```text
<w,G_hatXi>=0,                                        (607)
```

or to construct a scalar endpoint potential whose coboundary is `w` on the
particular realized component.  No owner-resolved assignment of individual
reversal orbits is necessary.

This is an important scope difference from the Baer terminal.  There the
primary source is the two-coordinate class `(1,1)`, and changing a path
decomposition may attach the two pole owners to different terminal flip
states; scalar endpoint pricing does not by itself preserve that owner
vector.  Here all H-run contributions enter the single grading (606), so a
pairing-independent **total** endpoint price already proves the required
contradiction even if individual orbit labels are reassigned.

Therefore the gauge-mediated bridge of Section 195 may be used at scalar
strength.  Compatible completion plus invariance of the total four-switch
price would suffice for (607); the stronger task of transporting every
private reversal-orbit label should be imposed only if scalar cancellation
fails.  This strictly weakens the live SRP target without changing its
conclusion.

## 197. Additive total price is automatically pairing-independent

Suppose the no-holonomy branch of the Baer paired-star dichotomy supplies a
vertex potential `lambda` on one typed star endpoint population `U`.  Extend
its pair price from the canonical edges of `P_r` to every unordered pair in
`U` by

```text
w_lambda(a,b):=lambda(a)+lambda(b).                   (608)
```

For every perfect matching `M` of the same endpoint population,

```text
sum_({a,b} in M) w_lambda(a,b)
 =sum_(a in U) lambda(a).                             (609)
```

Hence this total is independent of `M`.  In particular every four-endpoint
switch (604) has zero `w_lambda` defect automatically; no separate table of
switch identities is needed for the scalar total once the additive potential
exists.

This sharpens (605) in the additive branch.  The live bridge conditions are
now:

```text
(a) compatible completion: realize the full H/V/S star data as a matching
    of the same typed endpoint population U;
(b) price identification: show that the aggregate SRP edge price
    (H contributes its marked parity; V/S contribute their audited
    payments) equals the extended total (609), modulo proved boundaries. (610)
```

Condition (b), not pairing gauge, is the remaining scalar content.  The
canonical and realized matchings may pair endpoints differently without
changing (609).  This does not solve (610): `lambda` is known initially from
K-prices on the Baer `00/11` edges, while the SRP H/V/S price lives on a
different decorated edge alphabet.  An occurrence-level identification of
those aggregate prices is still required.

In the alternative odd-holonomy branch no `lambda` exists and this extension
is unavailable; the localized odd K-cycle must instead be converted directly
to the Erdős 85 contradiction.  Thus (608)--(610) simplify only the additive
branch and make no assumption about the other branch.

## 198. Every `C_V` star matching has an untyped perfect completion

Fix one root or port witness `r`.  The realized `C_V` edges at `r` are
pairwise disjoint as edges on `N_A(r)`.  Indeed, if one resolved route label
`y` occurred in two such pairs at the same root (respectively port), then
the support of the intermediate-resolved matrix `F_(d,y)` would contain two
entries in one row (respectively column), contradicting the partial-matching
theorem of Section 113.

Thus the `C_V` edges at `r` form a partial matching `M_V(r)` on the `q`
neighbors of `r`.  Since `q` is even, the number of uncovered endpoints is

```text
q-2|M_V(r)|=0 mod 2.                                  (611)
```

Pair those endpoints arbitrarily.  This extends `M_V(r)` to a perfect
matching `M_hat(r)` of the same untyped endpoint population `N_A(r)` used by
the Baer star pairing `P_r`.

Consequently condition (610a) is automatic after forgetting endpoint types:
the actual V--V turns and `P_r` are two matchings of the same neighbor set,
so the additive total (609) is identical on them regardless of the chosen
completion.  No injectivity or parity obstruction remains at this level.

The completion is not yet geometrically priced.  Its added pairs represent
the neighbors not consumed by V--V turns; the current argument neither
identifies them with the realized H/S decorations nor respects the `00/11`,
owner, and activity subtypes of `P_r`.  Therefore the entire additive-branch
interface has reduced to one typed aggregate statement:

```text
price of the arbitrary complement M_hat(r) setminus M_V(r)
 = audited H/S boundary and transfer payments at r, modulo boundaries. (612)
```

Equation (612) is the local form of (610b), not a proved identity.  The
point is that completion existence and scalar pairing gauge are now both
discharged; only the price attached to the complementary endpoints remains.

## 199. Typed completion has one T-word parity obstruction

The type used by the Baer star pairing is not the SRP target-activity bit
`t_y`.  For `y in N_A(r)` it is instead

```text
tau_r(y):=1[ry in T].
```

Let `W_r` be the endpoints already consumed by the partial V matching
`M_V(r)`.  The canonical Baer star pairing has no mixed T-word: its pairs lie
in the `00` or `11` sectors.  Therefore the arbitrary completion in Section
198 can be chosen with the same T-word rule if and only if the number of
T-marked uncovered endpoints is even.

Define the obstruction

```text
kappa_T(r):=sum_(y in N_A(r) setminus W_r) tau_r(y)
           =deg_T(r)+sum_(y in W_r)tau_r(y)
           =sum_(y in W_r)tau_r(y).                   (613)
```

The last equality uses the audited fact that `deg_T(r)` is even.  Since `q`
is even, `kappa_T(r)=0` makes both uncovered T-word populations even, so they
can be paired separately into `11` and `00` edges.  Conversely a same-type
completion pairs the marked uncovered endpoints two at a time and forces
`kappa_T(r)=0`.

If `kappa_T(r)=1`, every perfect completion of the untyped matching contains
an odd number of mixed `01` pairs.  Such a completion cannot be identified
with `P_r`, whose canonical pairing preserves the T-word sectors.  Thus
(613) is the complete typed-population obstruction to condition (610a); no
larger matching table is needed.

The right side of (613) is fully resolved by the actual V decorations and
the T-membership of their witness edges.  It has no direct identification
with the target-activity states `t_y`, the silent footprints, or the Baer
activation bit `s=A(tx)`.  A necessary scalar residual identity for the
gauge bridge is

```text
sum_(relevant root/port witnesses r) kappa_T(r)=0,     (614)
```

with the same occurrence weights used in (610b).  Equation (614) is a
target; (613) is the proved local reduction.  Vanishing of (614) alone does
not give a same-type completion separately at every star: a transport
identity must pair the nonzero `kappa_T(r)` defects through the realized
H/S sectors.  If even the scalar sum fails, an odd mixed-T-word endpoint is
the located obstruction that the final capacity argument must price.

## 200. The typed obstruction is exactly mixed-word `C_V` parity

Because `W_r` is the disjoint union of the endpoint pairs in `M_V(r)`, the
last expression in (613) can be regrouped edgewise:

```text
kappa_T(r)
 =sum_({y_1,y_2} in M_V(r))
      (tau_r(y_1)+tau_r(y_2))
 =#{mixed 01 T-word edges of M_V(r)} mod 2.            (615)
```

Thus a `00` or `11` realized V--V turn contributes nothing to the typed
completion obstruction, while a mixed `01` turn contributes one.  No
activity state, owner label, or completion choice enters (615).

Summing over the root and port witnesses used by the realized dart cycle
gives

```text
sum_r kappa_T(r)
 = parity of all mixed-T-word C_V turns on Z.          (616)
```

Consequently the target (614) is precisely an evenness statement for the
mixed-T-word V--V sector.  The complement price (612) need not repair any
same-word turn; it only has to route the endpoints of the mixed turns through
the H/S sectors or show that their total is even.

Equation (616) does not assert that this parity vanishes.  The existing
unweighted V marginal (345) forgets `tau_r`, so it cannot supply (616) by
itself.  A successful next identity must be the T-word-weighted refinement
of the H/V/S marginal, retaining the actual root or port witness on every
mixed endpoint.

## 201. The T-word-weighted H/V/S marginal is exact

For a V dart `v` with resolved label `y`, root witness `x`, and port witness
`z`, define its two T-leg bits

```text
tau_R(v):=1[xy in T],        tau_P(v):=1[zy in T].     (617)
```

Let `m_R` and `m_P` be the parities of mixed-T-word V--V pairs at roots and
ports, respectively.  Also define the weighted boundary terms

```text
b_HV^T:=sum_(root H--V pairs) tau_R(the V dart),
b_SV^T:=sum_(port S--V pairs) tau_P(the V dart),
q_V^T :=sum_(all V darts v) (tau_R(v)+tau_P(v)).       (618)
```

Count `tau_R` over all V darts through the root matching.  A V--V root pair
contributes `tau_R(v_1)+tau_R(v_2)`, which is one exactly for a mixed pair;
an H--V root pair contributes its single V bit.  The root alphabet (297) has
no other V case.  Therefore

```text
sum_(V darts v) tau_R(v)=m_R+b_HV^T.                  (619)
```

The identical count through the port matching uses only V--V and S--V
unmarked pairs, giving

```text
sum_(V darts v) tau_P(v)=m_P+b_SV^T.                  (620)
```

Adding (619)--(620) yields the exact weighted marginal

```text
m_R+m_P=q_V^T+b_HV^T+b_SV^T.                          (621)
```

By (616), the left side is the global typed-completion obstruction on `Z`.
Thus all of its residual information lies in the three located terms on the
right: the two-leg T defect of actual V triangles, the T-marked H boundary,
and the T-marked S handoff.

No relation between `tau_R(v)` and `tau_P(v)` is assumed here.  In
particular, (621) does not discard `q_V^T` by claiming that the two legs of a
rooted triangle have equal T status.  The remaining geometric task is now
exactly to evaluate `q_V^T` and transport the two boundary terms through the
canonical H runs and S excursions.

## 202. Every V endpoint has T-word zero

Recall that

```text
T=A cap D
```

is the triangle-free edge graph: an A-edge belongs to `T` exactly when it
lies in no triangle.  A V dart with root `x`, port `z`, and resolved label
`y` is, by definition (Section 99), the actual rooted triangle

```text
x--y--z--x.                                           (622)
```

Hence both A-edges incident with its route label lie in a triangle and are
not in `T`:

```text
tau_R(v)=1[xy in T]=0,
tau_P(v)=1[zy in T]=0.                                (623)
```

It follows immediately that every realized `C_V` endpoint has T-word zero.
In particular, pointwise at every root or port witness,

```text
kappa_T(r)=0,        m_R=m_P=0,                       (624)
```

and all three terms in the weighted marginal (621) vanish separately.

Thus the typed-population condition in (610a) is fully discharged, not just
after summing witnesses: every `C_V` partial matching lies entirely in the
`00` endpoint sector, and its uncovered endpoint population has even `11`
cardinality because `deg_T(r)` is even.  It extends to a perfect matching
with only `00` and `11` pairs.

This does not yet prove the price identity (612).  It removes the mixed-word
sector altogether and leaves a cleaner complement: canonical `00` pairs
have zero K-price/additive `lambda` defect, while the added `11` pairs carry
the broken-T matching price.  The remaining H/S aggregate identity must
show that the realized non-V decorations pay exactly that `11` complement.

## 203. The uncovered `11` population is exactly the T-neighbor set

Fix a witness `r`.  By (623), every endpoint used by `M_V(r)` lies in
`N_A(r) setminus N_T(r)`.  Therefore no T-neighbor is removed by the realized
V matching, and the uncovered endpoint population splits canonically as

```text
N_T(r)
  disjoint union
((N_A(r) setminus N_T(r)) setminus W_r).              (625)
```

The first set is the entire `11` sector and has even cardinality
`deg_T(r)`; the second is the residual `00` sector and is also even by
(611).  Thus a typed completion pairs these two sets separately.  Pairing
choices inside either sector do not affect the additive total (609).

In the Baer cut-potential branch, the scalar price of the `11` complement is
the endpoint sum

```text
Lambda_T(r):=sum_(y in N_T(r)) lambda(y).              (626)
```

Equivalently, under any owner-adapted pairing of `N_T(r)`, it is the sum of
the broken-pair prices `1+mu` from (73rnz_cjibkr).  This is independent of
that pairing by (609).

The `00` complement needs no new internal price law.  On the full non-T
population, the canonical `iota_r` pairing has zero price edgewise, so

```text
sum_(y in N_A(r) setminus N_T(r)) lambda(y)=0.         (627)
```

Consequently the endpoint sum on the residual `00` complement equals the
endpoint sum already used by `M_V(r)`; the two cancel when the actual V
matching and its complement are combined.

Thus (612) has only one genuinely new scalar term, `Lambda_T(r)`.  The final
local price attachment is exactly

```text
audited H/S payment at r = Lambda_T(r),                (628)
```

with the V contribution removed by (627) and the previously proved boundary
transports.  Equation (628) is a target, not yet an identity.  It states the
remaining additive interface on a canonical endpoint population, with all
completion and pairing choices eliminated.

## 204. The global complement price is `lambda^T T a`

Let `a(r)` be the parity with which a root or port witness `r` occurs in the
SRP sum under consideration (one dart cycle, one owner row, or the full sum
in (296)).  Summing (626) with these multiplicities gives

```text
sum_r a(r)Lambda_T(r)
 =sum_r a(r) sum_y T_(r,y)lambda(y)
 =a^T T lambda
 =lambda^T T a.                                      (629)
```

Thus the canonical `11` complement has no residual pairing data at all; its
total price is one bilinear evaluation of the witness-cover vector against
the triangle-free edge graph.

Since every T-degree is even,

```text
T 1=0.                                                (630)
```

Consequently a uniform witness cover `a=1` has zero total complement price.
More generally, (629) vanishes for every Baer potential `lambda` whenever
`a in ker T`.

No claim is made here that the witness multiplicity vector of one dart cycle
is uniform or lies in `ker T`.  The original target (296), however, sums over
all owner colors and all dart cycles, so it is enough to prove the weaker
global cover statement

```text
a_total in ker T,                                     (631)
```

where `a_total` retains the exact root/port occurrence multiplicities of
that full sum.  Equations (629)--(631) reduce the remaining additive price
identity (628) to a cover calculation in the already constructed dart-cycle
decomposition.  If `a_total=1`, Eulerianity closes it immediately; if not,
`T a_total` is the precise residual vector requiring H/S boundary transport.

## 205. The aggregate witness cover lies in `ker T`

For one ordered component pair `c!=e`, the dart set `D_ce` contains the two
`e`-ports at every root `x in c`, paired into one R-edge, and the two
`c`-roots at every port `p in e`, paired into one P-edge.  Across all cycles
of `D_ce`, every vertex of `c` therefore occurs exactly once as a root
witness and every vertex of `e` exactly once as a port witness.  Hence its
witness vector is

```text
a_ce=1_c+1_e.                                         (632)
```

Fix `c` as in the directed target (296) and sum over all `e!=c`.  If the
defect graph has `k` components, then

```text
a_total=(k-1)1_c+sum_(e!=c)1_e.                       (633)
```

In particular `a_total` is constant on every connected component of `D`.
Since `T=A cap D` is a subgraph of `D`, all T-neighbors of a vertex lie in
the same defect component.  Every T-degree is even, so for any vector `a`
constant on D-components,

```text
(Ta)(v)=a(component(v)) deg_T(v)=0.                   (634)
```

Applying (634) to (633) proves the cover condition (631):

```text
T a_total=0,
sum_(e!=c) sum_(witnesses r in D_ce) Lambda_T(r)=0.   (635)
```

Thus the additive Baer endpoint price of the entire `11` complement cancels
for the exact aggregate used by (296), with no assumption on the parity of
the number of defect components.

This is not yet the SRP contradiction.  It also exposes the limit of the
cross-lane additive potential: after the full directed-row sum its endpoint
price is identically zero.  To deduce the marked H parity one must still
prove the occurrence-level price identification (628), equating the realized
H/S payment with this vanishing complement.  Equations (632)--(635) close
the cover side of that identity; they do not prove its H/S side.

## 206. Internal T-neighbors cannot attach through V labels

The same containment used in (634) exposes the coordinate map that remains
to be built.  If `r` lies in defect component `c`, then

```text
N_T(r) subset c,                                      (636)
```

because `T subset D`.  By contrast, a resolved V label at `r` is an
intermediate vertex in an exterior component `d` of a rooted triangle, with
`d` distinct from the root/port components in the SRP block.  Therefore the
attachment cannot be the identity map on V route labels.

The perfect-matching complement introduced in Sections 198--203 is an
**auxiliary Baer completion**, not yet a proved decomposition of the realized
H/S occurrences.  Its right side in (628) is a sum over internal T-neighbors,
so its left side must be manufactured from the H/S owner and port
decorations.  The global vanishing (635) cannot imply marked parity before
that map is constructed.

There is one concrete candidate already present in the H alphabet.  An H
dart at root `x` retains the horizontal owner edge labelled by its port; its
opposite root `x'` lies in the same defect component and satisfies
`A(x,x')=1`.  But membership in one connected component of `D` does not imply
the edge `xx'` itself belongs to `D`.  Therefore the exact additional
checkpoint is

```text
D(x,x')=1  iff  x' in N_T(x).                         (637)
```

No current lemma says that every horizontal owner edge passes this
checkpoint.  Thus H owner mates, not V route labels, are the only immediate
candidate endpoint type for (628), but first their T-subfamily must be
identified.  One must then prove the coverage statement: as the owner color
and dart cycles vary, do those T-marked H mates enumerate every `N_T(x)`
endpoint with the multiplicity required by `Lambda_T(x)`?  Port witnesses
and S switches require the analogous audit.

Sections 197--205 prove that, **if** this H/S-to-complement attachment exists,
all of its completion, T-word, pairing, and cover gauges cancel.  The live
choices are consequently exact:

```text
(a) isolate the T-marked H-owner mates by (637), prove their coverage,
    construct the port/S companion, and verify (628); or
(b) abandon the Baer complement as a direct SRP price and prove scalar
    H/S cancellation inside the full state cycle by another invariant. (638)
```

Any cross-lane use of the active-residual census must meet the same test: it
must provide the occurrence correspondence in (a), not merely an equal
aggregate parity.

## 207. The natural H and S mates are also outside `T`

The checkpoint (637) can be evaluated directly for the mate carried by an H
dart.  A horizontal owner edge `xx' in A_c` is labelled by its port `p`,
meaning `p` is adjacent to both roots.  Therefore

```text
x--p--x'--x
```

is an actual triangle containing `xx'`.  Since `T` is the triangle-free
edge graph,

```text
xx' notin T.                                           (639)
```

Thus the opposite root retained by the H decoration never supplies an
endpoint of `N_T(x)`.

The same argument applies to the immediate S mate.  An S state at root `x`
is the `A_e` fiber switch joining its two ports `p,p'`; both ports are
adjacent to `x`, so the switch edge lies in the triangle

```text
p--x--p'--p
```

and hence

```text
pp' notin T.                                           (640)
```

Therefore none of the three direct occurrence labels supplies the internal
T-neighbor population: V label legs are non-T by (623), H owner mates by
(639), and S switch mates by (640).

This rules out the direct version of branch (638a).  Any proof of (628) must
use a genuinely secondary incidence construction (for example, a broken-T
endpoint attached through a matching atom), not the visible mate edge of an
H, V, or S decoration.  Absent such a construction, the additive Baer
completion remains globally cancelling auxiliary data and branch (638b) is
the honest SRP route.

## 208. Visible H/S pairs have zero additive Baer price

The triangles in Section 207 identify the visible mate pairs with the
canonical partial Baer involutions.  For an H--H port pair labelled by `p`,
the two roots `x,x'` are adjacent to `p` and to each other.  C4-freeness
makes their common-neighbor triangle unique, so

```text
iota_p(x)=x',       iota_p(x')=x.                     (641)
```

Likewise, for an S--S root switch at `x` joining ports `p,p'`,

```text
iota_x(p)=p',       iota_x(p')=p.                     (642)
```

Both are canonical `00` edges of the paired-star graph.  In the additive
cut-potential branch, (73rnz_cjibkr) therefore gives

```text
lambda(x)+lambda(x')=0,
lambda(p)+lambda(p')=0.                               (643)
```

Thus the visible H and S mate occurrences have zero additive Baer price
edgewise.  In particular, a marked H--H port pair contributes one to
`omega_M` but zero to (643).  The endpoint potential cannot distinguish that
marked occurrence from an unmarked canonical triangle pair.

This proves that (628) cannot mean direct equality between the marked H/S
grading and the pure `lambda`-pair prices.  Any valid attachment must add at
least the affine constant channel of Section 166 or a nonlinear/private
decoration retained by the activation ledger.  The endpoint potential alone
is exhausted as a direct SRP invariant: it removes pairing gauges but carries
no marked-H unit.

## 209. The affine constant channel can carry the marked unit

The complete gauge-independent pair form from Section 166 is affine rather
than purely potential:

```text
w(a,b)=lambda(a)+lambda(b)+c.                         (644)
```

On a canonical H or S mate pair, (643) reduces this to `w=c`.  Thus choosing
`c=1` supplies exactly the unit missing from a marked H--H pair.

This constant does not spoil scalar perfect-matching invariance.  For a
perfect matching `M` of a q-point star,

```text
sum_({a,b} in M) w(a,b)
 =sum_(a in U)lambda(a)+c(q/2)
 =sum_(a in U)lambda(a),                              (645)
```

because `8 divides q`, so `q/2` is even.  The constant channel is invisible
on the full star but can remain visible on the selected H submatching.

A uniform `c=1` on every realized pair is not the answer: it would also
charge S and V pairs.  The exact remaining scalar datum is therefore a
**decoration-dependent affine constant**

```text
c_H=1,       c_S and c_V chosen so that the full
H/V/S matching has zero total constant price.         (646)
```

Equation (646) is a target.  It reframes the H/S side of (628) more sharply:
the endpoint-potential and completion parts already cancel, so the marked
grading lives entirely in the constant/type channel.  The H/V/S marginal
identities (339), (343), and the canonical transfer chains are precisely the
available constraints on that type-dependent constant.  Nonlinear activity
states are needed only if those constraints cannot determine `c_S,c_V`.

The affine normal form in Section 166 was proved for its R/P interval
endpoint alphabet.  Applying a decoration-dependent version to the H/S/V
star alphabet is itself part of target (646), not an already justified
extension of that theorem.

## 210. Coarse decoration constants cannot isolate marked H parity

Write the mod-two root-pair counts as

```text
r_HH,r_HV,r_VV,r_SS
```

and the port-pair counts as

```text
p_HH,p_VV,p_SV,p_SS.
```

Equality of the one-dart H marginals gives

```text
2r_HH+r_HV=2p_HH,        hence r_HV=0.                (647)
```

Equality of the S marginals gives

```text
2r_SS=2p_SS+p_SV,        hence p_SV=0.                (648)
```

The V marginal repeats `r_HV=p_SV`, and equality of the total numbers of
root and port pairs leaves only

```text
r_HH+r_VV+r_SS=p_HH+p_VV+p_SS.                        (649)
```

These equations do not determine `p_HH=omega_M`.  Algebraically, toggling
`p_HH` and `p_VV` together preserves (647)--(649) and every one-dart type
marginal while changing the marked parity.

Thus no invariant depending only on the coarse H/S/V pair types, including
an unconstrained choice of constants `c_H,c_S,c_V`, can isolate the marked
H count from the marginal identities alone.  The constant channel in
Section 209 is a genuine location for the unit, but closing it requires the
resolved route labels, owner states, or nonlinear activity features.  This
recovers at the final interface the symmetric blind spot already identified
in Sections 10 and 112.

## 211. Full H/S occurrences embed in the Baer endpoint-state alphabet

Restrict to the configuration where the Baer two-pole state and its endpoint
subtypes are defined.  The visible H and S triangles from Section 208 give a
literal map into the full flip/endpoint alphabet `xi` of
(73rnz_cjibkt), even though their additive price is zero.

For an H--H port pair at port `p` with roots `x,x'`, retain

```text
Xi_H=(x,x', witness p, T-word 00,
      b-word, endpoint subtypes, component roles c,c,e). (650)
```

For an S--S root switch at root `x` with ports `p,p'`, retain

```text
Xi_S=(p,p', witness x, T-word 00,
      b-word, endpoint subtypes, component roles e,e,c). (651)
```

The `00` assertions are (639)--(640).  The full SRP edge state (577) retains
the same two endpoints, common witness, decorations, activity data, and
component roles, so (650)--(651) lose no occurrence identity.  C4-freeness
makes the common witness private.  Moreover the ordered component roles
distinguish H from S even after forgetting the coarse decoration symbol.

The Baer flip state `xi` is defined only when the b-word is mixed.  Thus if
the endpoints in (650) or (651) have word `10` or `01`, orient from `b=1` to
`b=0`; the occurrence is literally a private terminal flip state.  On that
flip subfamily, the Baer terminal classification applies conditionally and
exhaustively: a special-leaf endpoint gives an audited owner cell, while an
owner-free occurrence belongs to the odd-holonomy or additive fixed-margin
alternatives of (73rnz_cjibkzl).  The surviving affine bit is attached to a
full private state `(Xi_H or Xi_S)`, not merely to the coarse letter H or S.

If the b-word is `00` or `11`, the occurrence is not in `delta_P(B)` and
does not belong to `xi`; (73rnz_cjibkzl) cannot be applied.  It remains in
the same-side silent/private sector classified on the Baer lane.  This split
is essential: component roles and endpoint subtypes do not replace the
activation coordinate.

This embedding does not identify the affine-bit value and does not extend
the two-pole endpoint subtypes to an arbitrary SRP block.  Its rigorous gain
is narrower: on the shared configuration, the private coordinate map needed
after Section 210 exists occurrence-by-occurrence on the flip subfamily.  The
final finite problem splits into the fixed-margin/owner states there and the
same-side sector for the remaining occurrences; both must have zero total
marked-H charge.

## 212. The safe private terminal is a switch-relation quotient

Let `Sigma` be the private endpoint-occurrence alphabet on the shared
configuration, retaining all fields in (650)--(651), including actual
endpoint and witness identities, and let `E_Sigma` be the `F_2` vector space
on realizable unordered private pairs.  It is finite for each graph; no
uniform bound in `q` is asserted.  For every
realizable four-endpoint switch include the relation

```text
[a,b]+[c,d]+[a,c]+[b,d].                              (652)
```

Let `Q_switch` be the span of these relations.  The pairing-independent
private census lives canonically in the finite quotient

```text
H_private:=E_Sigma/Q_switch.                           (653)
```

This quotient gives the exact dichotomy needed by both lanes.  If the marked
price is nonzero on one generator (652), that switch is a localized odd
holonomy.  If it annihilates `Q_switch`, it descends to a linear functional
on `H_private`, and the remaining theorem is equality of the source and
terminal classes in that quotient.

One must not replace (653) automatically by endpoint potentials plus one
constant for each connected realizability fiber.  Connectedness of the
allowed-pair graph does not imply that its cycle space is generated by
realizable quadrilaterals; a connected six-cycle with no allowed four-switch
already leaves an additional holonomy class.  An affine representation

```text
w(a,b)=phi(a)+phi(b)+c_C                              (654)
```

is valid only after proving that, in each fiber, the switch relations generate
the full non-cut cycle space (or an equivalent kernel theorem).

Thus (653), not (654), is the unconditional per-graph finite terminal.  It retains
exactly the private information demanded by Section 210 and by the B3
seven-coordinate census: endpoint occurrences and realizable pair classes,
with no collapse to H/S/V types and no unproved affine normal form.

## 213. The affine-generation question is one finite rank test

For one private realizability fiber, let `G_Sigma=(V,E)` be its allowed-pair
multigraph and let

```text
partial:F_2^E -> F_2^V
```

be the incidence map.  Differences of two realizable perfect matchings have
zero boundary and even edge cardinality.  Define their actual span by

```text
D_match:=span{1_M+1_(M'): M,M' realizable perfect
         matchings in the same fiber},
Z_even:=ker(partial) cap ker(1_E^T).                   (655)
```

Then `D_match subseteq Z_even`.  Equality need not hold in an arbitrary
allowed-pair graph: an even cycle need not extend to two perfect matchings of
the fiber.  Every realizable four-switch vector (652) belongs to `D_match`.
If `Q` is the matrix whose rows are those switch vectors, then the exact
switch-generation lemma is

```text
rank(Q)=dim D_match.                                   (656)
```

Both sides of (656) are reproducible by enumerating the finite matchings and
switches of the occurrence fiber.  The cheaper equality
`rank(Q)=dim Z_even` is a sufficient test, and becomes equivalent only after
proving `D_match=Z_even`, for example by a matching-extension theorem.

A uniform constant edge cochain annihilates `Z_even` even when it is not a
graph cut, and

```text
ann(Z_even)=cut space + span{1_E}.                     (657)
```

Consequently the sufficient test `rank(Q)=dim Z_even` implies precisely the
affine form (654), with no missing cycle classes.  The exact test (656) gives
all realizable pairing invariance, but by itself need not force an affine
endpoint form when `D_match` is a proper subspace of `Z_even`; the extra
annihilator records pair states no realizable matching exchange can compare.

The ambient dimension needed for the sufficient test is elementary.  If

```text
beta=|E|-|V|+number_of_components(G_Sigma),
```

then

```text
dim Z_even = beta      if every graph cycle is even,
dim Z_even = beta-1    if an odd graph cycle exists.   (658)
```

The exact switch-generation defect is

```text
h_match:=dim D_match-rank(Q).                          (659)
```

It is the number of matching-exchange directions missed by the realized
four-switches.  The larger computable number
`h_ambient:=dim Z_even-rank(Q)` also contains the extension defect
`dim Z_even-dim D_match`; it must not be called realized pairing holonomy
without proving extension.  Equations (655)--(659) turn the disputed switch
generation step into a reproducible finite linear-algebra audit on the
private occurrence table; no informal connectedness or cycle-extension
argument is needed.

## 214. Local switch generation leaves one cross-witness cochain equality

The Baer generation theorem (73rnz_cjibkzo) now proves the stronger ambient
test on every variable owner-free witness fiber: after the canonical `00`
and prescribed owner pairs are removed, the remaining allowed graph is a
complete graph on an even endpoint set, and its realizable quadrilaterals
span `Z_even`.  Thus the local defects in (659) vanish there.  This does not
yet identify affine data belonging to different witnesses.

The remaining transport has an exact cochain form.  Let `z_P` be the edge
census of the witness-label multigraph `W_P` from (73rnz_cjibkzj), let
`partial_W` be its vertex--edge incidence map, and let `1_R` indicate the
residual witnesses.  Equation (73rnz_cjibkzk) is precisely

```text
Delta=<partial_W^*(1_R),z_P>.                          (660)
```

In other words, the Baer residual price is the literal cut cochain: a routed
segment has price one exactly when its two witness labels lie on opposite
sides of `R`.  Local complete-graph generation removes pairing holonomy
inside each star, but it cannot by itself prove (660) equals the SRP marked-H
price, because that comparison changes witness fibers.

Transport the H/S occurrence map (650)--(651), the audited owner-cell prices,
and the same-side sector to the same routed-segment space.  Denote the
resulting marked cochain by `tau_H`; this notation is a target and presumes no
value for an untransported occurrence.  The final cross-lane statement is
exactly

```text
<tau_H,z_P>=<partial_W^*(1_R),z_P>                     (661)
```

for the realized global census, after the owner-cell corrections.  More
canonically, if `Q_route` is the span of all realized segment switches and
both prices annihilate it, they descend to functionals `bar(tau_H)` and
`bar(tau_R)` on `H_route:=E_route/Q_route`, where
`tau_R=partial_W^*(1_R)`.  It is enough to prove

```text
<bar(tau_H)+bar(tau_R),[z_P]>=0 in F_2.                (662)
```

Failure of either price to annihilate a generator of `Q_route` is the already
localized odd-holonomy branch.  If both descend but (662) fails, the realized
class `[z_P]` identifies the exact additional private transport coordinate;
it must not be hidden by a coarse H/S/V marginal.

Thus (73rnz_cjibkzo) closes the **within-witness** generation question.  The
unproved theorem is now only the **cross-witness** equality (661), including
the same-side `b=00/11` occurrences excluded from `xi`.  This separation
prevents the local rank result from being mistaken for the global marked
parity cancellation.

## 215. The marked flip cochain on `W_P` is canonical

The provisional `tau_H` in Section 214 can be constructed on the flip
subfamily without any further routing theorem.  An edge `s` of `W_P` is not
an anonymous pair of witness labels: by construction it retains the two
particular flip edges `e,e'` of `delta_P(B)` paired consecutively on an
Eulerian circuit of `P`.  Write `y(e),y(e')` for their private witness labels
and define

```text
h(e)=1  iff e is the canonical P-edge supplied by a marked
             H--H port occurrence from (650),
tau_H^flip(s):=h(e)+h(e').                            (663)
```

Every flip edge occurs in exactly one routed segment.  Therefore (663) gives
the identity

```text
<tau_H^flip,z_P>
 = number of marked H occurrences with mixed b-word.  (664)
```

This is independent of how the flip edges were paired: changing the pairing
changes the individual segment prices but not their total.  No S or V edge
is charged, because the full occurrence decoration is retained.

Let `omega_same` be the number modulo two of marked H occurrences whose
b-word is `00` or `11`.  Sections 208 and 211 identify every H occurrence
with its canonical P-edge and partition them exhaustively by their b-word,
so

```text
omega_M=omega_same+<tau_H^flip,z_P>.                  (665)
```

On the same routed edge `s={e,e'}`, the residual-cut price from (660) is

```text
tau_R(s)=1_R(y(e))+1_R(y(e')).                        (666)
```

Combining (660), (665), and (666) turns the desired comparison into one
literal discrepancy ledger:

```text
omega_M+Delta
 =omega_same
  +sum_(s={e,e'} in z_P)
     (h(e)+h(e')+1_R(y(e))+1_R(y(e'))).               (667)
```

Thus the flip transport map itself is no longer missing.  What remains is
to prove the right side of (667) vanishes after inserting the audited owner
cells.  Equivalently, the endpoint classification must pair each residual
witness incidence with a marked-H flip incidence, with `omega_same` as the
only external correction.  A failure is now localized either to one routed
segment cell in the parenthesis or to one same-side private occurrence; it
cannot be attributed to a choice of Eulerian pairing or to an undefined
cross-witness cochain.

## 216. A same-side H edge is not automatically a `rho^tri` atom

The existing Baer classification suggests attaching `omega_same` through
the same-side `rho^tri` channel of (73rnz_cjibku)--(73rnz_cjibkx).  The two
objects share genuine geometry: both are canonical `00` P-edges with a
unique triangle witness.  That agreement is not yet an occurrence map.

For the H occurrence (650), write its canonical edge as `xx'` with witness
`p`.  To be a particular residual cross-matching atom
`rho^tri_(E_i,G)`, it must additionally admit the ordered four-step route

```text
E_i--x--x'--G   or   E_i--x'--x--G,                  (668)
```

where `E_i` is one of the two specified empty poles, `G` is a specified
residual full center, and the middle edge survives the switch removal used
to define `rho`.  Equivalently, one endpoint must lie in `N_A(E_i)`, the
other in `N_A(G)`, with the owner and residual labels retained.

The H state (650) supplies `x,x',p`, their canonical-00/T-word data,
endpoint subtypes, and component roles.  It does not by itself supply either
adjacency in (668), a residual center `G`, or a pole choice `E_i`.
C4-freeness makes `p` unique but cannot manufacture those two exterior
neighbors.  Hence

```text
same-side marked H canonical edge
   does not presently imply a rho^tri occurrence.     (669)
```

This is a typing obstruction, not a claim that the attachment is false in a
realized two-pole block.  A positive bridge must prove the **route extension
lemma** (668), including multiplicity and owner compatibility, for the
relevant H occurrences.  If extension fails for an occurrence, its private
state must remain as an additional same-side coordinate in (667).  Merely
identifying both edges as canonical `00` P-edges would repeat the
aggregate-versus-occurrence error excluded in Sections 206 and 211.

Thus the same-side test has a definite outcome with the current lemmas: the
`rho^tri` classification is a valid target container, but no literal map has
yet been proved.  The next graph-facing statement is (668), not another
parity identity on the already aggregated `rho^same` count.

## 217. Anchor incidence removes the unnecessary uniqueness demand

For parity transport, a same-side H edge need not choose a unique shore
anchor.  For a marked occurrence `e=(xx';p)`, let `A(e)` be the set of all
ordered tuples `(i,G,orientation)` satisfying (668), and define the two
owner-resolved anchor parities

```text
alpha_i(e):=# {anchors in A(e) with pole E_i} mod 2,
alpha(e):=alpha_1(e)+alpha_2(e).                       (670)
```

Every element of `A(e)` is literally one occurrence of the middle edge in
`rho^tri_(E_i,G)`.  Conversely, every `rho^tri` occurrence whose middle edge
is the marked H edge `e` supplies exactly one such ordered anchor.  Therefore
double counting the incidence set gives, separately by owner,

```text
sum_(same-side marked H e) alpha_i(e)
 = number of H-tagged same-side rho^tri atoms owned by E_i. (671)
```

This identity is canonical even if an H edge has zero, two, or more shore
extensions; no arbitrary choice or unique-anchor theorem is needed.  Its
scalar price of dropping uniqueness is the explicit residual character

```text
u(e):=h(e)+alpha(e),                                  (672)
```

Summing (672) says exactly that the scalar same-side marked census equals its
anchored `rho^tri` census plus `sum_e u(e)`.  Thus a unique-anchor theorem is
one sufficient way to kill `u`, but it is stronger than necessary.  The
exact scalar remaining statement is only

```text
sum_(same-side marked H e) u(e)=0
after the audited owner corrections.                   (673)
```

At owner-vector resolution, (671) already provides the canonical vector
`(sum_e alpha_1(e),sum_e alpha_2(e))`.  Comparing the scalar H mark with its
two coordinates requires the separate pole-owner lift demanded by
(73rnz_cjibkd); no pole label on `h(e)` is asserted here.

Equations (670)--(673) implement the alternative suggested after (669):
extend the private quotient by the actual shore-anchor incidence rather than
selecting one anchor.  They absorb every anchored occurrence, with correct
multiplicity, into the existing `rho^same -> delta_G -> Delta` chain.  Any
surviving obstruction is now supported precisely on the mod-two mismatch
between marked H ownership and anchor multiplicity, not on nonuniqueness
itself.

## 218. Anchor parity is a two-bit endpoint determinant

The residual character `u` has a closed graph-facing formula.  For any
vertex `v`, put

```text
ell_i(v):=1[E_i v in A],
ell(v):=ell_1(v)+ell_2(v),
r(v):=|N_A(v) intersect R| mod 2.                     (674)
```

For an H edge `e=xx'`, choosing an `E_i`-anchor means choosing one
orientation in which the first endpoint is adjacent to `E_i` and then one
residual center adjacent to the other endpoint.  The two orientations are
disjoint as ordered anchor incidences, so (670) becomes

```text
alpha_i(xx')=ell_i(x)r(x')+ell_i(x')r(x),
alpha(xx') =ell(x)r(x') +ell(x')r(x).                 (675)
```

Equivalently, if `a(v)=(ell(v),r(v)) in F_2^2`, then

```text
alpha(xx')=det(a(x),a(x')).                           (676)
```

This derivation counts anchor tuples with their actual multiplicity; it does
not assume that the neighbor in `R` is unique.  The survival clause in (668)
is automatic for H mates: removed leaf-switch middle edges lie in `T`, while
`xx'` lies outside `T` by (639).

Thus the scalar same-side residue in (673) is explicitly

```text
sum_(same-side marked H edge xx')
  (1+ell(x)r(x')+ell(x')r(x)).                        (677)
```

The unique-anchor problem has therefore been replaced by a bilinear
endpoint census.  Proving (673) now requires showing that the marked
same-side H edge census has total determinant equal to its cardinality.  It
is a subgraph of the horizontal owner two-factor, not a matching on root
vertices; a root may meet two H edges.  This
is not implied by the separate `ell` and `r` marginals, but it is expressed
in exactly the two-shore commutator alphabet already present in
(73rnz_cjibky)--(73rnz_cjibkza), so those identities can be tested against
(677) without constructing any new anchor choices.

## 219. The anchor defect has a four-state endpoint table

There are only four scalar shore states

```text
a(v) in {00,10,01,11}                                  (678)
```

from (674).  Over `F_2`, two vectors in `F_2^2` have determinant one exactly
when they are distinct and both nonzero.  Hence the contribution
`1+det(a(x),a(x'))` in (677) is zero precisely for

```text
{a(x),a(x')} in {{10,01},{10,11},{01,11}}.            (679)
```

The anchor defect is supported exactly on the complementary cells:

```text
at least one endpoint has state 00; or
the two endpoint shore states are equal.              (680)
```

Thus multiple shore anchors cause no uncontrolled case split.  Their parity
has already collapsed to (678), and every marked same-side H edge in one of
the three cells (679) is paid pointwise by an odd number of `rho^tri`
anchors.  The remaining statement (673) is the evenness, after owner
correction, of the marked H population in the seven unordered cells (680).

This is the smallest scalar table available: the separate one-dart
`ell/r` marginals do not determine the equal-state cells, just as the coarse
H/V/S marginals failed in Section 210.  A successful proof must use either
the horizontal-owner two-factor relation on these four shore states or the
owner-resolved commutator in (73rnz_cjibky)--(73rnz_cjibkza); no additional
anchor enumeration is required.

## 220. Only four diagonal pair cells survive the endpoint margins

Let `m_(uv)` be the parity of marked same-side H edges whose unordered shore
states are `{u,v}`, for `u,v in {00,10,01,11}`, and let `n_00` be the parity
of their endpoints having state `00`.  Since a `00--00` edge contributes two
such endpoints,

```text
n_00=m_(00,10)+m_(00,01)+m_(00,11).                  (681)
```

The defect table (680) therefore has total parity

```text
sum_e u(e)
 =n_00+m_(00,00)+m_(10,10)+m_(01,01)+m_(11,11).      (682)
```

Thus the three off-diagonal cells incident with `00` are not new pair data:
their sum is the ordinary one-endpoint margin `n_00`.  After that margin is
transported, the genuinely nonlinear same-side obstruction consists only of
four equal-state edge parities.

Equation (682) is sharp at this resolution.  Separate endpoint margins
cannot determine the diagonal edge counts: an abstract toggle of two
equal-state edge cells against two cross-state edge cells can preserve every
endpoint population.  Realizability of that toggle in the owner two-factor
is a separate graph question.  The
remaining graph theorem may therefore be stated minimally as an evaluation
of the equal-shore-state H edges, with `n_00` supplied by the existing
one-dart owner ledger and their incidence pattern retained in the horizontal
owner two-factor.  No seven-cell enumeration is necessary.

## 221. Diagonal cells are odd monochromatic shore runs

The marked H edge census is not a matching on its root vertices.  For fixed
`(c,e)` it is the horizontal owner subgraph
`K_ce=A_c intersect F_e[c]`, of maximum degree two; an interior root of an
H-run meets two marked edges.  Thus matching class-size formulas cannot be
used to evaluate (682).

For each shore state `u in {00,10,01,11}`, let `K_u` contain the marked
same-side H edges whose two endpoints both have state `u`.  Every component
of `K_u` is a path or a cycle.  Therefore

```text
m_(u,u)
 = number of odd-edge paths and odd-edge cycles in K_u mod 2. (683)
```

The endpoints of the path components are precisely the incidences where a
maximal `u`-run stops because the next horizontal owner edge is absent or
has a different shore state.  Handshake pairs these endpoints, but—as in
the original owner-run identity (54)—does not determine the parity of the
distance between them, and an odd closed `u`-cycle has no endpoints at all.

Combining (682) and (683), the same-side anchor theorem is exactly the
owner-corrected evenness of

```text
n_00 + sum_(u in F_2^2)
  #(odd-edge path/cycle components of K_u).            (684)
```

This is the correct use of the horizontal two-factor.  It localizes every
remaining diagonal unit to an odd monochromatic shore run, while showing why
endpoint populations alone cannot pay it.  A closing identity must use the
vertical triangle connections of the root--color state two-factor, or an
equivalent H-tagged owner route, to pair the odd runs and odd closed cycles.
No inference from a nonexistent global H matching is valid.

## 222. The final anchor defect is owner-vector valued, not the scalar determinant

Sections 218--221 deliberately analyze the scalar sum
`alpha=alpha_1+alpha_2`.  That sum is a useful selector diagnostic, but it
cannot be the final owner transport: it annihilates the diagonal class
`(1,1)` which (73rnz_cjibkzd) and (73rnz_cjibkd) must preserve.

A marked H unit is scalar before the pole choice, so at the owner interface
it must be compared with both pole characters, i.e. with the diagonal vector
`(1,1)`.  The exact owner-resolved defect of a marked same-side edge is

```text
u_vec(e):=(1+alpha_1(e),1+alpha_2(e)).                 (685)
```

Thus `1+det=1+alpha_1+alpha_2` from (677) is neither coordinate of (685)
nor their sum (whose two constant units cancel).  Equations (677)--(684)
remain correct scalar identities and locate selector/run holonomy, but they
do not by themselves prove the required diagonal owner conservation.

C4-freeness sharpens (685).  The two roots of an H edge already share their
port witness, so they cannot both be adjacent to the same pole or to the
same residual center.  Applying the ownerwise anchor formula (670) gives on
the four equal scalar shore-state cells

```text
state cell     (alpha_1,alpha_2)       u_vec
00--00         (0,0)                   (1,1)
10--10         (0,0)                   (1,1)
11--11         (1,1)                   (0,0)
01--01         (0,0)                   (1,1).          (686)
```

For `11--11`, odd pole parity makes each root meet exactly one pole and the
shared-witness C4 exclusion forces the poles to be different; odd residual
parity then gives one anchor for each owner.  For `01--01`, pole parity zero
means zero pole neighbors here: `E_1,E_2` are the two inside empty centers,
are D-adjacent in the minority clique, and therefore have A-codegree zero.
Their A-neighborhoods (the empty lines) are disjoint, so no double-pole root
exists.

Consequently the `11--11` diagonal cell is paid pointwise at full owner
resolution even though its scalar determinant is zero.  The genuine
diagonal owner residue is supported only on

```text
00--00, 10--10, and 01--01.                            (687)
```

This owner-vector correction supersedes treating the four diagonal terms of
(682) as equally unresolved.  The remaining theorem is to pair the odd
monochromatic runs in the three classes (687), together with the transported
`n_00` margin and inactive owner cells, against the diagonal source
`(73rnz_cjibkd)`.

## 223. Pole alternation removes closed `10`-run holonomy

Because the empty lines `N_A(E_1),N_A(E_2)` are disjoint, a root with
`ell=1` is adjacent to a unique pole.  If two adjacent H roots were adjacent
to the same pole, they would have that pole and their H-port witness as two
common A-neighbors, contradicting C4-freeness.  Hence on every H edge whose
two endpoint states have `ell=1`, the unique pole labels are different.

In particular, pole labels alternate along every component of `K_10` (and
of `K_11`).  Therefore

```text
every closed 10--10 or 11--11 H cycle has even length; (688)
```

and a `10--10` path has odd length exactly when its two endpoints carry
different pole labels.  Since `11--11` is already pointwise paid by (686),
the live consequence is

```text
m_(10,10)
 = number of K_10 path components whose endpoint
   pole labels are different mod 2.                   (689)
```

Thus the `10` diagonal defect has no closed-cycle holonomy.  It is an
owner-visible boundary term: every odd unit is carried by a path from the
`E_1` empty line to the `E_2` empty line.  The remaining owner transport may
attach those two endpoints to the vertical triangle edges of the root--color
state graph; it need not price an internal `10` run or enumerate its length.

No analogous two-color alternation follows for `01`: its endpoints have no
pole neighbor and only an odd parity of residual-center neighbors, possibly
more than one.  The unresolved closed-run sector is consequently narrowed
to `00` and `01`, while `10` is reduced to a two-pole boundary path and `11`
is already paid.

## 224. Every `01--01` unit lifts canonically to double-residual flags

The state `01` asserts only that a root has an odd number of neighbors in
`R`; the shared H state does not place the root in the ordinary occupied
shore where a replication-two bound would make that neighbor unique.  Thus
one must retain the full residual-neighbor incidence rather than select one
center.

For an H edge `e=xx'` in `K_01`, let

```text
R_x=N_A(x) intersect R,       R_(x')=N_A(x') intersect R.
```

Both sets have odd size.  They are disjoint: a residual center adjacent to
both roots would join their H-port witness as a second common A-neighbor,
contradicting C4-freeness.  For each unordered pair of distinct residual
centers `{G,H}`, define the private double-label flag

```text
beta_(G,H)(e)
 :=1[(G in R_x and H in R_(x')) or
     (H in R_x and G in R_(x'))].                     (690)
```

Disjointness makes the two alternatives exclusive.  Double counting the
Cartesian product gives the pointwise identity

```text
sum_({G,H} subset R) beta_(G,H)(e)
 =|R_x| |R_(x')|=1 mod 2.                             (691)
```

Hence every `01--01` marked unit has a canonical odd expansion into private
flags carrying two distinct residual labels.  This removes the need for a
unique residual-center label and is the exact analogue of the all-anchor
incidence construction (670).  It also matches the double-labelled flag
terminal independently isolated in the B3 lane: scalar or single-label
marginals cannot retain the required interaction.

Equation (691) is an occurrence map, not yet a cancellation theorem.  At
owner resolution the marked unit is still duplicated as `(1,1)`, so each
double-residual flag must enter the owner-route quotient with that diagonal
tag (or be paired there).  The gain is exact: `01` no longer contributes an
anonymous odd run length; its every edge unit is represented by a bounded-
arity joint label.  After the `10` boundary reduction and the pointwise
payment of `11`, only the `00` closed-run sector lacks such a nonzero
incidence expansion.

## 225. The fully shore-empty `00` cell cannot be incidence-lifted

For a `00` root, `ell=0` means no pole neighbor because the two empty lines
are disjoint, but `r=0` means only that its residual-neighbor set has even
cardinality; it may have size `0,2,4,...`.  Thus `00` does not mean absence
from the residual alphabet.

There is nevertheless one exact hard subcell.  Let `e=xx'` be a marked
`00--00` H edge with

```text
R_x=R_(x')=empty.                                     (692)
```

Every nonconstant flag built solely from the pole incidences
`ell_i(x),ell_i(x')` and residual incidences
`1[G in R_x],1[G in R_(x')]` vanishes on (692), at every arity.  The marked
H unit is still one.  Consequently no identity of the form

```text
marked unit = sum of positive-degree shore-incidence flags             (693)
```

can hold occurrence-by-occurrence on all `00` edges unless (692) is
geometrically impossible.

This is stronger than the failure of the particular determinant or pair
flag: it is the augmentation obstruction at the zero incidence state.  The
remaining `00` route has an exact fork:

```text
(a) prove every marked 00--00 H edge has a nonempty pole/residual
    incidence and construct an odd expansion there; or
(b) retain a non-shore generator, necessarily the private H-port witness,
    root--color vertical decoration, or V/S route state.                (694)
```

Branch (a) still needs an odd expansion: nonempty even residual sets do not
make the single- or double-label sums odd automatically.  Branch (b) is the
honest interface already indicated by the full state cycle (577).  Thus the
sole unexpanded class has now been localized further to a precise zero-state
obstruction rather than an undifferentiated `00` population.

## 226. The required non-shore generator is already `P_d(p)`

Branch (694b) needs no new alphabet.  For every marked H edge `e=xx'` with
port witness `p`, the full edge state (577) retains

```text
P_d(p)=(N_d(p),(t_y)_(y in N_d(p))).                  (695)
```

The set `N_d(p)` has two labels and pins `p` uniquely: a second port adjacent
to both labels would form a C4, as proved in Sections 181 and 184.  Hence the
one-hot flag

```text
gamma_q(e):=1[P_d(p)=q]                               (696)
```

is private, and for every occurrence, including the fully shore-empty cell
(692),

```text
sum_q gamma_q(e)=1.                                   (697)
```

Thus the augmentation obstruction in Section 225 forces use of a non-shore
coordinate but does not require inventing one: `P_d(p)` is exactly that
coordinate.  At owner resolution the flag carries the diagonal tag `(1,1)`.
It is also already present on the closed root-state flow, so transporting it
does not require an occurrence map from the SRP alphabet to Baer shores.

Reversal fixes the middle port state and exchanges the two root states:

```text
(R_d(x),H,P_d(p),H,R_d(x'))
 <-> (R_d(x'),H,P_d(p),H,R_d(x)).                     (698)
```

The orbit has no fixed member because the two root-label sets are disjoint
and nonempty.  This locates the oriented unit, but it does **not** make even
occupancy of each fully private orbit a justified target: privacy may prevent
a second physical occurrence from carrying the reversed state at all.

This is a strict narrowing of the original target (573): `11` is paid
pointwise, `10` is an opposite-pole boundary, `01` has the double-residual
flag expansion, and `00` has the private `P_d(p)` oriented flag.  The latter
is the only class with no shore-incidence carrier; it is not the only class
whose carrier still needs transport.  Equation (697) locates its unit.  The
still-unproved input is a joint V/S owner-route relation on a quotient coarse
enough to admit cancellation while retaining the marked character.

## 227. Full privacy forbids literal reversal-orbit cancellation

The distinction just made is forced.  The middle state `P_d(p)` pins the
physical port `p`.  At that port the auxiliary port involution has one H--H
pair with the two roots `x,x'`; hence the full data in (698) pin one physical
H occurrence.  A second occurrence with the reversed state would have the
same `P_d(p)`, hence the same port, roots, and physical pair.  It is not a
distinct occurrence in the realized edge census.

Consequently, after choosing an orientation of the dart component,

```text
each realized H edge occupies exactly one member of its
full-private reversal orbit.                           (699)
```

Thus the earlier proposed statement (573), if read literally at the fully
private occurrence resolution of (570)/(577), would imply that there are no
H occurrences, not merely that their total parity is even.  No proved route
identity supplies a second copy of the same private port state, and formal
duplication by reading the same cycle in both directions would make every
orbit even tautologically while destroying the grading identity (572).

This exposes the exact privacy--cancellation tradeoff.  Private labels are
needed to prevent accidental collisions when constructing occurrence maps,
but the final conservation law cannot demand equality occurrence-by-
occurrence at the maximally private resolution.  It must pass to a quotient
that forgets enough identity for distinct route occurrences to pair, while
remaining injective on the marked diagonal character.  Equivalently, one
needs a price functional on the private route quotient, not literal even
occupancy of every orbit.

For the `00` sector, `gamma_q` remains a valid one-hot carrier and (697)
remains exact.  What is withdrawn is only the overstrong orbitwise endpoint.
The rigorous terminal is now: construct a V/S owner-route quotient on the
`P_d`-tagged states, prove the marked `00` price descends, and show its
aggregate value vanishes.  Failure of descent on a realized relation is the
localized holonomy branch already encoded by Sections 212--214.

## 228. All live carriers share one unordered double-label terminal

After the privacy correction, the three unresolved classes still have a
common bounded-arity carrier:

```text
10: each odd run is a path with endpoint labels {E_1,E_2};
01: each unit expands into flags {G,H} with G,H in R, G!=H;
00: each unit carries the two-label port set N_d(p)={y_1,y_2}. (700)
```

Retain with each unordered pair its channel (`pole boundary`, `residual
pair`, or `port-secondary`), diagonal owner tag, endpoint/role subtype, and
the activity bits already present in the originating state.  Let `F_2Flag`
be the free `F_2` space on these full unordered double-label flag types and
let `L_H` be the sum of the carriers in (700), after subtracting the
pointwise-paid `11` cells and audited owner cells.

The augmentation of `L_H` is exactly the remaining marked parity:

```text
aug(L_H)
 = (# odd 10 paths)
   +sum_(01 edges e) sum_({G,H}) beta_(G,H)(e)
   +sum_(00 edges e) sum_q gamma_q(e),                (701)
```

with each inner sum equal to one by (691) or (697).  Thus no scalar unit is
lost in passing to the flag ledger.  The actual label identities are
retained; ``bounded arity'' does not assert a bounded number of types in q.

This is the same terminal shape independently forced by the B3 categorical
audit (12rzh)--(12rzi): unordered double labels plus role/channel data, while
forgetting either label or the role interaction restores feasible
countermodels.  The convergence is structural rather than a claimed map
between the two applications.

The remaining theorem can now be stated once:

```text
the realized simultaneous V/S and owner routes conserve L_H
in the unordered double-label flag quotient.          (702 GAP)
```

If (702) holds, its owner-boundary value is zero and (701) kills the marked
parity.  A relation on which the proposed flag price fails is a localized
joint-label holonomy witness.  What remains to prove is conservation, not
another occurrence expansion: all source units now enter the same arity-two
private ledger.

## 229. The `10` carrier is an exact root-state coboundary

The pole-boundary carrier in (700) can be transported immediately on the
closed state cycle (577).  Enrich each root occurrence by its Baer shore
state and define

```text
chi_10(v):=1[a(v)=10 and E_1 v in A].                 (703)
```

This is canonical because a `10` root meets exactly one pole.  On every
`10--10` H edge `vv'`, pole alternation from Section 223 gives
`chi_10(v)+chi_10(v')=1`.  Since the coboundary of any vertex function sums
to zero on the closed edge census `C_state`, partitioning its edges yields

```text
m_(10,10)
 =sum_(H edge vv' outside K_10) (chi_10(v)+chi_10(v'))
  +sum_(non-H edge vv' in C_state) (chi_10(v)+chi_10(v')). (704)
```

Thus `10` is not an independent diagonal generator in `L_H`: its unit is
exactly transferred to mixed-H boundary transitions and non-H V/S route
transitions of the same realized cycle.  No path pairing or endpoint-
coverage lemma is needed.  The complementary terms retain their physical
root states and diagonal owner tag for the joint quotient.

Equation (704) is a transport identity, not a vanishing statement.  It
updates the GAP (702): after substituting (704), the independent source
carriers are the `01` double-residual flags and `00` port-secondary flags,
together with explicit mixed-H/V/S boundary terms.  Proving their joint
owner-route conservation remains the live theorem.

## 231. B3 antisymmetry does not automatically conserve a directed route cycle

The unordered double-label shape in Section 228 is common to the B3 and SRP
terminals, but their conservation mechanisms differ.  In the B3 residual
selection, the occurrence weights satisfy

```text
x_(t,u)=x_(u,t),
```

so every antisymmetric boundary `F(u,t)=-F(t,u)` cancels pairwise.  The SRP
state ledger instead supplies an oriented closed-cycle flow.  Its transition
counts satisfy equal in- and out-degree at each state, but need not satisfy
edgewise symmetry.

For such a directed circulation, antisymmetry alone is insufficient.  A
directed three-cycle with unit weights and an antisymmetric cochain taking
value one on each forward edge has nonzero total circulation.  Only an exact
vertex coboundary is forced to sum to zero, as used in (704) and (707).

Consequently the B3 identity (12rzh) cannot be imported as a proof of the
GAP (702).  The common flag alphabet is genuine, while automatic
conservation is not.  To close the SRP ledger one must prove one of:

```text
the remaining flag cochain is exact on the realized route graph;
the route census is reversal-symmetric after an allowed coarsening;
or every nonzero circulation yields a localized joint-label holonomy.   (708)
```

This is precisely the quotient/price dichotomy of Sections 212 and 227.
The coboundary transports already proved remove the exact pieces; the
`01` union flags and `00` port-secondary flags represent the possible curl
that remains.

## 230. The `01` pair flags also have an exact coboundary transport

Fix an unordered pair of distinct residual centers `q={G,H}`.  On every root
occurrence define the quadratic incidence flag

```text
chi_q(v):=1[G in R_v and H in R_v].                   (705)
```

For an edge `e=xx'` of `K_01`, the sets `R_x,R_(x')` are disjoint.  Let

```text
U_q(e):=1[G,H both belong to R_x union R_(x')].
```

The pair `{G,H}` lies either twice on one side or once on each side, with
these cases exclusive.  Therefore the private cross flag (690) satisfies

```text
beta_q(e)=U_q(e)+chi_q(x)+chi_q(x').                  (706)
```

Now sum the coboundary of `chi_q` on the full closed state-edge census.  It
vanishes.  Partitioning the edges into `K_01` and its complement gives the
coordinatewise transport identity

```text
sum_(e in K_01) beta_q(e)
 =sum_(e in K_01) U_q(e)
  +sum_(e outside K_01) (chi_q(x_e)+chi_q(x'_e)).     (707)
```

Thus every `01` double-residual coordinate is transported, label pair by
label pair, to an unordered **union flag** on its H edge plus explicit
quadratic boundary terms on complementary H and V/S transitions.  This uses
no unique residual label and no pairing of private occurrences.

Equation (707) does not make the union flags vanish; it changes them from a
cross-endpoint product to a symmetric edge-union incidence, the same
collision form used by the unordered double-label capacity ledger.  Together
with (704), it leaves `00` port flags and the `01` union flags as the two
independent H-edge carriers, with all other terms already on complementary
route transitions.

## 232. The `00` port carrier is an edge chain in the dual owner factor

Fix the root component `c`, port component `e`, and secondary component `d`
of one simultaneous-routing block.  Every port `p in e` has exactly two
`d`-neighbors.  Those two vertices form the edge of the owner-`e` factor on
`d` indexed by their unique common neighbor `p`.  Thus

```text
Phi_(e,d): e -> E(F_e[d]),       p |-> N_d(p)          (709)
```

is a bijection.  Surjectivity is the definition of the exterior owner
factor; injectivity is C4-freeness, since two different ports with the same
two `d`-neighbors would be two common neighbors of that pair.  Both sets
have order `2q`, consistently with `F_e[d]` being two-regular on `2q`
vertices.

Let `M_00` be any selected census of marked `00--00` H ports in this block,
with multiplicity reduced modulo two, and transfer it through (709):

```text
B_00:=sum_(p in M_00) [N_d(p)] in C_1(F_e[d];F_2).     (710)
```

The private two-label coordinate in `P_d(p)` is now literally the unordered
endpoint pair of the corresponding owner-factor edge.  Its chain boundary
is

```text
partial B_00(y)
 =#{p in M_00 : y in N_d(p)} mod 2.                    (711)
```

Hence (711), rather than a root-incidence phase at the two H roots, is the
canonical channel-changing endpoint datum for the `00` carrier.  It is
indexed by the same secondary labels that occur in the V/S interval and
activity ledger.  Identifying that ledger with (711) is still a required
route statement; (709)--(711) only construct the exact interface.

Because `F_e[d]` is a disjoint union of cycles, two edge chains with the same
boundary differ on each factor cycle `C` by either zero or the full cycle.
Toggling the full cycle changes the augmentation of the chain by

```text
|E(C)| mod 2.                                          (712)
```

It follows that the scalar `00` marked parity is determined by the secondary
boundary (711) on every even factor cycle.  The only boundary-invisible
residue capable of changing it is the full edge set of an **odd** cycle of
`F_e[d]`.  Equivalently, the port-secondary part of the GAP (702) splits
canonically into

```text
secondary-label boundary transport
 + odd owner-factor-cycle holonomy.                    (713)
```

This is strictly coarser than the impossible full-private reversal pairing
of Section 227: distinct ports may now interact through their shared
secondary endpoints.  It also respects the obstruction of Section 231.
The boundary term is the part that can be exact after adjoining V/S states;
an odd full owner cycle is the localized curl which no endpoint coboundary
can see.  A closing argument must therefore identify (711) with the realized
V/S boundary and either exclude or separately price the selected odd-cycle
residue.  No same-channel exact-pair cancellation is asserted.

## 233. The active part of the owner-factor boundary is the `q_y` census

The interface in (711) already occurs in the secondary interval ledger.
Let `p` be an H port and let `h_p` be either of its two incidence darts.  If
`y in N_d(p)`, then `y` meets the H wedge at its port.  It cannot also meet
either root: that would be a rooted V triangle through an H dart, excluded
in Section 160.  Thus it meets the wedge exactly once, and (362)/(511) give

```text
q_y(h_p)=t_y  whenever y in N_d(p).                    (714)
```

Consequently the target-active projection of (711) is exactly

```text
t_y partial B_00(y)
 =sum_(p in M_00, y in N_d(p)) q_y(h_p).               (715)
```

There is no dart-choice ambiguity because `q_y` is constant on a port pair
by (381).  Equation (715) is the promised channel change: the two-label
port edge is split at its owner-factor boundary into the individual active
secondary labels already propagated by the canonical run intervals of
Sections 161--165.

For `t_y=0`, the right side of (715) is identically zero while
`partial B_00(y)` need not vanish.  Hence the existing active `q_y` ledger
sees precisely the active projection of the boundary, not all of it.  A
complete use of (713) must therefore handle three explicitly separated
terms: active boundary transport via (715), inactive secondary boundary,
and odd owner-factor-cycle holonomy.  Filtering the H census to the `00`
cell may also create complementary-state terms, just as in (704) and (707);
no cancellation of those terms is asserted here.

## 234. Every boundary-invisible `00` cycle is entirely inactive

The last two terms above are not independent on the cycle-space residue.
Suppose the restriction of `B_00` to a component cycle `C` of `F_e[d]` has
zero boundary and is nonempty.  Since `C` is a cycle graph, that restriction
is the full edge set of `C`.  At every vertex `y of C`, the two incident
factor edges correspond under (709) to the two `e`-neighbors of `y`.  Both
ports belong to `M_00`, hence both lie in the fixed target port set `V_j`.
By the definition of target activity,

```text
|N_e(y) intersect V_j|=2,       so t_y=0.              (716)
```

Therefore every full-cycle summand in the kernel of (711), including every
odd cycle capable of changing augmentation in (712), is supported entirely
on inactive secondary labels.  In particular, the active `q_y` channel of
(715) has no hidden cycle-space ambiguity: all of its ambiguity is exposed
at the boundary.

The live `00` split can consequently be sharpened to

```text
active split-label boundary (the q_y interval channel)
 + inactive boundary/companion-port footprints
 + inactive odd owner-factor-cycle holonomy.           (717)
```

This does not make the last two terms vanish.  It identifies the companion-
port shadow construction as the correct place to price them and rules out
using an active-label alternation to exclude the odd cycle: every label on
such a residue has activity zero.

## 235. The companion-port shadow split fixes the full-cycle holonomy

The three-port footprint transport does not by itself consume the last term
of (717).  Let a component of `F_e[d]` have cyclically ordered vertices
`y_i` and let its edge indexed by the port `p_i` be

```text
N_d(p_i)={y_i,y_(i+1)}.
```

If the full cycle belongs to `B_00`, then the other `e`-neighbor of `y_i`
relative to `p_i` is `p_(i-1)`, and the other neighbor of `y_(i+1)` is
`p_(i+1)`.  Therefore the singleton footprint of
`(73rnz_cjibkzzo)` specializes to

```text
Foot(p_i)=1_(p_(i-1))+1_(p_i)+1_(p_(i+1)).            (718)
```

Summing (718) around the cycle counts every port three times, and hence

```text
sum_i Foot(p_i)=sum_i 1_(p_i)  over F_2.               (719)
```

Equivalently, the labeled shadow stars have zero aggregate boundary on a
full factor cycle, so the footprint identity restricts to the identity map
on its cycle-space class.  On an odd cycle both sides of (719) have odd
augmentation.  Thus the bounded footprint alphabet is a valid transport for
general `00` chains, but its internal shadow relation neither cancels nor
changes the boundary-invisible odd holonomy.

The remaining cycle obstruction is consequently simultaneous in an exact
sense.  The cycle order in (718) comes from the owner factor `F_e[d]`, while
membership of every `p_i` in the marked H census comes from the distinct
root component `c` and its H/V/S matching.  A closing exclusion or price
must compare those two structures; no identity internal to the `d--e`
shadow two-factor can distinguish the selected full cycle from itself.

## 236. The odd curl is a primal owner-factor cycle inside the marked port set

There is an equivalent formulation entirely on the port component `e`.
Two ports `p,r in e` are consecutive in the line graph of `F_e[d]` exactly
when their dual edges share a vertex `y in d`, equivalently when `p,r` have
the common `d`-neighbor `y`.  By the cross-Gram owner-factor identity,

```text
R_ed R_de=2I+F_d[e],                                  (720)
```

this line graph is precisely the owner-`d` factor `F_d[e]`.  The bipartite
`d--e` incidence component therefore projects to cycles of the same length
on its `d` vertices (`F_e[d]`) and its `e` ports (`F_d[e]`), with the edge
of the first projection indexed by the corresponding vertex of the second.

Under this identification, a full-cycle summand of `B_00` is exactly a
component cycle `C*` of `F_d[e]` satisfying

```text
V(C*) subset M_00 subset V_j.                          (721)
```

The first containment says that every port on the primal owner cycle is a
marked `00--00` H port; the second is part of the fixed lifted-dart block.
Cycle length is preserved, so the augmentation-changing case of (712) is
equivalently an odd component of `F_d[e]` satisfying (721).  By (716), all
secondary vertices on its dual cycle are inactive.

Thus the remaining port-secondary curl has the following exact geometric
exclusion target:

```text
no odd component cycle of a third owner factor F_d[e]
is contained in the marked-00 port census of V_j,       (722)
```

or else such a cycle must receive a compensating price from the root-side
H/V/S and owner data.  Statement (722) is not proved here.  It makes clear
which simultaneous structures must interact: adjacency around the residue
comes from owner `d` on the port component, while membership in `M_00` is
defined by the distinct root component `c`, its internal H edge, and the
Baer shore state.  The local shadow identities internal to `(d,e)` cannot
supply that comparison, as (719) shows.

## 237. In the root-closed branch the odd port set is the whole target cycle

Apply the same port indexing to the root component: for the odd port set
`P_C=V(C*)` in (721), form the edge chain

```text
B_C^c:=sum_(p in P_C) [N_c(p)] in C_1(F_e[c];F_2).     (723)
```

Every edge in (723) is the marked shore-`00` H edge indexed by `p`.  The
root-boundary pincer `(73rnz_cjibkzzt)--(73rnz_cjibkzzw)` says that either
`partial B_C^c` gives selected-to-complement H/V/S endpoints, or `B_C^c` is
a union of full cycle components of `F_e[c]` and contains an odd one.

In the latter branch the fixed target component removes the apparent
possibility of several cycles.  A component cycle of `F_e[c]` is the root
projection of one connected bipartite cycle of `R_ce`; its edge-indexing
ports form exactly the corresponding component cycle of the dual shadow
factor `F_c[e]`.  All ports in (723) belong to the single fixed component
`V_j` of `F_c[e]`.  Therefore any nonempty full root-factor component used
by (723) has port set equal to `V_j`.  Since the port indexing is bijective,

```text
partial B_C^c=0  implies  P_C=V_j,                    (724)
```

and `B_C^c` is the unique root projection paired with that incidence
component.  In particular `|V_j|` is odd.

Combining (721) and (724), the boundary-free obstruction has the sharper
form

```text
V_j is simultaneously a component vertex set of
the distinct owner factors F_c[e] and F_d[e],
both restrictions are odd cycles, and every p in V_j
indexes a marked shore-00 H edge in the root projection. (725)
```

The two owner-factor cycles in (725) are edge-disjoint because the owner
factors partition the selector complement on `e`.  No contradiction from
two edge-disjoint odd cycles is asserted.  The gain is that a closed residue
cannot occupy a proper subset of the target incidence component: failure of
root-boundary transport forces a common invariant odd vertex set for two
different owner factors, with the entire root projection marked `00`.

## 238. The five-port simultaneous curl is locally C4-free

The minimum case left by (725) and `(73rnz_cjibkzzy)` cannot be excluded
from the three-component incidence skeleton alone.  There is an explicit
core on five ports `p_i`, five roots `x_i in c`, and five secondary labels
`y_i in d`, with indices modulo five:

```text
N_c(p_i)={x_i,x_(i+1)},       x_i x_(i+1) in A_c,
N_e(y_i)={p_i,p_(i+2)}.                              (726)
```

The root-line edges on the ports are `p_i p_(i+1)`, while the secondary
owner edges are `p_i p_(i+2)`.  They are the two complementary five-cycles
of `K_5`, exactly the forced normal form from (725).

A direct common-neighbor check on the graph consisting of the incidences in
(726) and the five displayed root edges gives

```text
15 vertices, 25 edges, maximum off-diagonal codegree 1. (727)
```

Hence this core is simple and C4-free.  The deterministic reproducer
`verify_five_port_curl_core.py` constructs it and checks (727).  In
particular, the common-edge C4 argument excluding the triangular curl is
sharp at the level of these incidences: two edge-disjoint five-cycles do
not force a four-cycle.

This is a local counterprofile, not an SRP model.  It does not supply the
remaining neighbors required by regularity, the full owner factorization,
or the Baer shore-`00` states at the roots.  It proves that any exclusion of
the minimal curl must use at least one of those additional inputs.  Merely
recounting the two projected cycles, their unique shared roots/labels, and
the marked H triangles cannot close (722).

## 239. Strict color export turns the closed inactive curl into an odd active ledger

The global SRP export `(73rnz_cjibkzzz)--(73rnz_cjibkzzzd)` supplies a
strictly new component `a notin {c,e,d}` for which

```text
E_a:=supp(R_ac 1_C) intersect supp(R_ae 1_Z)
has odd order.                                         (728)
```

The support condition must be read as parity, not containment.  Every
cross fiber has order two, so each `y in E_a` has exactly one `c`-neighbor
`x_y in C` and exactly one `e`-neighbor `p_y in Z`.  In particular its
target-activity bit for the component `Z=V_j` is

```text
t_y=(R_ae 1_Z)(y)=1.                                  (729)
```

Thus the exported labels are active, not inactive.

There is a canonical occurrence map into the `q_y` ledger.  The selected
root `x_y` and port `p_y` cannot be incident in the paired `c--e` cycle:
if `x_y in N_c(p_y)`, then `y` meets both the root and port of an H dart,
giving the rooted V triangle excluded by Section 160.  Let the two H ports
incident to `x_y` on the closed root cycle be `p_y^-` and `p_y^+`; they are
distinct from `p_y`.  Since `y` has no other neighbor in `C or Z`, formula
(362) gives on the H port census

```text
q_y(h_z)=1  iff z in {p_y^-,p_y,p_y^+}.               (730)
```

Port-pair constancy (381) removes the choice of dart.  Each exported label
therefore contributes exactly three, hence one modulo two, to the total
active `q` mass.  Summing (730) over the odd set (728) yields

```text
sum_(y in E_a) sum_(z in Z) q_y(h_z)=|E_a|=1 mod 2.   (731)
```

Consequently the boundary-free inactive `00` curl does not remain an
independent inactive holonomy after the full simultaneous-routing identity
is applied: it creates a nonzero, indeed odd-mass, active secondary ledger
in a genuinely new color.  This is an occurrence transport, not yet its
cancellation.  The resulting `q_y` words enter the canonical interval and
separator/potential machinery of Sections 128 and 140--165; their joint
capacity conservation with the already transported `01` union flags and
complementary H/V/S terms remains the final theorem.

## 240. Every odd export forces an odd three-sector boundary triangle

Fix the receiving color `a` from (728), and for `y in a` put

```text
r_y:=(R_ac 1_C)(y),       t_y:=(R_ae 1_Z)(y).
```

The labels with `r_y=1` index the cut of `C` in the two-regular owner factor
`F_a[c]`; those with `t_y=1` index the cut of `Z` in `F_a[e]`.  Every cut of
a two-regular graph has even order.  If

```text
n_uv:=#{y in a:(r_y,t_y)=(u,v)} mod 2,
```

then (728) says `n_11=1`, while the two cut parities give

```text
n_10+n_11=0,       n_01+n_11=0.
```

Consequently

```text
n_10=n_01=n_11=1.                                  (732)
```

Thus the strict export never creates an isolated odd overlap.  In the same
new color it forces odd populations in all three nonzero boundary sectors:
root-only, port-only, and root-plus-port.

There is also an exact `q_y` interpretation of the two active sectors.  For
any `y` with `t_y=1`, sum (362) over all H ports of the closed paired cycle.
Every root of `C` belongs to two H wedges, so all root-incidence terms occur
twice and cancel; every port of `Z` occurs once, and `y` has exactly one
neighbor there.  Hence

```text
sum_(z in Z) q_y(h_z)=1.                              (733)
```

The entire `t=1` population is a factor cut and has even order, so summing
(733) and partitioning by `r_y` gives

```text
sum_(y:r_y=t_y=1) sum_z q_y(h_z)
 =sum_(y:r_y=0,t_y=1) sum_z q_y(h_z)=1.               (734)
```

Equation (734) is a scalar conservation/payment identity: the odd active
ledger exported from the closed `00` curl is accompanied by an odd active
port-only population in the same owner color.  It does not identify their
private labels occurrence-by-occurrence.  The root-only sector in (732) is
inactive for this target and is the corresponding propagation mark on the
`c` boundary.  Hence the remaining capacity theorem is now supported on a
three-sector boundary triangle, rather than on one unpaired curl.

This three-support shape is the same Boolean incidence pattern as the
singleton/union circuit isolated in the B3 flag kernel: two singleton
boundaries and their joint support.  That is structural convergence, not a
map or a proof of the B3 capacity assertion.  Here (732)--(734) are exact
consequences of the two owner-factor cuts and retain the receiving color,
the physical boundary components, and the active `q_y` occurrences.

## 241. The two factor cuts force an odd root-to-port alternating path census

The shared label `y` in (732) carries more information than the pair of bits
`(r_y,t_y)`.  The edge `N_c(y)` belongs to the two-factor `F_a[c]`.  On each
cycle of that factor, pair the two boundary edges surrounding every maximal
nonempty run in `C`.  This gives a fixed-point-free involution

```text
mu_C : {y:r_y=1} -> {y:r_y=1}.                       (735)
```

Likewise the maximal `Z`-runs in the cycles of `F_a[e]` give

```text
mu_Z : {y:t_y=1} -> {y:t_y=1}.                       (736)
```

These are occurrence-level pairings: a `mu_C` edge remembers the actual
owner-`c` run in `F_a[c]`, and a `mu_Z` edge remembers the actual owner-`e`
run in `F_a[e]`.  They do not require a choice of orientation.  The absence
of two-cycles in the owner factors ensures that the two boundary edges of a
run are distinct.

Form the two-colored multigraph `P_a(C,Z)` whose vertices are the labels with
`r_y=1` or `t_y=1`, whose red edges are the pairs of `mu_C`, and whose blue
edges are the pairs of `mu_Z`.  A vertex in sector `10` has red degree one
and blue degree zero; a vertex in sector `01` has blue degree one and red
degree zero; and a vertex in sector `11` has one edge of each color.  Hence
every component is an alternating cycle or an alternating path, and the path
endpoints lie in the singleton sectors.

On an alternating path, the number of internal `11` vertices is odd exactly
when its two endpoints have different sectors.  Indeed the first and last
edge colors differ exactly when the endpoints are respectively `10` and
`01`; an alternating word has different end colors exactly when it has even
length, equivalently an odd number of internal vertices.  Alternating cycles
have even order.  Summing over components therefore gives the exact parity
identity

```text
#{11 labels}
 = #{alternating paths from a 10 label to a 01 label} mod 2.   (737)
```

Since the export has `n_11=1`, (737) proves

```text
there are an odd number of owner-run alternating paths joining
a root-only boundary label to a port-only active label.        (738)
```

This upgrades the scalar payment (734) to an explicit, owner-resolved route.
The `11` labels on the interior of such a path are precisely exported active
labels; its `10` endpoint is the inactive `c`-boundary propagation mark, and
its `01` endpoint has odd H-port `q_y` mass by (733).  Thus at least one odd
export is transported through the actual two owner factors to a port-only
active occurrence, with all intermediate private labels retained.

Statement (738) is still not the terminal capacity contradiction.  A path
may contain several `11` labels and (733) is a parity statement on the closed
H cycle, not a choice of one private port occurrence.  The remaining theorem
can now be posed on these alternating owner-run paths, rather than on three
unrelated sector populations: combine their endpoint `q_y` words with the
`01` union flags and the complementary H/V/S boundary terms, and prove that
the resulting path boundary has zero total capacity.

## 242. The active word is a port point plus an exact root-chain boundary

The role separation in (730) has a coordinate-free chain form.  Regard the
closed H cycle on the port set `Z` as a cellular cycle.  Its edges are indexed
by the roots of `C`: the edge `E_x` indexed by `x` has as endpoints the two H
ports incident to `x`.  For a receiving label `y` put

```text
A_y:=sum_(x in C intersect N_c(y)) [E_x] in C_1(Z;F_2).
```

If `t_y=1`, let `p_y` be the unique member of `Z intersect N_e(y)`.  Expanding
(362) port by port gives the **zero-chain identity**

```text
Q_y:=sum_(z in Z) q_y(h_z)[z]=[p_y]+partial A_y.      (739)
```

Indeed the port-incidence term occurs only at `p_y`, while each selected root
`x` contributes at the two endpoints of `E_x`.  For `r_y=t_y=1`, the cross
fiber has order two and `A_y=[E_(x_y)]`; (739) is exactly the rigid three-port
pattern (730).  For `r_y=0,t_y=1`, the chain `A_y` has zero or two edges, so
(739) also covers the port-only sector without assuming that it has no root
incidences.

Thus the two root hits in the exported three-port word are already an exact
coboundary.  Modulo root-edge boundaries, every active word is represented by
its unique physical port:

```text
[Q_y]=[[p_y]] in C_0(Z;F_2)/im(partial).              (740)
```

Since `Z` is connected, the quotient in (740) is one-dimensional and all
port points have the same class.  Taking augmentation recovers (733), and
therefore gives no refinement of (734).  In particular a proposed cyclic
displacement parity cannot supply the missing conservation law.  There is no
nonzero rotation-invariant homomorphism from the odd cyclic position group
`Z/|Z|` to `F_2`; choosing numbered ports merely introduces a cut, and moving
that cut changes the parity because `|Z|` is odd.

The useful remaining datum is consequently not a scalar first moment but the
**relative chain representative** in (739): the actual point `p_y`, the
actual root chain `A_y`, and the receiving owner color.  Any terminal joining
the `11` export to its `01` payment must compare the sums of these port-point
chains before quotienting by `im(partial)`; after that quotient only the
already-known odd scalar survives.  Equivalently, the complementary H/V/S
terms in (704) and (707) must pay the root-chain boundaries in (739), while
the `01` union flags must control the residual distribution of the physical
port points.  This rules out both an untagged homology argument and a cyclic
displacement argument, and reduces the live joint-capacity theorem to those
two explicitly retained channels.

## 243. Every mixed owner-run path has an exact active boundary

The alternating paths of Section 241 remove the residual port-point term in
(739) without forgetting its location.  Consider one blue pair
`{y,mu_Z(y)}`.  By construction its two labels are the boundary edges of one
maximal `Z`-run in a cycle of `F_a[e]`.  Let `D_y` be the internal edge chain
of that run, viewed as a chain on the physical port vertex set.  The unique
inside endpoints of the two boundary edges satisfy

```text
[p_y]+[p_(mu_Z(y))]=partial D_y.                      (741)
```

This includes a one-vertex run: then the two inside endpoints coincide and
both sides are zero.  No orientation or choice of a distinguished endpoint
is involved.

Now let `P` be one of the mixed alternating paths in (738), and let `T(P)` be
its vertices with `t_y=1` (the internal `11` vertices together with its `01`
endpoint).  Every vertex of `T(P)` has blue degree one, so the blue edges of
`P` partition `T(P)` into the pairs above.  Summing (741) over those pairs
gives an occurrence-resolved version of the even `t`-cut parity:

```text
sum_(y in T(P)) [p_y]=partial D_P,                    (742)
```

where `D_P` is the sum of their actual owner-`e` run chains.  Combining (742)
with (739), label by label, yields

```text
sum_(y in T(P)) Q_y
 =partial (D_P + sum_(y in T(P)) A_y).                (743)
```

Thus the exported `11` active words and the forced `01` port-only payment do
not merely have equal odd augmentation as in (734): on every mixed
root-to-port owner path their **combined physical H-port zero-chain is
exact**.  The primitive in (743) is also fully resolved.  Its `D_P` part is
made of the receiving owner-`e` runs from Section 241, while its `A_y` part is
made of the root-H edges selected by the same private labels.

Equation (743) is not yet the GAP (702), because exactness here is in the
free port zero-chain after adjoining edges from two different factors.  The
realized H/V/S state route and the `01` union-flag quotient must still show
that this particular primitive has zero price, or transport its boundary
through the complementary transitions in (704) and (707).  It does eliminate
an independent port-distribution obstruction: after grouping by the
canonical mixed owner paths, the only remaining issue is compatibility of
the **cross-factor primitive** `D_P+sum_y A_y` with the realized route price,
not cancellation of unmatched active port points.

## 244. Red owner runs remove every internal root-chain label

The root-chain part of the primitive in (743) has the same run filling on
the red edges of `P_a(C,Z)`.  Let `P` be a mixed path, with `10` endpoint
`y_-` and `01` endpoint `y_+`.  For each red pair `{y,mu_C(y)}` in `P`, let
`R_y` be the internal edge chain of the corresponding maximal `C`-run in
`F_a[c]`, and put

```text
R_P:=sum_({y,mu_C(y)} red in P) R_y.
```

Every red cut label has a unique inside root in `C`.  Therefore

```text
partial R_P
 =sum_(y in P:r_y=1) [x_y].                          (744)
```

Let

```text
E_*:C_0(C;F_2) -> C_1(Z;F_2),       [x] |-> [E_x],
```

where `E_x` is the H-cycle edge indexed by the root `x`, as in Section 242.
For every label with `r_y=1`, the size-two cross fiber gives
`A_y=[E_(x_y)]`.  The `r=1` vertices of a mixed path are its `10` endpoint
and all of its internal `11` vertices.  Applying `E_*` to (744) consequently
gives

```text
E_*(partial R_P)
 =A_(y_-)+sum_(y internal in P) A_y.                 (745)
```

Write the cross-factor primitive from (743) as

```text
W_P:=D_P+sum_(y in T(P)) A_y.
```

Since `T(P)` consists of the internal `11` vertices and the `01` endpoint,
(745) yields the exact decomposition

```text
W_P
 =D_P+E_*(partial R_P)+A_(y_-)+A_(y_+).              (746)
```

Thus none of the private root chains attached to the internal exported
labels remains independent.  They assemble into the image of the actual
red owner-run boundary.  The only unpaired `A` terms are attached to the two
physical endpoints of the mixed path: `A_(y_-)` is one H edge because
`r_(y_-)=1`, while `A_(y_+)` has zero or two H edges because
`r_(y_+)=0`.

Together, (743) and (746) reduce the route-price problem to a geometric
two-ended strip:

```text
blue interior: D_P in F_a[e] on the port vertices;
red interior:  R_P in F_a[c] on the root vertices, mapped by E_*;
ends:          A_(y_-)+A_(y_+) on the H cycle.        (747)
```

This is stronger than retaining every private `A_y`, but it is not a claim
that `E_* partial` is itself a boundary operator or that the strip has zero
price.  That compatibility is exactly the remaining simultaneous H/V/S
input.  The endpoint names `10` and `01` in this section refer only to the
cut bits `(r_y,t_y)` from Section 240.  They are not the Baer shore states
called `10` and `01` in Sections 229--230, so (704) and (707) cannot yet be
applied to these endpoints.  The live theorem must first construct an
owner- and role-resolved map from the two cut-sector endpoints and the strip
in (747) to the complementary H/V/S transition chains and `01` union flags
of those earlier sections, then prove that the resulting price is zero.
Any failure is localized to a mixed path and cannot be attributed to an
unmatched internal active label.

## 245. Run fillers prevent a path-local strip-to-state map

The chains in (747) retain their physical edges but not all of the owner
labels indexing those edges.  This matters before any comparison with the
H/V/S alphabet.  An internal edge of a blue run in `D_P` is an edge of
`F_a[e]`, hence is indexed by a unique label `z in a` with

```text
|N_e(z) intersect Z|=2,       so t_z=0.              (748)
```

Its other cut bit is not determined by being a blue filler.  Since the
`a--c` cross fiber has order two,

```text
|N_c(z) intersect C| in {0,1,2},
r_z=1 iff |N_c(z) intersect C|=1.                    (749)
```

In the middle case `z` is itself a root-only boundary vertex of
`P_a(C,Z)`, hence the `10` endpoint of an alternating path component.  That
component may be the current component (if the endpoint label reappears as
one of its own run fillers) or a different one.  The unlabelled chain `D_P`
does not record which.  Thus even after (746), distinct mixed strips remain
coupled through equality between a run-filler label and a boundary label.

The even cases expose a second obstruction to a local alphabet map.  If the
cardinality in (749) is zero, the owner label `z` has no `V_a` occurrence on
the selected root cycle at all.  If it is two, it has two selected roots,
but the number and placement of rooted `V_a` triangles additionally depend
on which of those roots are incident to the two selected ports.  The bare
edge of `D_P` records neither alignment.  Hence a blue strip edge does not
canonically determine one H/V/S transition or one private half-atom.

There is a symmetric statement for a red-run filler.  An internal edge of
`R_P` is indexed by a label `z in a` satisfying

```text
|N_c(z) intersect C|=2,       so r_z=0,
|N_e(z) intersect Z| in {0,1,2}.                     (750)
```

The middle case is a port-only `01` endpoint of an alternating component;
the even cases again have zero/two target-port incidences.  Therefore the
two interiors in (747) generate a **global component-coupling graph**:
odd opposite-side incidence sends a filler to an endpoint of some
alternating component, while even incidence remains a zero-or-double local
cell whose rooted alignment must be retained separately.

This proves that the missing bridge after (747) cannot be a pathwise map
depending only on the three unlabelled chains displayed there.  A valid
owner/role-resolved lift must at least retain, for every run edge, its
indexing label, its opposite cut multiplicity `0/1/2`, and in the double
case the actual root--port incidence alignment.  After adjoining those
data, the odd fillers may be transported between path components and the
zero/double fillers may be compared with the H/V/S source cells.  Without
that lift, applying the Baer-state transports (704)/(707), or the B3
half-atom antisymmetry (12rzm), would conflate distinct alphabets.

## 246. A mod-four mixed moment counts the odd filler attachments

The `0/1/2` data in Section 245 have an exact aggregate that is invisible
modulo two.  For `z in a` put

```text
i_z:=|N_c(z) intersect C|,       j_z:=|N_e(z) intersect Z|,
```

and let `N_ij` be the integer number of labels with `(i_z,j_z)=(i,j)`.
Define the mixed incidence moment

```text
M_a(C,Z):=sum_(z in a) i_z j_z.                       (751)
```

The labels counted by `N_12` are root-cut labels whose `e`-edge is internal
to `Z`.  Such an edge is either in a proper maximal `Z`-run and hence is a
blue-filler attachment from Section 245, or belongs to a whole component
cycle of `F_a[e]` contained in `Z`.  Write the two counts as `B_att` and
`B_cyc`.  Symmetrically split

```text
N_12=B_att+B_cyc,       N_21=R_att+R_cyc,             (752)
```

where the second closed residue consists of whole `F_a[c]` cycles contained
in `C`.  Expanding (751) over the nine possible cells gives

```text
M_a(C,Z)=N_11+2N_12+2N_21+4N_22.                     (753)
```

Consequently

```text
B_att+R_att+B_cyc+R_cyc
 = (M_a(C,Z)-N_11)/2                         (mod 2). (754)
```

The quotient is integral by (753).  This is the first scalar that sees the
global component-coupling edges together with their boundary-invisible
closed-cycle residue: ordinary support parity sees `N_11` but identifies
opposite multiplicities zero and two, while (754) detects their combined
inside-edge incidence with the cut endpoints.

The same moment already has a graph-facing alphabet.  Double counting the
triples `(x,z,p)` gives

```text
M_a(C,Z)
 =sum_(x in C,p in Z) |N_a(x) intersect N_a(p)|.     (755)
```

C4-freeness makes every summand in (755) zero or one.  Split the sum according
to whether `x` and `p` are incident in the selected `c--e` cycle.  An aligned
triple is exactly a rooted triangle through the dart `(x,p)` with intermediate
color `a`, hence a `V_a` token in the H/V/S alphabet of Section 99.  A
nonincident triple is a uniquely witnessed off-incidence `C--a--Z` connection.
Thus

```text
M_a(C,Z)=V_a(C,Z)+O_a(C,Z),                           (756)
```

where `V_a` is the aligned rooted-`V_a` census and `O_a` is the off-incidence
two-path census, both with their actual root, port, and intermediate label.
The latter is not automatically an active `q_z` occurrence: in particular
the filler cells `j_z=2` have `t_z=0`.  It must remain a separate labeled
connection atom until a route identity transports it.

Combining (754) and (756) gives the exact handshake now required by the
global coupling graph:

```text
B_att+R_att+B_cyc+R_cyc
 = (V_a(C,Z)+O_a(C,Z)-N_11)/2                 (mod 2). (757)
```

Therefore the parity of component-to-component filler attachments **plus the
two closed owner-cycle residues** is encoded by one aligned H/V/S census and
one explicitly located off-incidence census.  The closed terms are the
expected holonomy branch, not path attachments, and must not be discarded.
What remains is to transport the `O_a` atoms and separately price/exclude
`B_cyc+R_cyc`, or prove their joint half-difference price with `V_a-N_11`
vanishes in the simultaneous owner ledger.  Any proposed mod-two argument
that omits the division-by-two information in (757) cannot distinguish the
zero and double filler profiles and is necessarily too coarse.

## 247. Integer SRP fixes the total mixed moment modulo four

The moments (751) are the integer masses of the exterior routing layers:

```text
M_a(C,Z)=1_C^T R_ca R_ae 1_Z.                        (758)
```

They therefore sum exactly under the integer simultaneous routing identity,
not merely under its mod-two reduction.  Because `(C,Z)` is one whole
connected component of the two-regular cross-incidence graph `R_ce`, one has
over the integers

```text
R_ce 1_Z=2 1_C,             R_ec 1_C=2 1_Z.          (759)
```

Let `e_c(C)` be the number of internal `A_c` edges with both endpoints in
`C`, and define `e_e(Z)` analogously.  Pairing

```text
A_c R_ce+R_ce A_e+sum_(a != c,e) R_ca R_ae=J
```

with `1_C,1_Z` and using (759) evaluates the two endpoint layers as

```text
1_C^T A_c R_ce 1_Z=2(1_C^T A_c 1_C)=4 e_c(C),
1_C^T R_ce A_e 1_Z=2(1_Z^T A_e 1_Z)=4 e_e(Z).
```

The two shores of a two-regular bipartite component have the same order;
write `|C|=|Z|=ell`.  The exact exterior-mass identity is consequently

```text
sum_(a != c,e) M_a(C,Z)
 =ell^2-4(e_c(C)+e_e(Z)).                             (760)
```

The closed curl has odd `ell`, so `ell^2=1 mod 4`.  Hence

```text
sum_(a != c,e) M_a(C,Z)=1 mod 4.                     (761)
```

This is a genuine strengthening of the odd export identity
`(73rnz_cjibkzzza)`: the endpoint layers vanish in blocks of four, not only
modulo two.

For each exterior color attach a superscript `a` to the nine-cell counts of
Section 246.  Substituting (753) into (761) gives the global coupling law

```text
sum_(a != c,e)
  (N_11^a+2N_12^a+2N_21^a)=1 mod 4.                 (762)
```

In particular, if

```text
S_11:=sum_a N_11^a,       F:=sum_a(N_12^a+N_21^a),
```

then `S_11` is odd and

```text
F=(1-S_11)/2 mod 2.                                  (763)
```

Here `F` counts both the odd filler attachments and the closed owner-cycle
residues split in (752).  Thus their **combined** global parity is fixed by
the total overlap population modulo four; neither part is an independent
path statistic, and the closed residue cannot be dropped.

Finally (756) turns the same law into the physical route alphabet:

```text
sum_(a != c,e) (V_a(C,Z)+O_a(C,Z))=1 mod 4.          (764)
```

Equation (764) is an integer H/V/S--connection curvature for the closed
curl: across every exterior routing color, the aligned rooted-V tokens and
the off-incidence atoms have total mass one modulo four.  It still does not
separate `V_a` from `O_a`, and (763) still requires `S_11 mod 4`; those are
the remaining owner-resolved tasks together with the closed-cycle price.
But any global half-atom conservation must now reproduce (760), not merely
the mod-two rank-one export, and its
candidate price is constrained by the nonzero residue (764).

## 248. The closed horizontal curl has purely off-incidence curvature

In the branch under consideration the aligned term of (764) vanishes, not
merely modulo four.  By (725), every `p in Z` indexes a marked horizontal
edge in the root projection on `C`.  Equivalently, both incidence darts at
that port are decorated `H`.  Since `(C,Z)` is the whole cross-incidence
component, every root `x in C` is incident to its two cycle ports in `Z`, and
both are horizontal.  The rooted budget from Section 99 is

```text
a(x)+2b(x)+v(x)=2.
```

Here `a(x)=2`, so `b(x)=v(x)=0`.  In particular no selected incidence dart
`(x,p)` with `x in C,p in Z` supports a rooted triangle of any exterior
color.  Therefore, color by color,

```text
V_a(C,Z)=0.                                           (765)
```

Substitution into (756) sharpens the per-color filler handshake to

```text
B_att^a+R_att^a+B_cyc^a+R_cyc^a
 = (O_a(C,Z)-N_11^a)/2                       (mod 2). (766)
```

The numerator is even by the exact cell identity, so no independent
divisibility assumption is used.  More importantly, (764) becomes

```text
sum_(a != c,e) O_a(C,Z)=1 mod 4.                     (767)
```

Thus the nonzero integer curvature of the closed curl is **entirely
off-incidence**.  It cannot be paid by aligned `V` tokens on the selected H
cycle, because the all-horizontal root budget excludes every such token.
The remaining transport problem has consequently lost one more channel:
the global owner ledger must carry an off-incidence `C--a--Z` two-path mass
congruent to one modulo four, while its half-difference from the strict
overlap count prices the proper filler attachments plus the closed-cycle
residues through (766).  Any proposed H/V/S cancellation that uses only the
visible alphabet on the selected darts misses the whole curvature in (767).

## 249. Off-incidence curvature bounds the internal edge budget

The exact identity (760) and the vanishing (765) also give a nonnegative
integer constraint, not only a congruence.  Every one of the `ell` distinct
ports in `Z` indexes one distinct horizontal edge of the root projection on
`C`.  All of those edges belong to `A_c[C]`, so

```text
e_c(C) >= ell.                                        (768)
```

Additional `A_c` edges with both endpoints in `C` are not excluded; (768)
is deliberately an inequality rather than the false assertion that the
displayed cycle is induced in `A_c`.

By (756) and (765), `M_a(C,Z)=O_a(C,Z)` for every exterior color.  Therefore
(760) becomes the exact identity

```text
O_tot:=sum_(a != c,e) O_a(C,Z)
 =ell^2-4(e_c(C)+e_e(Z)).                             (769)
```

The left side is a cardinality and is nonnegative.  Hence

```text
e_c(C)+e_e(Z) <= floor(ell^2/4),
e_e(Z) <= floor(ell(ell-4)/4).                        (770)
```

Thus the selected horizontal root cycle consumes enough of the integer SRP
mass to bound every internal `A_e` edge on the paired port set.  This is a
uniform consequence of the closed curl; it uses no finite certificate and
does not assume either selected set is induced.

For the minimal surviving curl `ell=5`, (768)--(770) leave only

```text
(e_c(C),e_e(Z),O_tot)
  in {(5,0,5),(5,1,1),(6,0,1)}.                     (771)
```

Indeed `5 <= e_c(C)`, `0 <= e_e(Z)`, and their sum is at most six; (769)
then gives `O_tot=25-4(e_c+e_e)`.  In particular the five-port core of
Section 238 has at most one internal port-side edge and at most one extra
root-side edge beyond its horizontal cycle, never both.  The local core
check (727) did not include these regularity-completion edges, so (771) is a
strict global refinement of that counterprofile.

Equation (771) is not a five-port exclusion.  Its remaining cases have one
or five off-incidence atoms, and the identity does not yet locate their
intermediate colors or owner prices.  It reduces the minimal curl terminal
to three exact edge budgets on which the global labeled-atom handshake must
act; any proposed completion with a larger internal edge count is already
ruled out by integer SRP.

## 250. The horizontal five-cycle is induced

The exact mass formula becomes rigid in the minimum case of Section 238.
Assume `ell=5`.  The five horizontal root-projection edges form a `C_5`
inside `A_c[C]`.  Any additional `A_c` edge on these five vertices joins two
nonconsecutive cycle vertices.  One of the two cycle arcs between its
endpoints has length three, so that chord together with the three arc edges
is a four-cycle.  C4-freeness therefore forces the horizontal `C_5` to be
induced and

```text
e_c(C)=5.                                             (772)
```

This argument is special to length five; for a longer odd cycle a chord need
not have a complementary three-edge arc, so no general chord-free assertion
is made.

Substituting (772) into the already sharpened five-port budget (769) gives

```text
sum_(a != c,e) O_a(C,Z)=25-20-4e_e(Z)=5-4e_e(Z).     (773)
```

The left side is a nonnegative census.  Hence `e_e(Z)<=1`, and integrality
leaves exactly

```text
(e_e(Z), sum_a O_a(C,Z)) in {(0,5),(1,1)}.           (774)
```

Thus C4-freeness removes the `(6,0,1)` case from (771).  The explicit
five-port incidence core of Section 238 has only two possible regular
completions at the level of the integer routing mass: five
off-incidence exterior atoms when the port set is internally `A_e`-empty, or
one atom when it contains a unique `A_e` edge.  Excluding the minimal curl
now requires ruling out these two sharply bounded owner-resolved cases, not
an unbounded connection ledger.

## 251. Endpoint-layer disjointness removes the last port-edge case

The remaining `e_e(Z)=1` alternative in (774) is incompatible with the
entrywise endpoint-layer partition.  Retain the cyclic indexing (726).  By
the induced horizontal cycle (772), routing from a fixed root `x_i` through
its two `A_c` neighbors reaches

```text
N_e(x_(i-1)) union N_e(x_(i+1))
 ={p_(i-2),p_(i-1),p_i,p_(i+1)}.                    (775)
```

These are exactly four occupied cells in row `x_i` of
`Q_c=A_c R_ce`; its unique missing column on `Z` is `p_(i+2)`.

Suppose `p_j p_k` were an edge of `A_e[Z]`.  Since `p_j` is incident to
both `x_j,x_(j+1)`, the other endpoint layer `Q_e=R_ce A_e` would contain
the two cells

```text
(x_j,p_k),       (x_(j+1),p_k).
```

Their respective `Q_c`-missing columns are `p_(j+2)` and `p_(j+3)`.  One
column `p_k` cannot equal both, so at least one displayed `Q_e` cell overlaps
`Q_c`, contradicting the endpoint-layer disjointness (7).  Therefore

```text
e_e(Z)=0,             O_tot=5.                       (776)
```

The conclusion is entrywise.  On the `C by Z` block, `Q_c` occupies the four
cells (775) in every row and `Q_e` is zero.  Integer SRP leaves exactly the
permutation support

```text
sum_(a != c,e) Q_a |_((C,Z))
  ={(x_i,p_(i+2)): i in Z/5}.                        (777)
```

Each missing cell has a unique exterior intermediate vertex `z_i`, so the
five off-incidence atoms are located at

```text
x_i -- z_i -- p_(i+2).                               (778)
```

Adjacent atoms have distinct intermediate vertices.  If
`z_i=z_(i+1)`, then the consecutive roots `x_i,x_(i+1)` would have the two
common neighbors `p_i` and `z_i`, forming a four-cycle.  Repetition at
nonadjacent indices is not excluded, and distinct vertices may lie in the
same exterior component.

Thus the minimum curl has neither a root chord nor an internal port edge:
it has one rigid five-cell off-incidence permutation.  This still does not
exclude a regular completion, but it replaces the two numerical cases of
(774) by one fully located interface on which the owner/color handshake
must act.

## 252. Every five-port exterior atom is a distinct strict export

The five intermediates in (778) cannot reuse a vertex.  In fact every pair
of distinct roots of the horizontal `C_5` already has a common neighbor in
the displayed core.  Consecutive roots `x_i,x_(i+1)` share their indexing
port `p_i`.  Nonconsecutive roots have cycle distance two and share the
middle root on the corresponding two-edge `A_c` path.  If one exterior
vertex `z` met two roots of `C`, it would be a second common neighbor of
that pair and would create a four-cycle.  Hence, for every exterior label,

```text
i_z=|N_c(z) intersect C| <= 1.                       (779)
```

The aggregate exterior support (777) has exactly one cell in each root row.
If a label with `i_z=1` had `j_z=2`, its two selected ports would create two
exterior cells in the same row.  Therefore every label which contributes a
positive mixed moment has

```text
(i_z,j_z)=(1,1).                                     (780)
```

It follows both that the five intermediates `z_i` in (778) are pairwise
distinct and that the full nine-cell census across all exterior colors is

```text
sum_a N_11^a=5,
sum_a N_12^a=sum_a N_21^a=sum_a N_22^a=0.            (781)
```

The vanishing is integer, not only parity.  In particular the proper
run-filler attachments and the whole contained owner-cycle residues from
(752) all vanish for the selected five-port target:

```text
sum_a(B_att^a+R_att^a+B_cyc^a+R_cyc^a)=0.           (782)
```

Color by color one also has

```text
O_a(C,Z)=N_11^a,                                     (783)
```

because every exterior two-path cell is one of the five strict exports and
all aligned cells vanish by (765).  Thus the division-by-two handshake
(766) is identically zero in every receiving color, while the global
curvature is the five strict-overlap atoms themselves.

The minimum curl terminal has therefore lost all new-color filler and
closed-cycle ambiguity.  Its only exterior response is a rigid five-term
strict export, one atom in each root and port position of the offset
permutation (777), with adjacent (indeed all) intermediate vertices
distinct.  What remains is a color/owner constraint on these five labels,
not a capacity choice among `0/1/2` profiles.

## 253. Each receiving color has an exact ten-by-ten cut census

The five strict exports are distributed among components genuinely different
from the original curl colors.  Fix

```text
a notin {c,e,d}.
```

The root-side argument (779) applies to every vertex of `a`: no label can
meet two roots of `C`.  Every root has cross degree two into `a`, so the ten
`C--a` incidences have ten distinct `a` endpoints.  Therefore

```text
#{z in a:i_z=1}=10.                                  (784)
```

There is a symmetric pointwise bound on the port side which uses the
original secondary color `d`.  Two adjacent ports of the cycle `F_c[e][Z]`
share their `c`-root.  Two nonadjacent ports have cyclic distance two and,
by the complementary five-cycle normal form (726), share their unique
`d`-owner vertex.  Thus every pair of distinct ports in `Z` already has a
common neighbor in `c` or `d`.  Since `a` is different from both colors,
C4-freeness gives

```text
j_z=|N_e(z) intersect Z| <= 1       for every z in a. (785)
```

Every port has cross degree two into `a`, so the same incidence count yields

```text
#{z in a:j_z=1}=10.                                  (786)
```

Put `k_a:=N_11^a`, the number of the five strict exports received by color
`a`.  Equations (784)--(786), together with the absence of `12` and `21`
cells from (781), give the exact integer census

```text
N_10^a=N_01^a=10-k_a.                                (787)
```

This strengthens the parity triangle (732): in the five-port case both
singleton sectors have the same known cardinality, not merely the same
parity as the overlap.  The alternating graph `P_a(C,Z)` therefore has
`k_a` degree-two vertices and exactly `10-k_a` endpoints of each color.

The original secondary component `d` receives no strict export because
`R_de 1_Z=0` makes every one of its labels have `j_z` even.  Hence (781)
also gives

```text
sum_(a notin {c,e,d}) k_a=5.                         (788)
```

No distribution of the five among receiving colors is asserted.  Equations
(787)--(788) provide the exact owner-factor capacity that any such color
distribution must support: a color receiving `k_a` rigid atoms must also
carry `10-k_a` root-only and `10-k_a` port-only cut labels.  The remaining
terminal is to show that these ten-by-ten cut systems cannot realize the
offset five-atom routing permutation while respecting the simultaneous
owner factors and their outside endpoints.

## 254. The five strict-export active words are linearly independent

The active `q`-ledger retains the complete index set of the five exports,
not only its parity.  In the indexing (726), root `x_i` is incident to the
two H ports `p_(i-1),p_i`, while the strict export `z_i` meets the selected
port `p_(i+2)` by (778).  Therefore (730) gives

```text
supp(q_(z_i)|_Z)={p_(i-1),p_i,p_(i+2)}.              (789)
```

Let `v_i in F_2^Z` be this three-port word.  Suppose
`sum_i s_i v_i=0`.  Reading the coordinate at `p_j` gives, for every
`j in Z/5`,

```text
s_j+s_(j+1)+s_(j-2)=0.                               (790)
```

The equations at `j=0,1` give
`s_3=s_0+s_1` and `s_4=s_1+s_2`.  The equation at `j=2` then gives
`s_2=s_1`, hence `s_4=0`; the equations at `j=3,4` give successively
`s_0=0` and `s_1=0`.  Thus every coefficient vanishes:

```text
v_0,v_1,v_2,v_3,v_4 are linearly independent over F_2. (791)
```

For an exterior receiving color `a`, let

```text
I_a:={i:z_i in a},       Q_a:=sum_(i in I_a) v_i.
```

Then (791) proves

```text
Q_a=0 iff I_a=empty,                                   (792)
```

and indeed `Q_a` uniquely recovers the entire subset `I_a`.  Consequently
no nonempty collection of the five strict exports can cancel inside one
color's active H-port ledger, even when `|I_a|` is even.  Across colors the
same conclusion holds in the direct sum of the color-tagged ledgers.

The scalar three-sector law of Section 240 only detects colors with odd
`|I_a|`; (792) also exposes every nonempty even population.  Hence a
five-port completion cannot hide any exported color by internal active-word
cancellation.  Every used exterior color leaves a nonzero, index-resolved
boundary demand which must be paid by that color's complementary transition
terms.  The remaining owner theorem may therefore work color by color on
the explicitly recoverable subsets `I_a`, rather than on an anonymous
five-unit total.

## 255. Every strict export has an isolated root--port payment path

The ten-by-ten census of Section 253 makes the alternating paths completely
local.  Fix an exterior color `a`.  Since every label has `i_z<=1`, no edge
of the owner factor `F_a[c]` has both endpoints in `C`.  Thus `C` is an
independent set in that factor.  Every maximal nonempty `C`-run is a single
root, and its two boundary labels are paired by `mu_C`.  Symmetrically,
`j_z<=1` makes `Z` independent in `F_a[e]`, so every `mu_Z` pair bounds one
selected port.

Let `z_i in a` be one of the strict exports.  Its red mate is the other
`a`-label indexing an owner-factor edge at `x_i`; call it `u_i`.  The row
support (777) has only one strict export at `x_i`, so `u_i` is not an overlap
label.  The exact bounds give

```text
(i_(u_i),j_(u_i))=(1,0).                             (793)
```

Likewise the blue mate `v_i` is the other `a`-label at `p_(i+2)`, and

```text
(i_(v_i),j_(v_i))=(0,1).                             (794)
```

Consequently the component of `P_a(C,Z)` containing `z_i` is exactly

```text
u_i --red-- z_i --blue-- v_i,                        (795)
```

an isolated length-two path from a root-only label to a port-only label.
Different strict exports have different red and blue mates because the
factor pairings are involutions.  The rest of `P_a(C,Z)` consists of
`5-k_a` isolated red `10--10` edges and `5-k_a` isolated blue `01--01`
edges, in agreement with (787).

The active-word payment on (795) is pointwise.  The port-only mate `v_i`
has no selected root and has the unique selected port `p_(i+2)`, so (739)
specializes to

```text
Q_(v_i)=[p_(i+2)].                                   (796)
```

For the strict export, (739) gives

```text
Q_(z_i)=[p_(i+2)]+partial[E_(x_i)].                  (797)
```

Adding the two active words cancels their common physical port point:

```text
Q_(z_i)+Q_(v_i)
 =partial[E_(x_i)]=[p_(i-1)]+[p_i].                 (798)
```

Thus the scalar payment of (734) has become a canonical occurrence-level
map in the five-port case: every strict export is paired with one private
port-only label in the same receiving color, and their combined active
ledger is exactly the boundary of the one horizontal H edge indexed by the
shared root.  No filler chain, multi-export alternating path, or closed
cycle remains.  The final owner-price question is now whether the red
root-only mate `u_i` and the complementary H/V/S transition at `x_i` pay
this single edge boundary; the active port side is completely resolved.

## 256. The active boundary closes only in the monochromatic case

Sum the isolated payment identity (798) over the strict exports received by
one exterior color `a`.  With `I_a` as in Section 254, its total active
residue is

```text
partial H_a,       H_a:=sum_(i in I_a)[E_(x_i)].     (799)
```

The edges `E_(x_i)` form the connected five-cycle on `Z`.  Over `F_2`, the
kernel of the boundary map on the edge space of a connected cycle consists
of the zero chain and the full cycle.  Therefore

```text
partial H_a=0
 iff I_a=empty or I_a=Z/5.                            (800)
```

This criterion retains the color tag.  The nonempty sets `I_a` partition
the five export indices by (788), so exactly one of the following holds:

```text
monochromatic: one exterior color has I_a=Z/5;
               its five active payments close once around the H cycle;

multicolor:    at least two exterior colors are used;
               every used color has partial H_a != 0.                (801)
```

In the multicolor branch the boundary support is explicit: it is the set of
ports at which membership in the cyclic subset `I_a` changes.  It is
nonempty and even, and different colors retain disjoint export-index sets
even if their boundary port supports overlap.

Equation (801) separates two genuinely different final owner-price tasks.
In the multicolor branch, every used color must transport a nonzero located
H-boundary through its root-only mates and complementary transitions.  In
the monochromatic branch, the active boundary itself vanishes, so an
exclusion must use the closed full-cycle owner/color data rather than an
endpoint demand.  No scalar parity or uncolored sum distinguishes these
branches; the color-resolved chain does.

## 257. Each active payment equals its inactive mate boundary

The right side of (798) already has a canonical label: it is the
unprojected wedge word of the red root-only mate.  For any receiving label
`y`, before multiplying by the target-activity bit, define

```text
W_y:=sum_(p in Z intersect N_e(y))[p]+partial A_y.    (802)
```

This is the same incidence expression as (739), without the factor `t_y`.
Thus

```text
t_y=1 implies W_y=Q_y;
t_y=0 implies Q_y=0 but W_y may be nonzero.           (803)
```

On the isolated path (795), the red mate `u_i` lies in cell `10`.  It has
the unique selected root `x_i` and no selected port, so

```text
A_(u_i)=[E_(x_i)],       W_(u_i)=partial[E_(x_i)].    (804)
```

Comparing (804) with the active pair identity (798) gives the pointwise
three-label conservation law

```text
Q_(z_i)+Q_(v_i)=W_(u_i).                              (805)
```

Hence the active strict export and its port-only payment do not leave an
anonymous H-boundary: they produce exactly the boundary word carried by the
unique inactive root-only mate in the same owner-factor component.  Summing
(805) over `I_a` recovers (799), now with a private label on every summand.

This identifies, occurrence by occurrence, the inactive secondary-boundary
channel separated abstractly in Section 233.  It does not make that channel
zero.  The remaining owner theorem is to transport the labeled words
`W_(u_i)` through the companion ports and complementary H/V/S transitions,
or to show that a closed monochromatic sum has forbidden owner holonomy.
The payer is no longer missing; only its global route price is.

## 258. Untagged wedge-word conservation is tautological

The raw words (802) satisfy a colorwise identity before any five-port
specialization.  Fix a receiving color `a` and sum over all `y in a`.  In
the port term, every `p in Z` has exactly two `a`-neighbors because the
cross block `R_ea` has row sum two.  Hence every basis point `[p]` occurs
twice.  In the root-chain term, every `x in C` likewise has exactly two
`a`-neighbors, so its edge `[E_x]` occurs twice in `sum_y A_y`.  Over
`F_2` both contributions vanish:

```text
sum_(y in a) W_y=0.                                  (806)
```

For a genuine exterior color in the five-port case, the pointwise bounds
`i_y,j_y<=1` from Section 253 imply that a `00` label has no selected root
and no selected port, hence `W_y=0`.  Active labels have `W_y=Q_y` by
(803).  Splitting (806) into the exact four cut sectors therefore gives

```text
sum_(y:11 or 01) Q_y = sum_(y:10) W_y.               (807)
```

The isolated paths of Section 255 refine (807) label by label through
(805); the remaining `10--10` and `01--01` singleton-run pairs cancel in
their respective raw/active sums because both endpoints carry the same
single root-edge boundary or port point.  Thus §257 is not merely compatible
with cross-degree conservation: it is its canonical private-label
decomposition.

Equation (806) also proves a sharp no-go for coarse prices.  If
`lambda:C_0(Z;F_2)->F_2` is any linear functional depending only on the
unlabeled physical port zero-chain, then

```text
sum_(y in a) lambda(W_y)=0                            (808)
```

identically in every receiving color.  Such a price cannot distinguish the
marked curl from its forced active/inactive payments and therefore cannot
exclude the five-port completion.  A successful final price must retain
data erased by `W_y`: at least the private label, its sector/owner role, or
the destination components of its two outside cross-fiber neighbors.  This
is the same information boundary independently found by the B3 half-atom
dual audit: color aggregation fails, while private label identity together
with its local role census suffices on every sampled terminal.

The live five-port theorem is consequently precise.  Transport the
**label-tagged** inactive words `W_(u_i)` through their outside ports and
complementary owner states, or derive a private-label price whose sum is
nonzero despite the untagged identity (806).  Repeating an untagged boundary
or homology calculation cannot make progress beyond this point.

## 259. Every strict export has a canonical odd outside-destination tag

The isolated red mate in Section 255 can be tied to an actual row of the
`c--a--e` routing layer.  Fix `i in I_a`.  The two `a`-neighbors of the
selected root `x_i` are exactly the strict export `z_i` and its red mate
`u_i`.  Consequently the support of the `x_i` row of

```text
L_a^(c,e):=R_ca R_ae
```

is the union of their two port-neighborhoods.  This union is disjoint.  If
some port `p` were adjacent to both `z_i` and `u_i`, then `x_i` and `p`
would have the two common `a`-neighbors `z_i,u_i`, contrary to
`C_4`-freeness.  Thus the routing row has four distinct ports:

```text
supp(L_a^(c,e)[x_i,-])
 =N_e(z_i) disjoint_union N_e(u_i),
|supp(L_a^(c,e)[x_i,-])|=4.                         (809)
```

The sector labels make the selected part of this row exact.  The `11`
label `z_i` has the unique selected neighbor `p_(i+2)`, whereas the `10`
label `u_i` has none.  Hence

```text
supp(L_a^(c,e)[x_i,-]) intersect Z={p_(i+2)}.        (810)
```

Let `D_i^a` be the other three ports in this row.  They are distinct and
all lie outside the selected target incidence component `Z`.  One is the
second port of the active label `z_i`; the other two are precisely the two
outside ports of its inactive mate `u_i`:

```text
D_i^a=(N_e(z_i)\{p_(i+2)}) disjoint_union N_e(u_i),
|D_i^a|=3.                                          (811)
```

In particular this is private-label information that survives the no-go in
Section 258.  If the target incidence components outside `Z` are indexed by
`j != 0`, define the destination-parity tag

```text
delta_i^a(j):=|D_i^a intersect V_j| mod 2.
```

Because the three ports of `D_i^a` are partitioned among those components,

```text
sum_(j != 0) delta_i^a(j)=1 in F_2,
so delta_i^a != 0.                                  (812)
```

Thus every strict export carries a canonical nonzero off-component tag,
namely the odd destination profile of the same routing row that contains
its selected port.  The inactive mate alone contributes two of the three
outside ports and need not have nonzero component parity; the indispensable
tag is the full root-row triple (811), which also remembers the companion
outside port of `z_i`.  The remaining transport problem may therefore be
posed on the labeled vectors `delta_i^a`, rather than on the physical
boundary words `W_(u_i)` whose untagged color sum vanishes.

## 260. No color distribution hides both surviving channels

Aggregate the destination tags within one receiving color:

```text
Delta_a:=sum_(i in I_a) delta_i^a.
```

Let `aug` sum the coordinates over the incidence components `j!=0`.  By
(812), every strict export contributes one to this augmentation.  Therefore

```text
aug(Delta_a)=|I_a|=k_a mod 2.                        (813)
```

In particular, every color receiving an odd number of exports has
`Delta_a!=0`.  This complements the H-boundary criterion (800), which is
nonzero for every proper nonempty subset regardless of its cardinality.

The two branches of (801) can now be sharpened:

```text
monochromatic: k_a=5 for one color;
               partial H_a=0 but Delta_a!=0;

multicolor:    every used color has partial H_a!=0;
               every used color of odd k_a also has Delta_a!=0.     (814)
```

Since the nonzero `k_a` sum to five, the multicolor branch always has at
least one odd-`k_a` color, and hence at least one color in which both
channels are visible.  Consequently

```text
for every distribution of the five strict exports,
some color has a nonzero active H-boundary or a nonzero
outside-destination tag; the two vanish simultaneously for no branch.  (815)
```

This does not yet contradict a completion: complementary owner states may
transport either channel.  It removes the last purely color-distribution
escape.  In the multicolor case the located boundary `partial H_a` is the
primary demand, with `Delta_a` as an additional tag on odd populations.  In
the monochromatic case the active boundary closes, but its five private
rows export an unavoidable odd destination profile.  A final owner price
may therefore be stated uniformly on the pair

```text
(partial H_a,Delta_a),
```

and need only prove that the realized complementary transitions cannot pay
a nonzero pair.  Neither monochromatic closure nor an even-sized receiving
population makes the five-port curl invisible.
## 261. The destination tags are the root-indexed switch row

The vectors in Section 259 are not auxiliary decorations.  They give an
exact local decomposition of the component-switch matrix from Section 18.
For every root `x in C` and exterior color `a`, let `y_x^0,y_x^1` be the
two `a`-neighbors of `x`.  As in (809), their two port-neighborhoods are
disjoint, so they form the four distinct ports in the `x` row of
`L_a^(c,e)`.  For `j != 0`, put

```text
delta_x^a(j)
 :=|(N_e(y_x^0) disjoint_union N_e(y_x^1)) intersect V_j| mod 2. (816)
```

In the five-port case, every `a`-label has at most one neighbor in `C` by
(783).  Hence the support of `R_ac C` is partitioned by the five red pairs
`{y_x^0,y_x^1}`, one for each `x in C`.  Expanding (67) label by label and
then grouping by these private roots gives, for every outside component,

```text
t^a_0j=(R_ac C)^T(R_ae V_j)
       =sum_(x in C) delta_x^a(j),       j != 0.       (817)
```

Thus (817) is a root-indexed lift of the old aggregate switch row.  Its
local row parity is also exact.  The four ports belonging to `x` are
partitioned between `Z=V_0` and the components `V_j`, `j != 0`, so

```text
sum_(j != 0) delta_x^a(j)
 =|supp(L_a^(c,e)[x,-]) intersect Z| mod 2.           (818)
```

Section 251 proved that each selected root supports exactly one strict
export in total.  Therefore the right side of (818) is one precisely when
that unique export has color `a`, and is zero for every other exterior
color:

```text
sum_(j != 0) delta_x^a(j)=1_{x=x_i with i in I_a}.    (819)
```

For `x=x_i`, (816) is exactly the nonzero vector `delta_i^a` of Section
259.  All other local summands in the same color have even coordinate sum.
Consequently

```text
sum_(j != 0) t^a_0j=|I_a| mod 2,                     (820)
```

but (817)--(819) retain the five individual witnesses that (820) discards.
This identifies precisely where the switch formalism lost the private
label: it summed the five local routing rows over `x in C`.  Any proposed
owner holonomy can now be tested on the labeled family `delta_x^a`; no new
notion of destination or ad hoc refinement of `t^a` is required.

## 262. Rootwise SRP couples the destination tags to owner transfer

There is an exact label-preserving bridge from the local switch rows in
Section 261 to the complementary owner geometry on the target fiber.  For
`x in C` and every incidence component `V_j`, define

```text
b_x(j):=e_x^T R_ce A_e V_j.                          (821)
```

The vector `R_ec e_x` consists of the two `e`-ports incident to `x` in the
selected `R_ce` component.  Thus `b_x(j)` is the parity of their internal
`A_e` owner edges into `V_j`.

Pair `SRP(c,e)` on the left with the individual basis row `e_x^T` and on
the right with `V_j`.  The `A_c R_ce` endpoint term vanishes because
`R_ce V_j=0`.  The exterior routing term at `x` is the four-port row used
in (809) and (816).  Therefore, for every `j != 0`,

```text
sum_(a != c,e) delta_x^a(j)=s_j+b_x(j),              (822)
```

where `s_j=|V_j| mod 2` as in Section 19.  Unlike (71), equation (822) has
not summed over the five roots: it retains both the private root index and
the actual target-owner transition at its two adjacent ports.

The same row equation at `j=0` is also informative.  Its exterior routing
sum is the parity of strict exports supported at `x`, which is exactly one
by Section 251, while `s_0=|Z|=1` in `F_2`.  Hence

```text
b_x(0)=0.                                            (823)
```

Finally, summing (821) over every target component gives zero because
`A_e 1_e=0`.  Combining this with (823) yields the even-margin law

```text
sum_(j != 0)b_x(j)=0.                                (824)
```

Thus the complementary owner term cannot supply the odd augmentation of a
single strict destination tag by itself.  Rootwise, the sum over exterior
colors is the fixed incidence-parity vector `(s_j)_(j!=0)` plus the
even-augmentation owner deformation `b_x`.  Equation (822) is the precise
local transfer identity sought after (812): any terminal price must now
separate the unique odd color at `x` from the even local destination rows
of the other colors while respecting this owner deformation.

## 263. On the five-port curl the owner deformation is an exact coboundary

The owner profile in Section 262 has a canonical primitive on the selected
port cycle.  Retain the indexing in which the two selected ports incident
to `x_i` are `p_(i-1),p_i`.  Section 251 proved the integer statement
`e_e(Z)=0`, so neither `A_e`-neighbor of any `p_i` lies in `Z`.  For every
outside incidence component define the per-port destination profile

```text
beta_i(j):=|N_(A_e)(p_i) intersect V_j| mod 2,       j != 0.       (825)
```

Each `p_i` has `A_e`-degree two.  Hence every `beta_i` has even
augmentation:

```text
sum_(j != 0) beta_i(j)=0.                            (826)
```

The two entries of `R_ec e_(x_i)` are exactly `p_(i-1)` and `p_i`.
Expanding (821) at those two ports therefore gives the pointwise identity

```text
b_(x_i)(j)=beta_(i-1)(j)+beta_i(j).                  (827)
```

Thus the even-margin assertion (824) is not merely a scalar parity fact:
the whole complementary owner deformation is the adjacent boundary of the
five private port profiles.  If

```text
gamma_i:=sum_(a != c,e) delta_(x_i)^a
```

is the color-summed local routing row, then (822) becomes the exact affine
cycle equation

```text
gamma_i=s+beta_(i-1)+beta_i.                         (828)
```

Here `s=(s_j)_(j!=0)` is constant in the root index.  Summing around the
odd five-cycle cancels every `beta_i` twice and leaves

```text
sum_(i mod 5) gamma_i=s.                             (829)
```

Equation (829) is the root-indexed form of the old rank-one switch row
(73), while (828) records exactly what that contraction erased.  In the
cokernel of the cycle boundary `beta |-> (beta_(i-1)+beta_i)_i`, the local
routing family has the fixed affine class represented by the constant word
`s`; all target-owner freedom lies in the displayed coboundary.

This is still not a contradiction.  The sum over exterior colors in
`gamma_i` forgets which unique color has odd augmentation at `x_i`, and the
even local rows of the other colors may be nonzero.  The remaining theorem
must therefore separate that distinguished color before taking the sum in
(828), or show that no color-resolved lift of the canonical owner primitive
`beta` is compatible with the five subsets `I_a`.  There is no longer an
unlocated complementary owner term: its entire available payment is the
explicit adjacent gauge (827).

## 264. Component-parity data alone has arbitrary color lifts

The affine owner equation (828) does not by itself constrain which exterior
color receives the strict export at a root.  Let `W` be the binary vector
space on the outside incidence components and let

```text
aug:W -> F_2,       aug(v)=sum_(j != 0)v(j).
```

By (819), exactly one exterior color has odd local augmentation at each
root.  Equivalently,

```text
aug(gamma_i)=1.                                      (830)
```

This also follows directly from (828): `aug(beta_i)=0` by (826), while the
number of odd incidence components outside the odd component `V_0` is odd,
so `aug(s)=1`.

Now prescribe an arbitrary exterior color `a_i` at each of the five roots.
At the abstract component-vector level set

```text
delta_(x_i)^(a_i):=gamma_i,
delta_(x_i)^a:=0                    for a != a_i.      (831)
```

Then the color sum is exactly `gamma_i`; the distinguished row has odd
augmentation by (830); and every other row has even augmentation.  Thus
(831) satisfies all the local color-census and owner-transfer equations
(816)--(829), for every one of the possible color distributions of the
five strict exports.

This is an affine-freedom statement, not a claim that the rows in (831) are
always realizable by an ambient graph.  It proves that root indexing,
destination-component parity, and the exact owner coboundary still do not
form a terminal obstruction when treated only as binary vectors.  A final
argument must impose the realizability information erased in (831): the
actual outside port identities in the four-port rows, their private labels,
or the cross-color owner-factor transitions linking those ports.  Further
linear manipulation of the vectors `delta_x^a,beta_i,s` alone cannot rule
out a color lift, just as the earlier affine family (75) could not rule out
a color-resolved switch matrix.

## 265. Integer SRP gives an exact outside-port partition at every root

The realizability information omitted in Section 264 is already visible
before reducing the simultaneous routing identity modulo two.  Fix
`x in C` and an actual port `p in e\Z`.  Every `A_c`-neighbor of `x` stays
in the closed owner cycle `C`, and every `R_ce`-neighbor of a root in `C`
lies in its paired incidence component `Z`.  Therefore

```text
(A_c R_ce)[x,p]=0.                                   (832)
```

Take the `(x,p)` entry of the integer identity `SRP(c,e)`.  Using (832)
gives the pointwise equation

```text
(R_ce A_e)[x,p]
 +sum_(a != c,e)(R_ca R_ae)[x,p]=1.                  (833)
```

All summands are nonnegative integers.  Consequently exactly one term in
(833) is one and every other term is zero.  Thus the identity records an
actual owner/color assignment of every outside port, not merely a parity
relation.

To state the resulting partition, define

```text
D_x^a:=supp((R_ca R_ae)[x,-])\Z,
B_x:=supp((R_ce A_e)[x,-])\Z.                        (834)
```

The four-port-row argument of (809) applies to every exterior color.  The
unique color `a_x` receiving the strict export at `x` has `|D_x^(a_x)|=3`;
every other exterior color has `|D_x^a|=4`.  Moreover `B_x` consists of the
`A_e`-neighbors of the two selected ports incident to `x`.  Each selected
port has two such neighbors outside `Z` by `e_e(Z)=0`, and the two pairs
are disjoint: a common neighbor together with the two selected ports and
`x` would make a four-cycle.  Hence `|B_x|=4`.

Equation (833) now gives the disjoint set partition

```text
e\Z = B_x disjoint_union
      disjoint_union_(a != c,e) D_x^a.               (835)
```

The parity profiles `beta` and `delta` are exactly the projections of the
sets in (834) to the incidence-component index.  Thus (828) is the mod-two
shadow of (835), while (835) restores the actual port identity that the
arbitrary lift (831) was free to ignore.  At each private root the owner
channel and all exterior routing colors do not merely balance: they divide
the entire outside target fiber into uniquely assigned ports.  Any final
price may therefore be evaluated on this canonical labeled partition,
where reassignment of `gamma_i` to an arbitrary color is no longer allowed.

## 266. The target-owner payment has ten private ports and five return paths

The actual endpoints hidden by the binary profiles `beta_i` satisfy a much
stronger realizability condition.  Every two distinct selected ports already
have a common neighbor in the displayed five-port core.  Consecutive ports
share their incident `c`-root, while nonconsecutive ports share the
`d`-owner supplied by the complementary five-cycle normal form used in
Section 253.  Therefore two selected ports cannot also share an
`A_e`-neighbor: that vertex and the already displayed common neighbor would
give a four-cycle.

Together with `e_e(Z)=0`, this proves that the ten owner endpoints

```text
B:=disjoint_union_(i mod 5) N_(A_e)(p_i)
```

are ten distinct vertices, all outside `Z`:

```text
|B|=10,
N_(A_e)(p_i) intersect N_(A_e)(p_h)=emptyset for i!=h.  (836)
```

Thus each vertex of `B` is incident to exactly one of the ten cut edges
from `Z`; no outside endpoint is reused by two selected ports.  This is the
port-identity information erased when (825) records only the parity of the
incidence component containing an endpoint.

There is also a canonical return pairing on these private endpoints.  The
internal owner graph `A_e` is a disjoint union of cycles.  Delete the five
independent vertices `Z`.  In every `A_e`-cycle meeting `Z`, the remaining
boundary-bearing components are paths whose endpoints lie in `B`.  A cycle
containing `r` selected ports produces exactly `r` such paths.  Summing over
the cycles, there are exactly five boundary-bearing paths, and hence a
fixed-point-free involution

```text
nu_e:B -> B                                             (837)
```

which pairs the two endpoints of each outside owner path.  Untouched
`A_e`-cycles contain no vertex of `B` and play no role in this pairing.

Equivalently, contract each of the five outside paths and remember which
selected port is adjacent to each endpoint.  The result is a 2-regular
pseudograph `K_e` on the five labeled ports:

```text
V(K_e)=Z,          |E(K_e)|=5,          deg_(K_e)(p_i)=2.  (838)
```

A loop means that an `A_e`-cycle contains only that one selected port, and
two parallel return edges mean that it contains exactly two; neither is
excluded here.  Formula (838) is simply the cycle decomposition of `A_e`
with the actual outside paths retained, not a new parity relaxation.

This is the first target-owner refinement beyond the affine no-go of
Section 264.  The complementary payment is not an arbitrary collection of
even component vectors: it is the projection of ten distinct port
identities paired by the five concrete paths (837).  A terminal argument
may now seek incompatibility between this owner-return involution and the
private exterior-label paths `u_i--z_i--v_i`.  The present section does not
assert that every 2-regular pseudograph in (838) is impossible or that the
pairing already respects the receiving colors.

## 267. Every private owner endpoint carries a three-root routing word

The exact partition (835) determines how the ten vertices in (836) are
seen from all five roots.  Write

```text
T_h:=N_(A_e)(p_h),          |T_h|=2.
```

Since the selected port `p_h` is incident in `R_ce` to exactly the two
roots `x_h,x_(h+1)`, an endpoint `w in T_h` belongs to

```text
B_(x_h) and B_(x_(h+1)).                              (839)
```

At those two root--port pairs the unique intermediate layer in integer SRP
is the endpoint color `e`.  For every other root, `w` is absent from its
four-element owner set `B_x`; equation (835) therefore puts it in exactly
one exterior routing set.  In symbols, there are unique exterior colors
`a_i(w)` for

```text
i notin {h,h+1}
```

such that

```text
w in D_(x_i)^(a_i(w)).                               (840)
```

Thus every private owner endpoint has a canonical three-root exterior-color
word supported on

```text
C\{x_h,x_(h+1)}.                                     (841)
```

This is an actual routing word, not a component parity: each letter records
the unique intermediate component of the root--port pair `(x_i,w)`.
Equivalently, at a fixed root `x_i`, its owner block
`B_(x_i)=T_(i-1) disjoint_union T_i` contains four of the ten private
endpoints, while the other six occur in uniquely colored exterior sets
`D_(x_i)^a`:

```text
|B\B_(x_i)|=6.                                       (842)
```

The return involution `nu_e` from (837) now pairs ten such three-letter
words along five concrete outside `A_e` paths.  Any terminal compatibility
test can therefore compare the exterior colors at their six routed root
occurrences before projecting to `delta` or `beta`; neither endpoint
identity nor the owner-return pairing has to be reconstructed from parity.

## 268. The three-root routing words are necessarily nonmonochromatic

The words in Section 267 retain still more actual-label information.  Fix
`w in T_h`, and for each `i notin {h,h+1}` let `y_i(w)` be the unique
intermediate label in the cell `(x_i,w)` of color `a_i(w)`.  The three
labels are distinct: Section 252 proved that every exterior label has at
most one neighbor in `C`, whereas these labels meet three different roots.
Thus `w` carries the label-refined ticket

```text
tau(w):=(a_i(w),y_i(w))_(i notin {h,h+1}).           (843)
```

This ticket cannot be monochromatic.  For a fixed exterior color `a`, the
cross block `R_ae` gives `w` exactly two neighbors in `a`.  Three cells of
color `a` would require the three distinct labels `y_i(w)` to be three such
neighbors.  Consequently

```text
max_a |{i notin {h,h+1}:a_i(w)=a}| <= 2.             (844)
```

The color pattern of every private owner endpoint is therefore `2+1` or
`1+1+1`, never `3`.  Across the ten endpoints this yields thirty actual
exterior label occurrences, grouped into ten nonmonochromatic tickets:

```text
sum_(w in B) |tau(w)|=30.                            (845)
```

This is a realizability constraint absent from the arbitrary
component-vector lift (831).  The unresolved step is to compare the
tickets at the two endpoints paired by an outside `A_e` path, or to tie one
of their labels to the strict paths `u_i--z_i--v_i`; no compatibility of
paired tickets is asserted here.

## 269. Every residual port forces three exterior colors

The ten private owner endpoints do not exhaust the outside target fiber.
Define the residual set

```text
O:=e\(Z union B).
```

The three sets are disjoint, `|e|=2q`, `|Z|=5`, and `|B|=10`, so

```text
|O|=2q-15.                                           (846)
```

Fix `w in O`.  Since `w` belongs to none of the sets `T_h`, it belongs to
no owner block `B_(x_i)`.  The exact partition (835) therefore assigns the
cell `(x_i,w)` to a unique exterior routing color at **every** one of the
five roots.  Let `a_i(w)` be that color and `y_i(w)` its unique intermediate
label:

```text
x_i -- y_i(w) -- w,          i in Z/5.               (847)
```

The five labels in (847) are distinct.  Each meets a different root in
`C`, while the pointwise bound (779) allows an exterior label at most one
neighbor in `C`.  On the other hand, `w` has exactly two neighbors in each
exterior component.  Hence no exterior color can occur more than twice in
the five-root word:

```text
max_a |{i:a_i(w)=a}| <= 2.                           (848)
```

It follows that every residual port uses at least three exterior colors;
its multiplicity pattern is one of

```text
2+2+1,       2+1+1+1,       1+1+1+1+1.              (849)
```

There are `r=q/2` component colors in total and only `r-2` exterior to the
fixed endpoints `c,e`.  Therefore the existence of a five-port curl with
`O` nonempty forces

```text
r-2>=3,       equivalently q>=10.                    (850)
```

In the binary-power regime this sharpens to `q>=16`.  In particular the
uniform five-root word mechanism immediately excludes the `q=8`
(order-64) specialization: there `|O|=1` but only two exterior colors are
available, contradicting (848).  This is a q-generic corollary of integer
SRP and the five-port geometry, not an order-64 census or certificate
calculation.  For larger `q`, (847)--(849) supply `5(2q-15)` further actual
label occurrences which any remaining owner-return construction must
realize.

## 270. Each receiving color has an exact global ticket load

The private-endpoint tickets and residual words admit a colorwise load law.
Fix an exterior color `a`, and let

```text
b_a:=|{(x,w) in C times B: the cell (x,w) has color a}|,
o_a:=|{(x,w) in C times O: the cell (x,w) has color a}|.  (851)
```

The routing layer `Q_a=R_ca R_ae` has row sum four.  Its restriction to the
five selected roots therefore contains exactly twenty cells.  The target
fiber is the disjoint union `Z disjoint_union B disjoint_union O`.  On `Z`,
Section 252 showed that the only exterior cells are the five strict exports,
and color `a` receives exactly `k_a` of them.  The cells over `B` and `O`
are precisely the occurrences counted in (851).  Consequently

```text
k_a+b_a+o_a=20.                                      (852)
```

In particular, if the actual outside-port load of color `a` is

```text
L_a:=b_a+o_a,
```

then

```text
L_a=20-k_a.                                          (853)
```

This recovers the export population from a global load scalar without
remembering arbitrary endpoint names.  A nonreceiving exterior color has
load twenty; a color receiving `k_a` strict exports has load exactly
`20-k_a`.  Summing (852) over all exterior colors gives the consistency
check

```text
sum_a k_a=5,       sum_a b_a=30,
sum_a o_a=5(2q-15),
sum_a(k_a+b_a+o_a)=20(q/2-2).                        (854)
```

The middle identities are the thirty letters of Section 268 and the five
letters at each residual port from Section 269.  Both sides of the last
identity equal `10q-40`.

Equation (853) is the five-port realization of the information boundary
seen independently in the B.3 label-compression audit: literal private
names are unnecessary once one retains the global fiber load together with
the local role census.  It is not yet a contradiction, because (853) does
not determine how `L_a` splits between `B` and `O`, nor how the `B` tickets
are paired by `nu_e`.  Those are now the only owner-return data still absent
from the colorwise load.

## 271. Each color load has a canonical root-pairing graph

The scalar load in Section 270 has an exact portwise geometry.  Fix an
exterior color `a` and form the bipartite graph `G_a^C` whose left vertices
are the five roots `C`, whose right vertices are the actual ports in `e`,
and whose edges are the cells in the restricted routing layer

```text
Q_a^(c,e)|_(C times e).
```

Every left degree is four.  On the selected side `Z`, (777) gives exactly
the `k_a` strict cells, in distinct rows and columns, so each used selected
column has degree one.  An arbitrary port column has degree at most two:
the port has only two `a`-neighbors, and (779) lets each such intermediate
label meet at most one root of `C`.  Therefore

```text
deg_(G_a^C)(x_i)=4,
deg_(G_a^C)(p)<=2,
G_a^C[C,Z] is a k_a-edge matching.                  (855)
```

Delete the selected columns `Z`.  The remaining root degrees are

```text
deg_(G_a^C-Z)(x_i)=4-1_{i in I_a}.                  (856)
```

Every outside port of degree two now canonically pairs the two distinct
roots in its neighborhood; every degree-one port is a boundary stub.  If
`m_1^a,m_2^a` count outside ports of degrees one and two, respectively,
the load law (853) becomes

```text
m_1^a+2m_2^a=20-k_a,
m_1^a=k_a mod 2.                                    (857)
```

Equivalently, contracting every degree-two port produces a loopless
multigraph on the five labeled roots, together with `m_1^a` labeled stubs,
whose vertex degrees are (856).  Multiple root-pair edges are not excluded.
This is strictly finer than the number `L_a=20-k_a`: it records which
actual ports pair two root occurrences and which terminate.  The private
ticket occurrences in `B` and `O` are the distinguished labeled edges and
stubs of these colorwise graphs, providing a direct combinatorial interface
with the owner-return pairing `nu_e`.

## 272. Global load plus the local three-role census is exact

The rootwise role data underlying Sections 270--271 can be stated without
retaining arbitrary port names.  For every root index and exterior color
put

```text
epsilon_i^a:=1_{i in I_a},
b_i^a:=|D_(x_i)^a intersect B|,
o_i^a:=|D_(x_i)^a intersect O|.                      (858)
```

The set `D_(x_i)^a` is the outside part of the four-port row of color `a`.
It has size three when the row contains the unique strict selected cell and
size four otherwise.  Since `B` and `O` partition the outside target ports,
this gives the exact local role equation

```text
epsilon_i^a+b_i^a+o_i^a=4.                          (859)
```

At a fixed root, four of the ten private endpoints form the owner block
`B_(x_i)=T_(i-1) disjoint_union T_i`; the other six are assigned by integer
SRP to exterior colors.  Every residual port is exterior-routed there.
Therefore the root margins are

```text
sum_a epsilon_i^a=1,
sum_a b_i^a=6,
sum_a o_i^a=|O|=2q-15.                              (860)
```

The color margins recover the global census exactly:

```text
sum_i epsilon_i^a=k_a,
sum_i b_i^a=b_a,
sum_i o_i^a=o_a,
k_a+b_a+o_a=20.                                     (861)
```

Thus each exterior color has a canonical five-row local role table

```text
(epsilon_i^a,b_i^a,o_i^a)_(i mod 5)
```

together with the global load `L_a=20-k_a`; either determines the missing
row entry through (859), and all row and column margins are fixed by
(860)--(861).  In the colorwise pairing graph of Section 271, `b_i^a` and
`o_i^a` distinguish whether an incident edge or stub uses a private owner
endpoint or a residual port.

This is precisely the invariant class suggested by the independent B.3
compression experiments: global fiber load plus local role geometry, with
literal label names discarded.  The analogy does not import the finite B.3
certificate into this setting.  The remaining uniform task is to impose
the realizability constraints that the table alone omits--the
nonmonochromatic ticket caps (844), the residual caps (848), and the
return pairing `nu_e` on the `B` occurrences.

## 273. The root-pairing graph is a ten-edge owner-factor subgraph

The pairing geometry in Section 271 is realized inside a canonical
two-factor, rather than being an abstract contraction.  Fix an exterior
color `a`.  The pointwise bound (779), the two `a`-neighbors at each root,
and the five roots show that exactly ten `a`-labels meet `C`, each at a
unique root.  Every such label `y` indexes the edge of the owner factor
`F_a[e]` whose endpoints are the two ports in `N_e(y)`.

Let `H_a^C` be the subgraph of `F_a[e]` consisting of these ten indexed
edges.  They are distinct: two labels indexing the same pair of ports would
give those ports two common `a`-neighbors and hence a four-cycle.  Exactly
two edges carry each root label `x_i`.  Start with the edge--vertex
incidence graph of `H_a^C` and merge the two edge-nodes carrying the same
root label; the result is precisely the routing graph `G_a^C` of
Section 271.  In particular, the degree of every port is unchanged by this
merger.  Since `F_a[e]` is two-regular,

```text
H_a^C is a disjoint union of paths and cycles,
|E(H_a^C)|=10.                                      (862)
```

Its degree-one vertices are also completely identified.  On `Z`, the only
incidences are the `k_a` strict-export cells, in distinct ports.  Outside
`Z`, they are exactly the `m_1^a` stubs of (857).  Thus

```text
|{p:deg_(H_a^C)(p)=1}|=k_a+m_1^a.                   (863)
```

Every path component has two endpoints and every cycle component has none,
so the number of path components is

```text
(k_a+m_1^a)/2.                                      (864)
```

Following each path gives a canonical fixed-point-free pairing of the
`k_a` selected strict ports and the `m_1^a` outside stubs.  A pair may be
selected--selected, selected--outside, or outside--outside; none of these
types is excluded yet.  The internal edges of the path retain their private
root labels, two occurrences of each root across the whole subgraph.

This owner-factor path pairing is the actual realization constraint behind
the parity `m_1^a=k_a mod 2`.  Together with the target-owner return pairing
`nu_e` on the ten ports `B`, it supplies two concrete pairing systems on the
same ticket data: one follows `A_e` outside paths, while the other follows
the color-`a` factor `F_a[e]` through the ten labels meeting `C`.

## 274. The owner-factor paths have a proper five-root edge coloring

The private root labels on `H_a^C` obey a pointwise separation law.  Let
`y_i^0,y_i^1` be the two `a`-neighbors of a fixed root `x_i`; these index
the two edges of `H_a^C` colored by `x_i`.  Their port-neighborhoods are
disjoint.  Indeed, a shared port `p` would make `x_i` and `p` have the two
common neighbors `y_i^0,y_i^1`, contrary to `C_4`-freeness.  Therefore

```text
N_e(y_i^0) intersect N_e(y_i^1)=emptyset.            (865)
```

Consequently the two occurrences of every root color are nonadjacent edges
of `H_a^C`.  At any degree-two port, the two incident edges carry distinct
root colors.  Thus the ten-edge path/cycle system has a proper edge coloring
by the five roots in which every color occurs exactly twice:

```text
each x_i colors two nonadjacent edges of H_a^C.       (866)
```

In particular every path and cycle component of (862) has a root word with
no equal consecutive letters, while the concatenation over all components
uses each of the five letters twice.  For `i in I_a`, one of the two
`x_i`-colored edges is the strict edge incident to its selected port and
the other lies wholly outside `Z`; (865) keeps their port supports private.

This is a finite realizability constraint absent from both the load scalar
and the local table (858): those data remember how many occurrences have
each role, but not that the two occurrences of one root can never meet at a
port.  The endpoint pairing (864) must therefore be realizable by properly
colored path words with prescribed strict endpoint letters.

## 275. Every odd receiving color has a strict-to-outside owner path

The endpoint pairing in Section 273 forces an actual escape whenever the
strict-export population is odd.  For a fixed exterior color `a`, classify
the path components of `H_a^C` by the locations of their two endpoints.
Let

```text
n_ZZ^a,       n_Zo^a,       n_oo^a
```

count selected--selected, selected--outside, and outside--outside paths,
respectively.  Counting the selected and outside degree-one endpoints gives

```text
k_a   =2n_ZZ^a+n_Zo^a,
m_1^a =2n_oo^a+n_Zo^a.                              (867)
```

Consequently

```text
n_Zo^a = k_a = m_1^a mod 2.                         (868)
```

In particular, if `k_a` is odd, then `n_Zo^a` is odd and nonzero.  At least
one canonical path in the actual owner factor `F_a[e]` starts at a strict
selected port and ends at an outside degree-one stub.

This occurs in every five-port distribution.  The nonzero populations
`k_a` sum to five, so at least one receiving color has odd `k_a`.  In the
monochromatic branch that unique color has `k_a=5`; although its active
boundary `partial H_a` closes by (800), its owner-factor subgraph has an odd
number of selected--outside paths:

```text
there exists a receiving color a and an H_a^C path
p_(i+2) -- ... -- w,       p_(i+2) in Z, w in e\Z.   (869)
```

The first edge of this path is indexed by the strict label `z_i`: it is the
unique edge of `H_a^C` incident to the selected endpoint `p_(i+2)`.  The
last edge is indexed by the unique `a`-label meeting `C` at the outside
degree-one port `w`.

The terminal port `w` belongs either to `B` or to `O`.  In the first case it
has the three-root ticket of Section 267; in the second it has the five-root
word of Section 269.  Because its degree in `H_a^C` is one, color `a` occurs
exactly once in that word:

```text
|{h:a_h(w)=a}|=1.                                   (870)
```

Thus the odd destination profile of Section 260 no longer escapes into an
anonymous component.  At least one strict occurrence continues through a
finite, private-label path in `F_a[e]` to a located outside port carrying a
single `a`-role in an already classified ticket.  This is not yet a
contradiction: the next composition must compare that terminal role with
the target-owner return pairing `nu_e` when `w in B`, or with the residual
five-root word when `w in O`.

## 276. The color-factor path boundaries cover every port oddly

The tickets of Sections 268--269 are exactly the local degrees in the
owner-factor subgraphs.  For an outside port `w` and exterior color `a`,
each occurrence of color `a` in the root word of `w` is one edge of
`H_a^C` incident to `w`.  Hence

```text
deg_(H_a^C)(w)
 =|{i in Z/5: the cell (x_i,w) has color a}|.         (871)
```

At a private owner endpoint `w in B`, a ticket of type `2+1` therefore
makes `w` an internal degree-two vertex in the doubled color and a path
endpoint in the singleton color.  A ticket of type `1+1+1` makes it a path
endpoint in three colors.  At a residual port `w in O`, the three patterns
in (849) make it a path endpoint in respectively one, three, or five
exterior colors.  In every case the number of color-factor boundaries
containing `w` is odd.

The same holds on `Z`: each selected port supports exactly one strict
exterior cell by (777), so it is a degree-one vertex of exactly one
`H_a^C`.  Writing `partial H_a^C` for the mod-two degree boundary on the
port vertex set, the pointwise statement over the whole target fiber is

```text
sum_(a != c,e) partial H_a^C = 1_e.                  (872)
```

The right side has even weight `2q`, consistently with every graph
boundary having even weight.  Equation (872) is not a scalar contradiction;
it is an exact boundary cover by the canonical path systems of (864).  It
ties the local ticket roles to those path pairings without retaining an
arbitrary label name: every actual port must be paired as an endpoint in an
odd number of exterior owner factors, while doubled ticket colors pass
through it internally.

## 277. The exterior factor edges split into five rootwise matchings

The boundary cover (872) has an exact integral refinement before the root
colors are forgotten.  For each selected root `x_i`, let `M_i` be the union,
over all exterior colors `a`, of the two edges of `H_a^C` carrying the root
label `x_i`.

Within one color those two edges have disjoint endpoints by (865).  Across
different colors their endpoint sets are also disjoint: they are the
supports of the disjoint routing-layer rows in integer SRP.  Hence `M_i` is
a matching.  The endpoint layers locate its uncovered ports exactly.
The root-owner row occupies the four selected ports other than
`p_(i+2)`, while the target-owner row occupies
`B_(x_i)=T_(i-1) disjoint_union T_i`.  Therefore

```text
V(M_i)
 ={p_(i+2)} disjoint_union ((e\Z)\B_(x_i)),
|V(M_i)|=2q-8,          |E(M_i)|=q-4.                (873)
```

Thus `M_i` is a perfect matching on its displayed actual-port support.  The
edge count also equals two edges for each of the `q/2-2` exterior colors.

The five matching supports have a rigid multiplicity profile.  A selected
port `p_j` occurs only in `M_(j-2)`.  A private owner endpoint `w in T_h`
is omitted precisely from `M_h` and `M_(h+1)`, whose owner blocks contain
it, and occurs in the other three.  A residual port belongs to every
matching.  Hence

```text
sum_i 1_(V(M_i))(w)
 = 1,  w in Z;
 = 3,  w in B;
 = 5,  w in O.                                      (874)
```

Equivalently, the multigraph union

```text
M:=M_0 multiset_union ... multiset_union M_4
```

is properly edge-colored by the five root labels and has integer vertex
degrees

```text
deg_M(w)=1_Z(w)+3 1_B(w)+5 1_O(w).                  (875)
```

Reducing (875) modulo two recovers (872): every vertex has odd degree.
The integer handshake is consistent and exact,

```text
sum_w deg_M(w)=5+30+5(2q-15)=10q-40
              =2 sum_i |E(M_i)|.                    (876)
```

This matching factorization retains the rootwise pairing that the boundary
sum erased.  The surviving realization problem can now be phrased as a
two-axis decomposition of `M`: by root it is the five fixed-support
matchings `M_i`; by exterior color it is the properly root-colored
ten-edge path/cycle system `H_a^C`.  Any terminal incompatibility must use
the coherence of these two decompositions together with the target-owner
return pairing `nu_e`; neither axis separately is contradictory.

## 278. The two-axis union is a simple doubly colored graph

The multigraph qualifier in (875) is unnecessary for the realized union.
No port pair can support two distinct edges among all the subgraphs
`H_a^C`.  Such edges would be indexed by two distinct intermediate labels
which are both common neighbors of the same two ports, creating a
four-cycle.  The same label cannot occur in two root matchings because
(779) gives it at most one neighbor in `C`.  Therefore

```text
K:=union_(i mod 5) M_i=union_(a != c,e) H_a^C
```

is a simple graph on the actual target fiber `e`.  Its exact degree
sequence is inherited from (875):

```text
deg_K(w)=1 on Z,       3 on B,       5 on O,         (877)
```

and hence

```text
|E(K)|=5(q-4).                                        (878)
```

Every edge has two canonical labels.  Its root label `i` records the
matching `M_i`, and these five classes are proper matchings of `q-4` edges.
Its exterior label `a` records the factor subgraph `H_a^C`; each exterior
class has ten edges, exactly two in every root matching:

```text
|M_i intersect H_a^C|=2.                             (879)
```

Within an exterior class the root coloring is proper by (866), and the
class decomposes into the paths and cycles of (862).  Thus the remaining
five-port data is a doubly colored **simple** graph with fixed degree
classes `(1,3,5)`, fixed root-color matching sizes, fixed exterior-color
loads, prescribed strict endpoints, and the independent return pairing
`nu_e` on `B`.  This formulation removes artificial parallel-edge freedom
from the finite compatibility problem while retaining both decompositions.

## 279. Composing the two pairing systems forces an escape into `O`

The path pairing from Section 273 and the target-owner return pairing from
Section 266 have a global parity consequence which neither has separately.
For every exterior color `a`, contract each path component of `H_a^C` to
one edge between its two degree-one endpoints; discard its cycle components.
Let `P` be the multigraph union of these endpoint-pairing edges over all
exterior colors.  At a port `w`, its degree in `P` is the number of colors
for which `w` belongs to `partial H_a^C`.  Equation (872) therefore gives

```text
deg_P(w)=1 mod 2             for every w in e.        (880)
```

Now add the five edges of the target-owner return matching `nu_e` on the
ten private endpoints `B`, retaining multiplicity if an endpoint-pair edge
happens to coincide.  Put

```text
Pi:=P multiset_union nu_e.
```

The matching flips the degree parity exactly on `B`.  Hence the odd-degree
vertices of `Pi` are precisely

```text
Odd(Pi)=Z disjoint_union O.                          (881)
```

Every connected component of a finite multigraph contains an even number
of odd-degree vertices.  Since `|Z|=5` is odd, not every component meeting
`Z` can have all its odd vertices in `Z`: otherwise those components would
partition `Z` into even-sized sets.  Consequently

```text
some component of Pi contains a port of Z and a port of O. (882)
```

Choose a path in that component between such ports and expand every `P`
edge back to its canonical path in one `H_a^C`, and every `nu_e` edge back
to its outside `A_e` return path.  This gives a concrete composed route
from a selected port to a residual port.  The selected endpoint has only
one incident `P` edge, whose expanded first factor edge is its strict
export edge.  At the residual endpoint, the final `P` edge belongs to a
color in which that port has degree one, so that color occurs exactly once
in its five-root word.

Thus the strict-to-outside escape of Section 275 can be continued globally
past all private `B` terminals: after composing the two actual pairing
systems, at least one strict occurrence reaches a located residual port in
`O` with a singleton exterior-color role.  No alternation of edge types
along the chosen path is asserted; the invariant is the forced `Z`--`O`
connectivity after the owner-return edges evenize every vertex of `B`.

## 280. The composed escape has an uncontracted owner-edge realization

The matching `nu_e` in Section 279 can be replaced by the full outside
owner graph, retaining every intermediate residual port.  Let

```text
J_e:=A_e[e\Z]
```

be the subgraph induced after deleting the five selected ports.  Every
private endpoint in `B` has exactly one `A_e`-neighbor in `Z`, and the ten
endpoints are distinct, so it has exactly one remaining neighbor in `J_e`.
A residual port lies in none of the sets `T_i`, hence has no `A_e`-neighbor
in `Z` and retains both of its owner neighbors.  Therefore

```text
deg_(J_e)(w)=1 for w in B,
deg_(J_e)(w)=2 for w in O.                           (883)
```

Keep the endpoint-pairing multigraph `P` from (880), and now form

```text
Xi:=P multiset_union J_e.
```

Since every `P` degree is odd, (883) again gives the exact odd set

```text
Odd(Xi)=Z disjoint_union O.                          (884)
```

The component-parity argument of (882) applies verbatim: because the five
vertices of `Z` cannot be partitioned into even-sized odd-vertex sets
without mixing with `O`,

```text
some component of Xi contains both Z and O.          (885)
```

A path between them now uses only endpoint-pairing edges from `P` and
actual outside `A_e` edges.  Expanding each `P` edge into its color-factor
path produces a completely uncontracted route in the union of the realized
owner-factor systems.  It begins with the unique strict edge at its selected
port and ends with a singleton-color edge at a residual port, exactly as in
Section 279, but it also records every residual vertex traversed inside the
target-owner return paths.  Thus later local constraints may be applied at
those intermediate `O` vertices rather than only at the contracted
endpoints in `B`.

## 281. The return matching carries an odd path-length holonomy

The contraction to `nu_e` in Section 266 discards one further binary datum:
the parity of the residual ports inside each return path.  Write the five
boundary-bearing components of `A_e\Z` as

```text
R_s,       s=1,...,5,
```

with endpoints in `B`, and let

```text
lambda_s:=|V(R_s) intersect O| mod 2.                (886)
```

These are exactly the internal vertices of the path, because its two
endpoints lie in `B`.  Every other component of `A_e\Z` is an untouched
cycle lying wholly in `O`: vertices of `B` have degree one after deleting
`Z`, whereas vertices of `O` retain degree two.  Consequently the residual
set has the disjoint decomposition

```text
O = disjoint_union_s (V(R_s) intersect O)
    disjoint_union disjoint_union_(Q an untouched cycle) V(Q).    (887)
```

Since `|O|=2q-15` is odd, reducing (887) modulo two gives

```text
sum_(s=1)^5 lambda_s
 + |{Q: Q is an untouched odd A_e-cycle}| = 1 mod 2.  (888)
```

Thus one of two owner-holonomy outcomes is unavoidable:

```text
there is an odd A_e-cycle entirely inside O;
or, if every untouched cycle is even, an odd number of the five
nu_e return paths contain an odd number of internal O ports.       (889)
```

In the second branch, transport `lambda_s` to the corresponding edge of
the return pseudograph `K_e` on the five selected ports from (838).  The
five edge marks then have odd total.  Loops and parallel return edges remain
allowed; the mark belongs to the actual expanded path, so it distinguishes
parallel edges canonically.

Equation (888) is not implied by the unmarked matching used in Section 279.
It records where the odd cardinality of the terminal set `O` lives in the
target-owner geometry: either on a closed odd owner cycle already disjoint
from the curl, or as odd holonomy on the five return edges through which the
strict-to-`O` route is composed.  A final price may therefore split on this
explicit dichotomy instead of treating `nu_e` as an arbitrary matching.

## 282. Return holonomy produces an odd residual shore crossed by every root

The two branches of (889) have a common formulation on actual residual
ports.  If there is an untouched odd `A_e`-cycle in `O`, let `S` be its
vertex set.  Otherwise every untouched cycle is even, so (888) makes at
least one return-path mark `lambda_s` equal to one; let `S` be the internal
`O` vertices of that path.  In both cases

```text
S subset O,             |S|=1 mod 2.                 (890)
```

The target-owner boundary of `S` is located.  In the cycle branch it is
empty.  In the path branch the marked path has two endpoints in `B`, and
the internal vertices form one interval, so its `A_e` cut consists exactly
of the two endpoint edges:

```text
|delta_(A_e)(S)|=0 or 2,                             (891)
```

with the two-edge case attached to one identified return edge of `K_e`.

Every residual port belongs to the support of every root matching `M_i` by
(873)--(874).  Thus each vertex of `S` has degree one in `M_i`.  Handshaking
inside `S` gives, for all five roots,

```text
|delta_(M_i)(S)|
 = |S|-2|E(M_i[S])|
 =1 mod 2,                 i in Z/5.                 (892)
```

Hence the composed owner escape does not terminate at one anonymous
residual ticket.  It produces a located odd residual shore which every one
of the five private root matchings crosses oddly, while its genuine
`A_e`-owner boundary is either closed or a single identified two-edge
attachment.  Equation (892) is the recursive export datum available for a
terminal price: the new shore simultaneously retains root identity,
actual port identity, and the return-holonomy branch.

## 283. The residual matching cuts have an odd color-resolved export

The five odd cuts in (892) can be resolved simultaneously by exterior
color.  For every root and exterior color define

```text
chi_i^a:=|delta_(M_i intersect H_a^C)(S)| mod 2.     (893)
```

The exterior-color edge classes partition the matching `M_i`.  Therefore
(892) gives an odd row sum at every root:

```text
sum_(a != c,e) chi_i^a=1,          i in Z/5.         (894)
```

Summing the five rows shows that the total number of marked matrix entries
is odd.  Hence an odd number of exterior-color columns have odd sum.  For a
fixed color, its root-labeled edge classes partition `H_a^C`, so the column
sum is exactly its factor cut:

```text
sum_(i mod 5) chi_i^a
 =|delta_(H_a^C)(S)| mod 2.                         (895)
```

Consequently there exists an exterior color `a` with

```text
|delta_(H_a^C)(S)|=1 mod 2,                         (896)
```

and the root-index set

```text
J_a:={i:chi_i^a=1}
```

is nonempty and odd.  Thus the new residual shore does not export only an
uncolored five-fold parity.  At least one actual exterior owner factor has
an odd cut across it, supported on an explicit odd subset of the five root
matchings.  This is the color-resolved recursive analogue of the strict
export that initiated the five-port analysis, now located entirely on
actual ports in `O` and tied to the holonomy shore from Section 282.

## 284. An odd residual factor cut exports a nonzero reverse tag

Fix a color `a` satisfying (896).  Because `H_a^C` has port degrees at most
two, the parity of its cut across `S` is the parity of its degree-one
vertices lying in `S`.  Put

```text
W_a(S):={w in S:deg_(H_a^C)(w)=1}.
```

Then handshaking on `S` gives

```text
|W_a(S)|=|delta_(H_a^C)(S)|=1 mod 2.                (897)
```

Every `w in W_a(S)` carries a canonical reverse routing row.  The port `w`
has exactly two `a`-neighbors, say `y_w^0,y_w^1`.  Its degree one in
`H_a^C` means that exactly one of these labels meets `C`, at exactly one
root by (779); the other label meets no root of `C`.  Their two-element
`c`-neighborhoods are disjoint.  A common root would make that root and
`w` have the two common `a`-neighbors `y_w^0,y_w^1`, contrary to
`C_4`-freeness.  Hence

```text
E_w^a:=(N_c(y_w^0) disjoint_union N_c(y_w^1))\C,
|E_w^a|=3.                                           (898)
```

This is the exact reverse analogue of the three-port destination set
`D_i^a` in (811): there are four distinct roots in the full reverse row,
exactly one selected and three outside the selected incidence component.

Let `(U_j,V_j)` be the incidence components of `R_ce`, with `U_0=C`, and
for `j!=0` define

```text
rho_w^a(j):=|E_w^a intersect U_j| mod 2.             (899)
```

The outside root components partition `c\C`, so every singleton terminal
has odd augmentation:

```text
sum_(j!=0) rho_w^a(j)=1.                             (900)
```

Aggregate over the odd set of singleton terminals,

```text
Rho_a(S):=sum_(w in W_a(S)) rho_w^a.
```

Equations (897) and (900) give

```text
aug(Rho_a(S))=|W_a(S)|=1,
so Rho_a(S)!=0.                                      (901)
```

Thus the residual owner shore does not merely have a nonzero color cut.
In one actual exterior color it exports an odd, component-resolved
three-root tag back to the opposite side `c\C`.  The composed route from
Sections 279--283 has therefore returned to the same kind of nonvanishing
destination ledger with which Section 259 began, but now without a closed
five-port target.  A terminal price must identify why this reverse tag
cannot be absorbed by the ordinary outside incidence components, or show
that iterating these located tags creates forbidden owner holonomy.

## 285. The full owner factor forces an odd inactive-label payment

The odd cut in (896) cannot terminate inside the ten `C`-active edges.
For its exterior color `a`, decompose the full owner factor as

```text
F_a[e]=H_a^C disjoint_union Hbar_a^C,                (902)
```

where `Hbar_a^C` consists of the factor edges indexed by `a`-labels which
do not meet `C`.  The indexing is exact: every `a`-label indexes one
`F_a[e]` edge, and (779) identifies the ten labels meeting `C` precisely
with the edges retained in `H_a^C`.

The graph `F_a[e]` is two-regular.  Therefore every vertex shore has an
even cut:

```text
|delta_(F_a[e])(S)|=0 mod 2.                         (903)
```

The two edge classes in (902) partition this cut.  Combining (896) and
(903) yields

```text
|delta_(Hbar_a^C)(S)|=1 mod 2.                       (904)
```

Every edge counted in (904) has one actual port in the located residual
shore `S`, one port outside it, and is indexed by a private `a`-label with
no neighbor in the original root cycle `C`.  Thus the recursive
color-resolved export forces an odd population in the complementary
`C`-inactive label channel.  The payment is now fully located at the level
of actual labels and factor edges; it is not an untagged boundary sum or an
arbitrary component-vector lift.

## 286. The reverse tag is supported on an actual odd root shore

The component vector in (901) has a canonical port-to-root realization.
Take the symmetric difference of the actual three-root sets from (898):

```text
T_a(S):=triangle_(w in W_a(S)) E_w^a subset c\C.    (905)
```

Cardinality modulo two commutes with symmetric difference.  Since every
`E_w^a` has size three and `W_a(S)` is odd by (897),

```text
|T_a(S)|
 =sum_(w in W_a(S)) |E_w^a|
 =1 mod 2.                                          (906)
```

Moreover the incidence components `(U_j,V_j)` partition `c`, and the
component projection of symmetric difference is linear.  Thus the reverse
tag is exactly the component-parity profile of this actual shore:

```text
Rho_a(S)(j)=|T_a(S) intersect U_j| mod 2,       j!=0. (907)
```

In particular some outside incidence component `U_j` contains an odd part
of `T_a(S)`.  The recursive route has therefore produced not only a
nonzero abstract destination vector but a located odd set of actual roots
outside `C`, canonically assembled from the singleton terminal labels.
This is the object on which a next owner/cut transport can act without
choosing representatives for the component tag.

## 287. Odd active and inactive cuts meet on mixed residual intervals

The two odd cut populations (896) and (904) can be composed
occurrence-by-occurrence inside the full factor `F_a[e]`.  Consider the
components of the induced shore `F_a[e][S]`.  Components which are whole
factor cycles have no cut edges.  Every other nonempty component is a path
interval with exactly two `F_a[e]` cut edges.  Classify such intervals by
whether their two boundary edges lie in the active class `H_a^C` or the
inactive class `Hbar_a^C`, and let

```text
n_AA,       n_AI,       n_II
```

be the three counts.  Every active--inactive interval is counted once,
without orienting its two ends.  Counting the two cut populations gives

```text
|delta_(H_a^C)(S)|    =2n_AA+n_AI,
|delta_(Hbar_a^C)(S)| =2n_II+n_AI.                  (908)
```

Both left sides are odd by (896) and (904).  Therefore

```text
n_AI=1 mod 2.                                       (909)
```

In particular there is an actual path interval through `S` whose one
boundary edge is indexed by an `a`-label meeting `C` and whose other
boundary edge is indexed by an `a`-label with no neighbor in `C`.  Expanding
the interval in the two-factor gives a private-label chain

```text
outside -- active a-edge -- (path through S)
        -- inactive a-edge -- outside.              (910)
```

The active boundary edge has a unique root label in `C` by (779).  If
`m_i` counts mixed intervals whose active end has root label `x_i`, then

```text
sum_(i mod 5) m_i=n_AI=1 mod 2.                     (911)
```

Thus an odd nonempty subset of the five roots occurs at the active ends of
these mixed payment intervals.

This is stronger than retaining two separate odd ledgers: an odd number of
their occurrences are joined by canonical paths inside the located
residual shore.  It is the residual analogue of the isolated
`u_i--z_i--v_i` payment paths from Section 255, with the important scope
difference that the active endpoint of a mixed interval need not be a
degree-one vertex of `H_a^C`; therefore the reverse tags of Section 284 are
not claimed to pair bijectively with these intervals.  The next price must
couple the odd root-indexed family (908) to the nonzero aggregate reverse
tag (901).

## 288. Reverse-tag terminals connect oddly to active cut occurrences

There is nevertheless a canonical parity bridge inside the active subgraph.
Let

```text
C_a(S):={w in S:
         the number of H_a^C cut edges incident to w is odd}.      (912)
```

Every cut edge has exactly one endpoint in `S`, so (896) gives
`|C_a(S)|=1 mod 2`.  The reverse-tag terminal set `W_a(S)` is odd by
(897).  Split the degree of `H_a^C` at a vertex of `S` into its internal
and cut parts.  Modulo two this gives the exact boundary identity

```text
partial(H_a^C[S])=W_a(S) triangle C_a(S).            (913)
```

The noncycle components of `H_a^C[S]` pair the vertices on the right side
by their unique internal paths.  Put `I:=W_a(S) intersect C_a(S)` and pair
each vertex of `I` to itself by a zero-length connection.  Among the
remaining internal paths let `p_WC` count those with one endpoint in
`W_a(S)\C_a(S)` and one in `C_a(S)\W_a(S)`.  Counting the former endpoint
set gives

```text
|W_a(S)\C_a(S)|=2p_WW+p_WC,
|I|+p_WC=1 mod 2.                                   (914)
```

Thus an odd number of the resulting connections join a reverse-tag
singleton terminal to an active cut occurrence, allowing a zero-length
join when the two roles occur at the same port.  In particular at least one
actual `w in W_a(S)` is connected inside `H_a^C[S]` to a port supporting
one active cut edge.  This closes the scope gap noted after (911) at the
level of parity: the reverse tags and the active ends of the residual cut
ledger are not bijective, but an odd nonempty family of canonical internal
connections links the two occurrence systems.

## 289. The two canonical pairings join reverse tags to inactive payments

The active cut occurrences can be used as internal nodes to compose the
two odd ledgers completely.  First construct the **active pairing**.  At
every vertex of `S`, retain the internal `H_a^C[S]` edges, truncate every
active cut edge to a terminal half-edge, and add one formal terminal stub
at each vertex of `W_a(S)`.  If the global `H_a^C` degree is two, no stub is
added and the retained internal/cut incidences still total two.  If it is
one, the added `W` stub raises the total to two.  Thus every nonisolated
vertex has degree two, and the resulting paths canonically pair the
terminal occurrences

```text
W_a(S) disjoint_union delta_(H_a^C)(S).              (915)
```

Second use the **factor pairing** from Section 287.  The path intervals of
the full two-factor `F_a[e]` through `S` canonically pair all terminals in

```text
delta_(H_a^C)(S)
 disjoint_union delta_(Hbar_a^C)(S).                 (916)
```

Now overlay the two pairing systems, identifying the two copies of each
active cut-edge occurrence.  Every active occurrence has degree two in the
overlay, one edge from each pairing.  The only degree-one vertices are the
reverse-tag stubs `W_a(S)` and the inactive cut-edge occurrences
`delta_(Hbar_a^C)(S)`.  Consequently every noncycle component is a path of
type `W--W`, `W--I`, or `I--I`.

Let their counts be `N_WW,N_WI,N_II`.  Endpoint counting gives

```text
|W_a(S)|                         =2N_WW+N_WI,
|delta_(Hbar_a^C)(S)|            =2N_II+N_WI.        (917)
```

Both left sides are odd by (897) and (904), so

```text
N_WI=1 mod 2.                                        (918)
```

Hence an odd nonempty family of canonical occurrence paths joins actual
reverse-tag singleton terminals to actual cut edges indexed by
`C`-inactive labels.  Expanding the two pairing edges along such a path
gives a private-label chain through the located shore `S`; active cut
occurrences are internal transition states and no arbitrary bijection is
chosen.  This is an occurrence-level walk: the two pairing expansions may
reuse an underlying factor edge, so edge-simplicity is not asserted.  This
composes the reverse export of Section 284 with the inactive
payment of Section 285 and removes the non-bijection caveat left after
Section 287.

## 290. The mixed occurrence paths transport a nonzero reverse tag

Let `W_I` be the set of `W_a(S)` endpoints belonging to the `W--I`
components of the overlay in Section 289.  Each such component has exactly
one `W` endpoint, so (918) gives

```text
|W_I|=N_WI=1 mod 2.                                 (919)
```

Every endpoint `w in W_I` retains its component-resolved reverse tag
`rho_w^a` from (899), of augmentation one.  Therefore the tag restricted
to the terminals which actually reach inactive payments is still nonzero:

```text
Rho_I:=sum_(w in W_I) rho_w^a,
aug(Rho_I)=|W_I|=1,
Rho_I!=0.                                           (920)
```

The overlay component containing `w` has a unique other endpoint, an
inactive cut-edge occurrence.  Hence the `W--I` components give a canonical
bijection between `W_I` and an odd set of distinct cut edges indexed by
`a`-labels with no neighbor in `C`.  No tag is assigned to an anonymous
aggregate edge: each `rho_w^a` travels along its specified occurrence walk
to one specified inactive label.

Equivalently, the symmetric difference

```text
T_I:=triangle_(w in W_I) E_w^a subset c\C           (921)
```

is an actual odd root shore whose component profile is `Rho_I`, exactly as
in (905)--(907), but now every contributing triple is paired with an
inactive payment occurrence.  Thus the nonzero reverse destination tag
survives the full active/inactive composition rather than being carried
only by terminals which might close among themselves.

## 291. Every inactive payment leaves an odd reverse-root defect

The inactive endpoint paired to a reverse tag in Section 290 has the wrong
augmentation to absorb it.  For `w in W_I`, let `z(w)` be the private
`a`-label indexing the inactive cut edge at the other endpoint of its
overlay component.  Since `z(w)` has no neighbor in `C`, its two
`c`-neighbors lie in the outside incidence components.  Define

```text
sigma_(z(w))(j):=|N_c(z(w)) intersect U_j| mod 2,
j!=0.                                                (922)
```

The two roots give

```text
aug(sigma_(z(w)))=0,                                 (923)
```

whereas `aug(rho_w^a)=1` by (900).  Hence the
occurrence-level payment defect

```text
d_w:=rho_w^a+sigma_(z(w))
```

has augmentation one.  Summing over the odd family (919) yields

```text
D_I:=sum_(w in W_I)d_w,
aug(D_I)=|W_I|=1,
D_I!=0.                                             (924)
```

This defect again has an actual shore realization.  Put

```text
T_I^def:=triangle_(w in W_I)
          (E_w^a triangle N_c(z(w))) subset c\C.    (925)
```

Each summand has odd cardinality `3+2` modulo two, so the aggregate shore
is odd, and its component-parity profile is exactly `D_I`.  Therefore the
canonical inactive-label payments do not close the reverse export even at
the coarsest component level: after every paired payment is included, a
nonzero odd root defect remains, located on actual roots outside `C`.

## 292. The transported defect retains an odd source subset on the core

The incoming end of every mixed payment path also has a canonical root in
the original five-cycle.  For `w in W_I`, let `x(w)` be the unique root of
`C` adjacent to the active `a`-label at `w`, and define

```text
X_I:=triangle_(w in W_I){x(w)} subset C.             (926)
```

Symmetric-difference cardinality again preserves parity.  By (919),

```text
|X_I|=|W_I|=1 mod 2.                                (927)
```

Thus `X_I` is a nonempty subset of the five roots, of size one, three, or
five.  Let

```text
H(X_I):=sum_(x_i in X_I)[E_(x_i)]
```

be the corresponding edge chain on the connected core `C_5`.  The boundary
kernel on a cycle consists only of the zero and full edge chains, so

```text
partial H(X_I)=0 iff X_I=C.                          (928)
```

Equivalently, the occurrence-level payment composition has the exact
dichotomy

```text
|X_I| in {1,3}:  partial H(X_I)!=0;
X_I=C:            the five source edges close once around the core. (929)
```

The nonzero outside defect `D_I` from (924) is therefore paired with an odd
source subset which retains the same located-boundary versus full-cycle
closure split as Section 256.  The long residual transport has not erased
the original owner index: it returns either a nonzero core boundary demand
or the closed five-edge holonomy, together with an unavoidable odd root
defect outside `C`.

## 293. Every individual payment defect has size one, three, or five

The oddness in Section 291 holds before aggregation and has a bounded
geometric realization.  At `w in W_I`, denote by `y_w^+` the active
`a`-label incident to `w` and by `y_w^-` its inactive companion.  Thus
`y_w^+` has one root in `C`, `y_w^-` has none, and the disjointness proved
in Section 284 gives

```text
E_w^a=(N_c(y_w^+)\C) disjoint_union N_c(y_w^-),
|E_w^a|=1+2=3.                                      (930)
```

Let `z=z(w)` be the terminal inactive label paired with `w`.  It cannot
equal `y_w^+`, because `z` has no neighbor in `C`.  If `z=y_w^-`, then
`N_c(z)` contributes exactly the two-root second summand of (930).  If `z`
is distinct from both companion labels, `C_4`-freeness gives

```text
|N_c(z) intersect N_c(y_w^+)|<=1,
|N_c(z) intersect N_c(y_w^-)|<=1.
```

Indeed, two common roots with either label would form a four-cycle through
those two labels.  In both cases, therefore,

```text
r_w:=|E_w^a intersect N_c(z(w))| belongs to {0,1,2}. (931)
```

The actual support of the pointwise defect `d_w` is

```text
T_w^def:=E_w^a triangle N_c(z(w)) subset c\C,
|T_w^def|=3+2-2r_w belongs to {1,3,5}.               (932)
```

Its component-parity profile is exactly `d_w` from Section 291.  Thus the
aggregate defect (925) is assembled from canonically paired local defects
of uniformly bounded odd size; no cancellation inside one payment can
make its tag vanish.  In the completely local case where the factor
interval pairs the active cut occurrence at `w` directly with the inactive
cut occurrence at the same port, `z(w)=y_w^-`, so `r_w=2` and
`T_w^def=N_c(y_w^+)\C` is the single outside root of the active label.

## 294. The source and defect are joined by an actual root-factor chain

The six-root parity behind each occurrence defect is the boundary of three
canonical edges on the root side.  For `w in W_I`, let `y_w` be its active
`a`-neighbor, let `y'_w` be the other, `C`-inactive `a`-neighbor at `w`,
and retain the terminal inactive label `z(w)` from Section 291.  Every
`a`-label `ell` indexes the edge `E_c(ell)` of the root owner factor
`F_a[c]` whose endpoints are `N_c(ell)`.  Therefore

```text
partial([E_c(y_w)]+[E_c(y'_w)]+[E_c(z(w))])
 ={x(w)} triangle E_w^a triangle N_c(z(w)).          (933)
```

Indeed the first two root pairs are disjoint and their union is the one
core root `x(w)` together with the outside triple `E_w^a`; the last pair is
the terminal inactive support.

Sum these three-edge chains over the odd transported family:

```text
L_I:=sum_(w in W_I)
       ([E_c(y_w)]+[E_c(y'_w)]+[E_c(z(w))]).          (934)
```

Equations (921), (925), and (926) turn (933) into the exact boundary law

```text
partial L_I=X_I triangle T_I^def.                    (935)
```

The two boundary shores are disjoint, and both have odd cardinality by
(927) and (924)--(925).  As a subgraph of the two-factor `F_a[c]`, the
mod-two chain `L_I` is a disjoint union of paths and cycles.  If
`N_XX,N_XT,N_TT` count its path components by endpoint shore, then

```text
|X_I|       =2N_XX+N_XT,
|T_I^def|   =2N_TT+N_XT,
N_XT=1 mod 2.                                        (936)
```

Consequently an odd nonempty family of canonical root-factor paths joins
actual source roots in the original core to actual roots in the outside
defect shore:

```text
x in X_I -- path in F_a[c] -- t in T_I^def.          (937)
```

Thus the residual active/inactive composition has a fully realized route
on both sides: its port-side occurrence walk transports the tags to
inactive labels, and the three associated label edges assemble into an
actual `F_a[c]` path carrying the surviving odd defect away from `C`.

## 295. The surviving defects and routes retain their individual source roots

The aggregate chain in Section 294 decomposes canonically by the original
core root.  For `x in C`, put

```text
W_I(x):={w in W_I:x(w)=x},
D_x:=sum_(w in W_I(x)) d_w,
T_x:=triangle_(w in W_I(x)) T_w^def.                 (938)
```

The component-parity profile of `T_x` is `D_x`.  Since every pointwise
defect has augmentation one and odd support by Sections 291 and 293,

```text
aug(D_x)=|T_x|=|W_I(x)| mod 2.                       (939)
```

In particular the source shore from (926) is exactly the set of roots with
odd local defect augmentation:

```text
X_I={x in C:aug(D_x)=1}={x in C:|T_x|=1 mod 2},
D_I=sum_(x in C)D_x,
T_I^def=triangle_(x in C)T_x.                        (940)
```

This statement does not assert that `D_x` vanishes for `x` outside `X_I`;
such a root may carry a nonzero even-augmentation profile.  It identifies
exactly the odd local rows which survive the symmetric-difference source
census.

There is also a rootwise version of the actual route in (937).  Restrict
the chain (934) to one source fiber:

```text
L_x:=sum_(w in W_I(x))
      ([E_c(y_w)]+[E_c(y'_w)]+[E_c(z(w))]).          (941)
```

Summing (933) only over `W_I(x)` gives

```text
partial L_x=(|W_I(x)| mod 2){x} triangle T_x.        (942)
```

Hence for every `x in X_I`, the mod-two subgraph `L_x` has boundary
`{x} triangle T_x`, with `T_x` odd and disjoint from `C`.  The unique path
component of `L_x` incident to its boundary vertex `x` therefore ends at
an actual root of `T_x`:

```text
x -- path in L_x subset F_a[c] -- t_x in T_x.       (943)
```

Thus neither aggregation over the five core roots nor cancellation between
different source fibers is needed to obtain the outside route.  Every root
which occurs oddly in the transported population carries its own nonzero
component-resolved defect and its own realized root-factor path.  This is
the source-indexed form needed to compare the residual construction with
the rootwise SRP rows (822), rather than with their color-summed shadow.

## 296. Every surviving route is localized on one owner-factor cycle

The rootwise route in Section 295 retains one further canonical index.
Let `Q_a(x)` be the cycle component of the two-factor `F_a[c]` containing
the core root `x`.  Since `L_x` is a subgraph of that two-factor, the path
in (943) cannot leave `Q_a(x)`.  Consequently, for every `x in X_I`, there
is an actual endpoint

```text
t_x in T_x intersect Q_a(x),
x -- path in Q_a(x) -- t_x.                          (944)
```

Thus the odd local defect attached to `x` is not merely nonempty somewhere
outside `C`: at least one of its roots lies on the same owner-factor cycle
as `x`.

There is also an exact cyclewise parity statement for the aggregate chain.
For a cycle component `Q` of `F_a[c]`, restrict `L_I` to its edges and put

```text
epsilon_Q:=|X_I intersect Q| mod 2.
```

Because factor components are vertex-disjoint, restricting (935) gives

```text
partial(L_I intersect Q)
 =(X_I intersect Q) triangle (T_I^def intersect Q),
|T_I^def intersect Q|=epsilon_Q mod 2.               (945)
```

Moreover

```text
sum_Q epsilon_Q=|X_I|=1 mod 2.                       (946)
```

Hence an odd number of owner-factor cycles meet both boundary shores oddly.
On each such cycle, decompose the mod-two subgraph `L_I intersect Q` into
paths and cycles.  If `N_XT(Q)` is the number of its path components with
one endpoint in each shore, the endpoint count on that single factor cycle
gives

```text
N_XT(Q)=epsilon_Q=1 mod 2.                           (947)
```

The residual obstruction is therefore localized simultaneously in three
ways: by receiving color `a`, by source root `x`, and by the concrete cycle
`Q_a(x)` of the root owner factor.  Any proposed absorption must pay an odd
outside defect on an odd family of those actual factor cycles; cancellation
between different owner-factor cycles is unavailable.

## 297. Every odd owner cycle carries two complementary defect routings

The cycle structure supplies a second routing without any additional
choice.  Fix a factor cycle `Q` with `epsilon_Q=1` and write

```text
J_Q:=L_I intersect Q,
Jbar_Q:=Q triangle J_Q.                              (948)
```

Here chains are taken over `F_2`, so `Jbar_Q` is precisely the edge
complement of `J_Q` inside the cycle.  The two supports are edge-disjoint
and partition `E(Q)`.  Since the full cycle has zero boundary, (945) gives

```text
partial J_Q=partial Jbar_Q
 =(X_I intersect Q) triangle (T_I^def intersect Q). (949)
```

This boundary is nonempty: both shores have odd intersection with `Q` and
are disjoint.  Consequently both complementary chains are nonempty and
proper.  At every boundary vertex exactly one of its two incident cycle
edges belongs to `J_Q`, while the other belongs to `Jbar_Q`.

Decompose each chain separately into path components.  Applying the
endpoint count from (947) first to `J_Q` and then to `Jbar_Q` yields

```text
N_XT(J_Q)=N_XT(Jbar_Q)=1 mod 2.                      (950)
```

Thus every owner-factor cycle with odd source mass contains two
complementary, edge-disjoint path systems, each with an odd number of
actual core-to-defect paths.  The statement is cyclewise and does not pair
the same source endpoint across the two systems; it asserts the exact
parity routing that survives all cancellations.  In particular absorption
on such a cycle must account for both directions around the owner factor,
not only for the particular subchain selected by the three-label payment
construction.

## 298. The comparison with the forward SRP row has two exact error terms

The rootwise defect `D_x` and the forward routing row `delta_x^a` use the
same incidence-component index, but they are not the same vector for free.
The discrepancy can be written exactly at the private-label level.  Work in
the binary vector space on `a`-labels and put

```text
Lambda_x:=sum_(w in W_I(x))
          ([y_w]+[y'_w]+[z(w)]),
Y_x:=[r_x^0]+[r_x^1],
R_x:=Lambda_x+Y_x.                                  (951)
```

Here `r_x^0,r_x^1` are the two `a`-labels adjacent to `x`, so `Y_x` is the
private root-star pair used in (816).  Repeated labels in `Lambda_x` are
cancelled over `F_2`; it is the label chain indexing `L_x`, not an
occurrence multiset.

For a binary label chain `Lambda` and `j!=0`, define its two endpoint
profiles

```text
C_j(Lambda):=sum_(ell in Lambda)|N_c(ell) intersect U_j| mod 2,
E_j(Lambda):=sum_(ell in Lambda)|N_e(ell) intersect V_j| mod 2. (952)
```

The boundary identity (942), restricted to an outside component, and the
definition (816) say respectively

```text
C_j(Lambda_x)=D_x(j),
E_j(Y_x)=delta_x^a(j).                               (953)
```

Now retain the component-aligned endpoint discrepancy of every label,

```text
kappa_ell(j):=|N_c(ell) intersect U_j|
              +|N_e(ell) intersect V_j| mod 2,
K_x(j):=sum_(ell in Lambda_x)kappa_ell(j).           (954)
```

Linearity and `R_x=Lambda_x+Y_x` give the exact bridge

```text
D_x(j)+delta_x^a(j)
 =K_x(j)+E_j(R_x),                    j!=0.          (955)
```

Indeed the right side is
`C_j(Lambda_x)+E_j(Lambda_x)+E_j(Lambda_x)+E_j(Y_x)`.
Thus no graph-theoretic assertion is hidden in (955); all cancellations,
including repeated terminal labels, are already accounted for.

Consequently the desired colorwise identification is equivalent to the
specific private-label terminal

```text
D_x=delta_x^a
 iff K_x=(E_j(R_x))_(j!=0).                          (956)
```

Neither (822) nor the cycle localization of Sections 296--297 proves
(956).  The first error term records the component-switch discrepancy of
the labels actually used by the residual payment chain; the second records
the unmatched labels between that chain and the complete two-label star at
`x`.  This is the precise remaining bridge to the forward SRP row.  Any
next absorption theorem must cancel these two displayed terms, or exploit
their failure to cancel; replacing `D_x` by `delta_x^a` without such an
argument would discard exactly the private-label information retained by
the construction.

## 299. The bridge error detects every source/export mismatch

The augmentation of the exact error in (955) has a simple rootwise
meaning.  Write

```text
M_x:=K_x+(E_j(R_x))_(j!=0)=D_x+delta_x^a.           (957)
```

Section 295 gives `aug(D_x)=1` exactly for `x in X_I`.  On the other hand,
(819) says that `aug(delta_x^a)=1` exactly when the unique strict export at
`x` has receiving color `a`; these roots form the set `I_a`.  Therefore

```text
aug(M_x)=1_{x in X_I}+1_{x in I_a}
        =1_{x in X_I triangle I_a}.                 (958)
```

In particular, every root in the symmetric difference carries a nonzero
private-label bridge error.  Thus pointwise cancellation in (956) at all
five roots would force the exact source identity

```text
M_x=0 for every x in C  implies  X_I=I_a.            (959)
```

The converse is deliberately not asserted: when the two root sets agree,
each `M_x` merely has even augmentation and may still be nonzero.

There is also a color-level consequence.  Since `|X_I|` is odd by (927)
and `|I_a|=k_a`, summing (958) over the core gives

```text
aug(sum_(x in C)M_x)=|X_I|+|I_a|=1+k_a mod 2.       (960)
```

Hence every receiving color with even strict-export load `k_a` has a
globally nonzero aggregate bridge error.  For odd `k_a`, augmentation alone
does not decide the aggregate; complete pointwise invisibility still
requires the much sharper alignment `X_I=I_a` from (959).  The remaining
terminal is therefore split cleanly: either exploit the located nonzero
switch/unmatched-chain error on `X_I triangle I_a`, or analyze the rigid
aligned branch in which the residual source roots reproduce the original
strict-export set.

## 300. Every mixed payment has an actual path in the target owner factor

The occurrence walk from Section 289 can be reduced modulo two without
losing its endpoints.  Fix `w in W_I` and its `W--I` overlay component.
Expand every active-pairing edge as its internal path in `H_a^C[S]`, and
expand every factor-pairing edge as the internal part in `S` of its
`F_a[e]` interval.  Zero-length active connections are allowed.  Let
`Theta_w^S` be the symmetric difference of all these internal edge chains.

Every active cut occurrence internal to the overlay component is an
endpoint of exactly one chain of each kind, so its `S`-side vertex occurs
twice in the boundary and cancels.  The only uncancelled endpoints are the
initial tagged port `w` and the `S`-side endpoint `s_w` of the terminal
inactive cut edge indexed by `z(w)`.  Thus

```text
Theta_w^S subset F_a[e][S],
partial Theta_w^S={w} triangle {s_w}.                (961)
```

This identity remains valid if the two occurrence endpoints have the same
underlying port: then the right side of (961) is empty and the internal
chain is a mod-two cycle.  Let `o_w` be the other endpoint of the terminal
edge, so `o_w notin S`, and adjoin that edge:

```text
Theta_w:=Theta_w^S+[E_e(z(w))] subset F_a[e],
partial Theta_w={w} triangle {o_w}.                  (962)
```

The endpoints in (962) are distinct because they lie on opposite sides of
`S`.  Although the raw alternating expansion may traverse an underlying
factor edge more than once, symmetric difference removes every even reuse.
The resulting support is a subgraph of the two-factor and has boundary
exactly `{w,o_w}`.  Its path decomposition therefore contains one actual
edge-simple path component joining them:

```text
w in S -- path in F_a[e] -- o_w notin S.             (963)
```

There is also an aggregate parity consequence.  Put

```text
Theta_I:=sum_(w in W_I)Theta_w,
O_I:=triangle_(w in W_I){o_w} subset e\S.            (964)
```

The tagged ports in `W_I` are distinct, while outside endpoints may repeat
and are correctly cancelled in `O_I`.  Summing (962) gives

```text
partial Theta_I=W_I triangle O_I,
|O_I|=|W_I|=1 mod 2.                                (965)
```

Thus the residual construction now has realized routes on both owner
factors.  Sections 294--297 give root-factor paths from the original core
to the surviving root defect, while (963) gives, payment by payment, a
target-factor path from each transported reverse terminal through the
located shore and out across its specified inactive edge.  The earlier
warning about the raw occurrence walk remains correct; edge simplicity is
obtained only after mod-two reduction and path decomposition of the
resulting factor subgraph.

## 301. The unmatched label error has an exact root-factor boundary

The second error term in (955) is not an abstract label vector.  Its label
chain `R_x=Lambda_x+Y_x` has a completely explicit boundary in the root
owner factor.  Let `g_x^0,g_x^1` be the other `c`-endpoints of the two
root-star edges indexed by `r_x^0,r_x^1`.  Both lie outside `C`, since an
exterior label meets at most one root of `C`, and they are distinct: if
they coincided, that root and `x` would have the two common `a`-neighbors
`r_x^0,r_x^1`, forming a four-cycle.  Put

```text
G_x:={g_x^0,g_x^1} subset c\C,
partial Y_x=G_x.                                    (966)
```

The root `x` cancels twice in the boundary of the complete two-edge star.
Combining (942), (951), and (966) now gives

```text
partial R_x
 =(1_{x in X_I}){x} triangle T_x triangle G_x.      (967)
```

There is an equivalent private-label statement at the core root.  The only
`a`-labels adjacent to `x` are `r_x^0,r_x^1`.  Every occurrence contributing
to `Lambda_x` supplies exactly one of them, namely its active label `y_w`,
while `Y_x` toggles both.  Hence

```text
|supp(R_x) intersect {r_x^0,r_x^1}|
 =|W_I(x)|=1_{x in X_I} mod 2.                      (968)
```

Thus for `x in X_I`, the unmatched chain retains exactly one of the two
root-star labels modulo two and has boundary `{x} triangle T_x triangle
G_x`.  For `x` outside `X_I`, it retains either zero or both star labels and
has only the outside boundary `T_x triangle G_x`.  This locates the
`E(R_x)` term of (955) on an actual subchain of `F_a[c]`; it cannot be
treated as an anonymous even correction.  What remains is to compare its
`e`-endpoint profile with the port-factor chain obtained by expanding the
Section 289 occurrence walk.

## 302. Every payment carries a bounded root route and a target escape

The root-factor realization can also be kept pointwise in the same
occurrence index as the target-factor path from Section 300.  For
`w in W_I`, define the three-label root chain

```text
L_w:=[E_c(y_w)]+[E_c(y'_w)]+[E_c(z(w))].            (969)
```

The pointwise identity (933) and the local defect shore from (932) give

```text
partial L_w={x(w)} triangle T_w^def.                 (970)
```

The active label `y_w` is distinct from both inactive labels and is the
only one of the three incident to a root of `C`; in particular it is the
unique edge of `L_w` incident to `x(w)`.  The two inactive labels either
coincide, in the completely local case `z(w)=y'_w`, or are distinct.
Consequently the mod-two support of `L_w` has respectively one or three
edges.  Its component at `x(w)` is therefore an actual path of length at
most three, whose other endpoint belongs to the pointwise defect shore:

```text
x(w) -- path of length <=3 in F_a[c] -- t_w,
t_w in T_w^def subset c\C.                          (971)
```

When `z(w)=y'_w`, the two inactive edges cancel and (971) is exactly the
single active factor edge from `x(w)` to the unique outside root of
`y_w`, agreeing with the final clause of Section 293.

For the same occurrence `w`, Section 300 supplies the independently
realized target-factor chain

```text
partial Theta_w={w} triangle {o_w},
w -- path in F_a[e] -- o_w,          o_w notin S.    (972)
```

Thus every member of the odd family `W_I` carries one concrete dual-route
quadruple

```text
(x(w),t_w; w,o_w),
x(w) in C,   t_w notin C,   w in S,   o_w notin S.  (973)
```

The first route is uniformly bounded by three root-factor edges; the
second is the mod-two reduction of the full occurrence overlay and may be
long.  No disjointness between different quadruples, and no equality of
their label sequences, is asserted.  The gain is exact occurrence
coupling: the same reverse terminal which produces the bounded odd root
defect also determines an actual escape across the target-owner shore.

## 303. The bounded root route has an exact local shape classification

The length bound in (971) can be resolved completely.  Fix `w in W_I` and
write the two companion root edges as

```text
N_c(y_w)={x,u},
N_c(y'_w)={v_0,v_1},                                (974)
```

where `x=x(w)` and the four displayed roots are distinct by Section 284.
Put `Z_w:=N_c(z(w))` and

```text
r_w=|Z_w intersect {u,v_0,v_1}|.
```

Section 293 gives `r_w in {0,1,2}` and
`|T_w^def|=5-2r_w`.  The component of `L_w` incident to `x` is as follows.

```text
r_w=0:
  x--u.                                              (975)

r_w=1, u in Z_w:
  x--u--h,       where Z_w={u,h}.                    (976)

r_w=1, Z_w intersect {v_0,v_1}!={}:
  x--u.                                              (977)
```

In (975) the other two edges form components disjoint from `x`.  In (976)
the terminal edge indexed by `z(w)` continues the active edge, and `h` is
the defect endpoint.  In (977) the terminal edge instead joins the
inactive-companion component, so the source component again ends at `u`.

It remains to resolve `r_w=2`.  If `z(w)=y'_w`, the two inactive label
edges cancel and the source route is the single edge `x--u`, as already
noted after (971).  Otherwise `z(w)` is distinct from both companions.
Then `C_4`-freeness permits at most one shared root with each companion;
therefore, after exchanging `v_0,v_1` if necessary,

```text
Z_w={u,v_0},
x--u--v_0--v_1,
T_w^def={v_1}.                                      (978)
```

These cases are exhaustive.  In particular the bounded root route uses
the same terminal label `z(w)` as the target escape (972) exactly when
`u in Z_w`; then it has length two or three.  Otherwise it is the single
active edge `x--u`, while the inactive labels lie in separate or cancelled
components.  This identifies precisely when the occurrence-indexed dual
routes share their terminal private label, rather than leaving that issue
inside the length-three bound.

## 304. A shared terminal label forces separation on the target factor

The shared-label cases in Section 303 have an additional `C_4`-free cost.
Suppose `u in Z_w`, so the active label `y_w` and terminal label `z(w)`
share the outside root `u`.  Their target neighborhoods must then be
disjoint:

```text
N_e(y_w) intersect N_e(z(w))=emptyset.              (979)
```

Otherwise a common target port together with `u,y_w,z(w)` would form a
four-cycle.  Since the tagged port `w` belongs to `N_e(y_w)`, neither
endpoint of the terminal edge indexed by `z(w)` is `w`.  In the notation
of Section 300,

```text
s_w!=w,       o_w!=w.                               (980)
```

The path component of `Theta_w` ending at `o_w` necessarily uses the
terminal edge `s_w--o_w` as its last edge: every other edge of
`Theta_w^S` has both endpoints in `S`.  Because `s_w!=w`, the preceding
part from `w` to `s_w` is nonempty.  Hence in every shared-label case the
target escape satisfies

```text
length_(F_a[e])(w--o_w)>=2.                          (981)
```

Conversely, if the particular terminal-`z(w)` path extracted from
`Theta_w` is a single edge, then `z(w)` is incident to `w`.
The only two `a`-labels incident to `w` are the active label `y_w` and its
inactive companion `y'_w`; since `z(w)` is inactive and cannot equal
`y_w`, this forces `z(w)=y'_w`.  The companion supports in (974) are
disjoint, so then `u notin Z_w` and the root route is the single active
edge `x--u`.

Thus the occurrence-level dual route has an exact alternative.  Either
the root route and target escape share the terminal private label, in which
case `C_4`-freeness separates its target edge from the starting active edge
and charges at least two target-factor steps, or the terminal-`z(w)` path
extracted from `Theta_w` is one step only in the completely local,
nonshared root-route case.  Other first-exit paths on the same factor cycle
are not bounded by this converse.

## 305. The dual routes can always share their active source label

The target escape in Section 300 can be chosen with more structure.  Fix
`w in W_I`.  Every expanded connection in its overlay component lies in
the same cycle of the full factor `F_a[e]`: active-pairing connections use
edges of `H_a^C[S] subset F_a[e]`, factor-pairing intervals use edges of
`F_a[e][S]`, and two successive connections are glued at the same active
cut-edge occurrence.  Denote this cycle by `Q_e(w)`.

The overlay component terminates at the inactive cut edge indexed by
`z(w)`.  Hence that edge belongs to `Q_e(w)` and crosses `S`, so

```text
Q_e(w) is not contained in S.                        (982)
```

The two factor edges incident to `w` are precisely those indexed by the
active and inactive companion labels `y_w,y'_w`.  Starting from `w`, follow
each of the two directions around `Q_e(w)` until its first vertex outside
`S`.  This gives two edge-disjoint first-exit arcs apart from their common
initial vertex (their outside endpoints may coincide):

```text
P_w^+ : w --[y_w]-- ... -- o_w^+,    o_w^+ notin S,
P_w^- : w --[y'_w]-- ... -- o_w^-,   o_w^- notin S. (983)
```

Their internal vertices lie in `S`, and their edge supports are disjoint.
In particular `P_w^+` is an actual simple target-factor escape whose first
edge has the active private label `y_w`.

On the root side, every path in the classification of Section 303 begins
with the edge indexed by that same active label:

```text
x(w) --[y_w]-- u -- ... -- t_w.                     (984)
```

Combining (983) and (984), every transported occurrence has a
source-synchronized dual route

```text
x(w) --[y_w]-- ... -- t_w notin C,
w    --[y_w]-- ... -- o_w^+ notin S.                (985)
```

Thus terminal-label synchronization from Section 303 may occur or fail,
but initial-label synchronization never fails: the same exterior label
`y_w` is the first owner edge on both fibers.  This conclusion does not
identify the later edges of the two paths and does not assert disjointness
between different occurrences.  It replaces the arbitrary target escape
choice in (972) by a canonical direction distinguished by the active
source label, while retaining the complementary inactive-start direction
as a second available escape.

## 306. The overlay-selected escape starts at the inactive companion

The particular mod-two escape `Theta_w` from Section 300 chooses the other
direction at its initial port.  Let `A_w` be the active-pairing connection
from the `W` stub at `w` to the first active cut occurrence on its `W--I`
overlay component.  If this connection is nonzero, its internal path in
`H_a^C[S]` starts with the active edge indexed by `y_w`.

Consider the factor-pairing interval attached at the other end of `A_w`.
At that active cut occurrence, the cut edge is missing from the induced
factor on `S`, so the interval's unique internal edge is the last edge of
`A_w`.  It therefore retraces `A_w`: every internal vertex of the active
path has both factor edges in `H_a^C[S]`, forcing the continuation, until
it reaches `w`.  There the active graph has degree one and the full factor
has degree two, so the interval continues through the other edge, indexed
by the inactive companion `y'_w`.  If `A_w` is zero-length, the same
conclusion holds immediately at `w`.  Thus the duplicated active segment
cancels in the symmetric difference defining `Theta_w^S`, leaving

```text
the unique Theta_w edge incident to w is E_e(y'_w). (986)
```

At the other boundary vertex `o_w`, the unique incident edge is the added
terminal edge `E_e(z(w))`.  Hence the unique path component of `Theta_w`
with boundary `{w,o_w}` has a canonically indexed label chain `Pi_w`
satisfying

```text
w --[y'_w]-- ... --[z(w)]-- o_w.                    (987)
```

This identifies the two private endpoint labels of the actual overlay
escape, not merely the direction of an arbitrary first-exit arc from
Section 305.  When `z(w)=y'_w`, (987) is the single terminal edge, in
agreement with the local case of Sections 303--304.

For distinct inactive endpoint labels, let `Pi_w^int` be the label chain
obtained from `Pi_w` by deleting its first and last labels.  The pointwise
root chain from (969) is

```text
Lambda_w=[y_w]+[y'_w]+[z(w)].
```

Therefore the two inactive endpoint labels cancel in the cross-factor
comparison:

```text
z(w)!=y'_w  implies
Lambda_w+Pi_w=[y_w]+Pi_w^int.                        (988)
```

In the equal-label local case the two inactive occurrences already cancel
inside `Lambda_w`, so instead

```text
z(w)=y'_w  implies  Lambda_w=[y_w],
                         Pi_w=[y'_w].                (989)
```

Equations (988)--(989) are the first exact label-level telescope between
the realized root and target routes.  Outside the completely local case,
the discrepancy is reduced to the single active source label plus the
strictly internal labels of the overlay-selected target path; no inactive
endpoint label remains unmatched.

## 307. The two owner factors are orthogonal on their common label set

There is a global realizability constraint on every dual-route label word.
Fix the exterior color `a` and put a graph `Gamma_c^a` on the vertices of
`a` by joining two labels when their indexed edges in `F_a[c]` share a
`c`-root.  Define `Gamma_e^a` analogously from `F_a[e]`.  Since both owner
factors are two-regular, their line graphs are spanning two-factors on the
same private-label set:

```text
Gamma_c^a=L(F_a[c]),
Gamma_e^a=L(F_a[e]).                                 (990)
```

Their edge sets are disjoint.  Indeed, if distinct labels `ell,m` were
adjacent in both graphs, their factor edges would share some root `u in c`
and some port `p in e`.  Then `u` and `p` would have the two common
`a`-neighbors `ell,m`, producing a four-cycle.  Therefore

```text
E(Gamma_c^a) intersect E(Gamma_e^a)=emptyset,        (991)
```

and their union is a simple four-regular graph on the `a`-labels.  This is
the label-level form of the `C_4` exclusion: two private labels consecutive
on a root-factor route are never consecutive on a target-factor route.

For the synchronized routes of Sections 303--305, the active label `y_w`
is the first edge on both sides.  Whenever the root route next uses the
terminal label `z(w)` (equivalently, `u in N_c(z(w))` in (978)), the pair
`y_w,z(w)` is an edge of `Gamma_c^a` and hence not of `Gamma_e^a`.  Thus any
target-factor path which contains both endpoint labels must have a genuine
intervening label:

```text
y_w,...,z(w) on a target path and
y_w,z(w) consecutive on the root path
implies target distance between their factor edges at least two. (992)
```

In particular such a target path uses at least three factor edges.  More
generally, every consecutive pair in the bounded root word of Section 303
is forbidden as a consecutive pair in either direction around the target
cycle.  This does not force the active first-exit arc to contain `z(w)`;
it constrains it when it does, and constrains every comparison of the full
root and target label chains.  The two words are therefore not arbitrary
reuses of the same labels: their adjacency sets must be disjoint.

## 308. The unmatched SRP term splits into actual target endpoints and one residue

The pointwise telescope of Section 306 can be summed without losing the
source-root index.  For `x in C`, put

```text
Pi_x:=sum_(w in W_I(x)) Pi_w,
A_x :=sum_(w in W_I(x))[y_w],                        (993)
```

and separate the local occurrences

```text
L_x^loc:={w in W_I(x):z(w)=y'_w}.
```

Define the remaining internal-label chain by

```text
J_x:=sum_(w in W_I(x)\L_x^loc) Pi_w^int
     +sum_(w in L_x^loc)[y'_w].                      (994)
```

For a nonlocal occurrence, (988) says
`Lambda_w+Pi_w=[y_w]+Pi_w^int`; for a local occurrence, (989) says the
same comparison is `[y_w]+[y'_w]`.  Summing the two cases gives

```text
Lambda_x+Pi_x=A_x+J_x,
R_x+Pi_x=Y_x+A_x+J_x.                               (995)
```

The `e`-endpoint profile of `Pi_x` is fully realized.  Every `Pi_w` is the
simple path component of `Theta_w` from `w` to `o_w`, so for `j!=0` put

```text
P_x(j):=E_j(Pi_x)
 =|V_j intersect
    triangle_(w in W_I(x))({w} triangle {o_w})| mod 2.             (996)
```

The initial endpoints satisfy `w in S subset O subset e\Z`.  The terminal
endpoint `o_w` lies outside `S`, but it may lie in `Z`; inactivity of
`z(w)` refers to its `c`-neighborhood, not its `e`-endpoints.  Formula
(996) therefore records exactly the outside-component coordinates
`j!=0` and silently discards a terminal endpoint in `V_0=Z`, as the
definition of `E_j` requires.  Applying that linear endpoint map to (995)
yields

```text
E_j(R_x)=P_x(j)+E_j(Y_x+A_x+J_x).                   (997)
```

Substitute (997) into the exact bridge (955).  Its missing colorwise term
now has the occurrence-resolved form

```text
M_x=D_x+delta_x^a
   =K_x+P_x+(E_j(Y_x+A_x+J_x))_(j!=0).              (998)
```

Thus the anonymous unmatched profile `E(R_x)` has disappeared.  The first
replacement term is the component profile of actual target-factor path
endpoints; the second is the endpoint profile of one explicit residual
label chain, consisting of the complete root star, the active source
labels selected by the odd occurrence family, and the strictly internal
target labels (with the local inactive edge retained exactly in the sole
exceptional case).  A final telescope must control this displayed residue,
but it no longer has to reconstruct which inactive endpoint labels are
paired: Section 306 has cancelled those labels exactly before aggregation.

## 309. Inactive-root overlap forces a genuine internal target label

The orthogonality in Section 307 gives a pointwise price for two of the
local shapes in Section 303.  Define

```text
W_I^in:={w in W_I:
         z(w)!=y'_w and
         N_c(z(w)) intersect N_c(y'_w)!={}}.         (999)
```

For `w in W_I^in`, the distinct labels `y'_w,z(w)` are adjacent in the
root-label factor `Gamma_c^a`.  But (987) says that they are respectively
the first and last labels of the simple target path `Pi_w`.  If
`Pi_w^int` were empty, those two labels would be consecutive in
`Gamma_e^a`, contradicting (991).  Hence

```text
w in W_I^in  implies
Pi_w^int!=0 and |E(Pi_w)|>=3.                       (1000)
```

More precisely, the first internal label of `Pi_w` is target-adjacent to
`y'_w` and therefore not root-adjacent to it; the last internal label is
target-adjacent to `z(w)` and therefore not root-adjacent to that terminal
label.  If there is only one internal label, it is root-disjoint from both
inactive endpoints.

The shape classification makes the charged occurrences exact.  Apart
from the excluded local equality `z(w)=y'_w`, condition (999) occurs in
precisely these cases:

```text
r_w=1 with the unique overlap in {v_0,v_1};
r_w=2 with z(w) distinct from y'_w.                 (1001)
```

The first has a three-root defect and the single-edge source route
`x--u`; the second has a singleton defect and the three-edge source route
in (978).  Thus every nonlocal singleton defect pays at least one strictly
internal target label, and so does every three-root defect whose terminal
overlap lies on the inactive companion.

This is a pointwise occurrence charge.  Different internal chains may
still cancel in the aggregate `J_x` of (994), so (1000) is not presented as
a nonvanishing theorem for `J_x`.  Its gain is the exact realizability
constraint needed by the next capacity step: two entire local defect
classes cannot contribute only their inactive endpoint labels to (998);
each must introduce a genuine separator label in the target factor.

## 310. The realized endpoint term is exactly the inactive return parity

The augmentation of `P_x` has a direct geometric meaning.  Each path
`Pi_w` has boundary `{w,o_w}` with `w in S subset e\Z`.  The outside
component coordinates count the initial endpoint once.  They count the
terminal endpoint once exactly when `o_w notin Z`.  Therefore its
contribution to the augmentation is

```text
1+1_{o_w notin Z}=1_{o_w in Z} mod 2.
```

Summing over one source root gives

```text
aug(P_x)=#{w in W_I(x):o_w in Z} mod 2.             (1002)
```

This is also the target-activity bit of the terminal label.  The `S`-side
endpoint `s_w` of `E_e(z(w))` lies outside `Z`, so

```text
t_(z(w)):=|N_e(z(w)) intersect Z| mod 2
          =1_{o_w in Z},
aug(P_x)=sum_(w in W_I(x)) t_(z(w)).                (1003)
```

Every terminal label is `C`-inactive.  Hence (1003) identifies `P_x` as
the actual parity of terminal labels in sector `01`: no neighbor in the
root core, but one neighbor in the selected target component.

Globally split the odd occurrence family into

```text
W_Z  :={w in W_I:o_w in Z},
W_out:={w in W_I:o_w notin Z}.                      (1004)
```

These sets partition `W_I`, so (919) gives

```text
|W_Z|+|W_out|=1 mod 2.                              (1005)
```

Exactly one of the two terminal populations is odd.  In the first branch,
an odd number of the realized payment paths return to the original
five-port component through `C`-inactive, target-active (`01`) labels.  In
the second, an odd number end outside both selected components, and their
terminal labels lie in sector `00`.  Thus the path-endpoint term in (998)
does not introduce a new anonymous parity: it restores the concrete
`01/00` sector dichotomy of the original three-sector payment triangle,
now attached to the transported residual occurrence paths.

## 311. Separator labels cannot cancel between selected overlay paths

The possible aggregate cancellation left open after Section 309 does not
occur.  Distinct vertices of `W_I` belong to distinct `W--I` components of
the abstract overlay, one `W` endpoint per component.  Consider the raw
expansions used to construct their chains `Theta_w`.

Active-pairing connections partition the internal edges of
`H_a^C[S]`, and factor-pairing intervals partition the internal edges of
`F_a[e][S]`.  Thus an underlying factor edge could occur in two raw
selected expansions only if it is active and is used once by an active
connection and once by a factor interval.  Let `A` be its active
connection.  If `A` has an active cut occurrence as an endpoint, the
factor interval containing the edge is forced to follow the same active
run to that occurrence.  The two pairing edges are therefore glued at
that occurrence and lie in the same abstract overlay component.  This
includes an `A--A` connection, where they are glued at both ends.

The only remaining active connection type is `W--W`; it has no active
occurrence node and is itself an unselected `W--W` overlay component.  A
selected factor interval may retrace such a physical run, but no second
selected expansion uses it through the active-pairing layer.  A whole
active cycle likewise has no cut occurrence and belongs to no selected
pairing path.  Consequently

```text
w!=v in W_I  implies
E(Theta_w) intersect E(Theta_v)=emptyset.           (1006)
```

The added terminal inactive edges are also distinct, because distinct
inactive cut occurrences index distinct factor edges.  Taking symmetric
differences inside one expansion can only delete edges, so it cannot spoil
(1006).  The boundary path components inherit the same property:

```text
w!=v in W_I  implies
E(Pi_w) intersect E(Pi_v)=emptyset.                 (1007)
```

Every factor edge has one private `a`-label, hence the path label chains
are pairwise support-disjoint as well.

This makes the aggregate residue `J_x` from (994) a literal disjoint
union.  A nonlocal occurrence contributes its internal path labels, while
a local occurrence contributes the one-edge path label `y'_w`.  Therefore

```text
|supp(J_x)|
 =sum_(w in W_I(x)\L_x^loc)|supp(Pi_w^int)|
  +|L_x^loc|.                                      (1008)
```

Combining (1000) with (1008) yields the capacity lower bound

```text
|supp(J_x)|
 >=|W_I^in intersect W_I(x)|+|L_x^loc|.             (1009)
```

In particular every internal separator forced in Section 309 survives in
`J_x`; so does every completely local inactive edge.  The caveat at the
end of Section 309 is thereby discharged: aggregate cancellation remains
possible among component *profiles* after applying `E_j`, but not among
the underlying private labels in the explicit residual chain of (998).
The remaining price must now pay an actual label population of the size
shown in (1009), rather than a collection of pointwise witnesses which
could disappear before aggregation.

## 312. The selected escapes obey an exact residual-shore capacity bound

The disjointness in Section 311 converts the label charge into an integer
capacity inequality.  Every path `Pi_w` consists of a path in
`F_a[e][S]` followed by its terminal cut edge.  Thus all of its vertices
except `o_w` lie in `S`.  Two edge-disjoint paths in a two-factor cannot
share an `S`-vertex: an internal shared vertex would require more than its
two factor edges, while a shared initial vertex would contradict the
distinctness of the `W_I` endpoints.  Hence the paths are vertex-disjoint
on `S`.

A path of `ell` factor edges from `S` to `e\S`, with all preceding vertices
in `S`, uses exactly `ell` vertices of `S`.  Therefore (1007) gives

```text
sum_(w in W_I)|E(Pi_w)|<=|S|.                       (1010)
```

The left side can be evaluated using the residue `J`.  A local occurrence
has `Pi_w=[y'_w]`, so its length is one and its contribution to `J` is one.
Every nonlocal path has its two distinct inactive endpoint labels plus
`Pi_w^int`.  Put `L^loc:=disjoint_union_(x in C)L_x^loc` and
`J:=sum_(x in C)J_x`.  Using the support-disjoint union (1008),

```text
sum_(w in W_I)|E(Pi_w)|
 =2|W_I|-2|L^loc|+|supp(J)|.                        (1011)
```

The supports of the `J_x` are disjoint by (1007), so
`|supp(J)|=sum_x|supp(J_x)|`.  Consequently

```text
2|W_I|-2|L^loc|+|supp(J)|<=|S|.                    (1012)
```

The located shore satisfies `S subset O`, and (846) gives
`|O|=2q-15`.  Combining (1009)--(1012) yields the explicit pair of bounds

```text
2|W_I|-2|L^loc|+|supp(J)| <= |S| <= 2q-15,
2|W_I|-|L^loc|+|W_I^in|   <= |S| <= 2q-15.         (1013)
```

This is the first integer capacity constraint on the full residual
transport.  It charges one shore vertex for a local escape, at least two
for every other transported occurrence, and a third for every
inactive-overlap separator class from Section 309.  Unlike the preceding
augmentation identities, (1013) can fail by magnitude; any continuation
must fit the odd occurrence population, the local exceptions, and all
forced separator labels inside the actual residual shore of order at most
`2q-15`.

## 313. Zero residual charge forces one of two rigid odd label families

The disjointness in Section 311 makes the zero-charge branch completely
classifiable.  Put

```text
J_tot:=sum_(x in C)J_x.
```

The path supports are disjoint even across different source roots.
Equation (1008), summed over `x`, therefore gives the equivalence

```text
J_tot=0
 iff L_x^loc=empty for every x and
     Pi_w^int=0 for every w in W_I.                 (1014)
```

Thus in the zero-charge branch every terminal label is distinct from its
inactive companion and every overlay-selected target path has exactly the
two-edge label word

```text
Pi_w=[y'_w]+[z(w)].                                 (1015)
```

These endpoint labels are consecutive in `Gamma_e^a`.  Orthogonality
(991) makes them nonadjacent in `Gamma_c^a`, equivalently

```text
N_c(y'_w) intersect N_c(z(w))=emptyset.             (1016)
```

The local classification of Section 303 now leaves only two shapes.  Write
`N_c(y_w)={x,u}` as before:

```text
type 0: r_w=0,                         |T_w^def|=5;
type u: r_w=1 and N_c(z(w)) contains u, |T_w^def|=3. (1017)
```

In type 0 the three labels `y_w,y'_w,z(w)` are pairwise nonadjacent in
`Gamma_c^a`, while `y_w--y'_w--z(w)` is a two-edge walk in
`Gamma_e^a`.  In type `u`, the same two target adjacencies hold and
`z(w)--y_w` is an edge of `Gamma_c^a`; hence the three labels form a mixed
triangle in `Gamma_c^a union Gamma_e^a`, with two target-factor edges and
one root-factor edge.

Let `W_0,W_u` be the two occurrence classes in (1017).  They partition the
odd set `W_I`, so

```text
|W_0|+|W_u|=1 mod 2.                                (1018)
```

Consequently exactly one rigid family is odd: root-independent target
two-paths carrying five-root defects, or mixed label triangles carrying
three-root defects.  Outside this rigid alternative, `J_tot` is a genuine
nonzero private-label charge by Section 311.  This is an exhaustive
terminal split, not yet an exclusion: the next capacity argument must
price the nonzero label population, the odd independent two-path family,
or the odd mixed-triangle family.

## 314. Odd-shore descent eliminates perpetual zero charge

The rigid alternative in Section 313 cannot persist under recursion.  In
the branch `J_tot=0`, every selected path `Pi_w` has length two by (1015).
Let

```text
U(S):=disjoint_union_(w in W_I)(V(Pi_w) intersect S). (1019)
```

Section 311 makes these `S`-vertex pairs disjoint, so

```text
|U(S)|=2|W_I|>=2.                                   (1020)
```

The capacity bound (1010) gives `U(S) subset S`.  Since `|S|` is odd and
`|U(S)|` is positive and even, equality is impossible.  Therefore

```text
S':=S\U(S) subset O,
0<|S'|<|S|,
|S'|=1 mod 2.                                      (1021)
```

The construction from Section 283 onward can be reapplied to `S'`.  This
scope point is exact.  Every vertex of `O` has degree one in each root
matching `M_i` by (873)--(874), so handshaking gives

```text
|delta_(M_i)(S')|=|S'|=1 mod 2,
i in Z/5,                                          (1022)
```

which is precisely the input (892) used by Section 283.  None of Sections
283--313 uses the special target-owner boundary statement (891) which
originally produced `S`; after (892), the only shore hypotheses are
`S subset O` and odd cardinality.  Thus color resolution supplies a new
receiving color and the entire residual construction applies to `S'`.

If the new stage again has zero aggregate residue, repeat (1019)--(1021).
Each zero-charge stage reduces the positive odd shore order by at least
two.  Hence after at most `(|S|-1)/2` such stages either a nonzero residue
appears or the shore has order one.  The latter cannot support another
zero-charge stage: (1014) would give a nonempty odd family of two-edge
paths, while (1010) would require

```text
2|W_I|<=1,                                          (1023)
```

an impossibility.

Consequently the recursion terminates at a descendant odd shore `S_*`
and an actual receiving color `a_*` for which

```text
J_tot(S_*,a_*)!=0.                                  (1024)
```

The two rigid families of Section 313 are therefore transient, not final
escape branches.  Starting from every holonomy shore supplied by Section
282, finite odd-shore descent forces a genuine, explicitly supported
private-label charge.  The remaining theorem no longer needs to price the
zero-charge label triangles or independent wedges indefinitely; it may
work at the first descendant stage carrying (1024).

## 315. Cancelling the forced charge consumes every unused root-star label

At the terminal stage of Section 314, the nonzero chain `J_tot` still
appears in the explicit residue of (998).  Its possible cancellation has a
rigid support interpretation.  Let

```text
Y:=sum_(x in C)Y_x,
A:=sum_(w in W_I)[y_w].                             (1025)
```

The chain `Y` consists of the ten distinct `a`-labels meeting `C`, two at
each root.  The active labels in `A` are also distinct.  Indeed, if the
same active factor edge had two endpoints in `W_I`, its active connection
would be of type `W--W` and neither endpoint would belong to a selected
`W--I` component; if the edge crosses `S`, it has only one endpoint in
`S`.  Therefore

```text
supp(A) subset supp(Y),
|supp(A)|=|W_I|.                                    (1026)
```

Moreover `A` is support-disjoint from every selected path chain `Pi_v`.
For its own occurrence, the simple path leaves `w` through the opposite
edge `y'_w` and cannot later use `y_w` without returning to its initial
vertex.  For a different occurrence, an internal active edge belongs to
the raw expansion of its own selected overlay component and is excluded by
Section 311; an active cut edge is neither an internal path edge nor an
inactive terminal edge.  Hence

```text
supp(A) intersect supp(sum_(w in W_I)Pi_w)=emptyset. (1027)
```

Now put

```text
Q_lab:=Y+A+J_tot.                                   (1028)
```

This is exactly the global explicit residual label chain in the last term
of (998).  If it vanishes, then (1026) and label disjointness give

```text
J_tot=Y\A,
|supp(J_tot)|=10-|W_I|.                             (1029)
```

In particular no local contribution can occur: its label `y'_w` is
`C`-inactive, whereas every label of `Y\A` meets `C`, and Section 311
prevents it from cancelling with another contribution.  Thus `L^loc` is
empty.  Substitute (1029) into the exact capacity identity (1011)--(1012):

```text
10+|W_I|=2|W_I|+|supp(J_tot)|<=|S|.                (1030)
```

Since `W_I` is nonempty and odd, complete cancellation of the explicit
label residue forces

```text
|S|>=11.                                            (1031)
```

Consequently the terminal stage has an exact alternative.  Either
`Q_lab!=0`, leaving a genuine private-label residue in (998), or every one
of its unused root-star labels is consumed by `J_tot` and the located odd
shore has order at least eleven.  This is not yet a component-profile
contradiction: applying `E_j` may still cancel a nonzero `Q_lab`.  It does,
however, replace arbitrary label cancellation by a finite ten-label
exhaustion with the quantitative threshold (1031), which is the remaining
case a final SRP price must address.

## 316. Every residual port has a singleton local-charge normal form

The scope audit in Section 314 allows the recursion to start directly from
any singleton residual shore.  Fix an arbitrary port `s in O` and put

```text
S_s:={s}.                                            (1032)
```

Every root matching `M_i` has degree one at `s`, so all five singleton
cuts are odd.  Section 283 therefore supplies an actual exterior receiving
color `a=a(s)` with

```text
deg_(H_a^C)(s)=1.                                   (1033)
```

Let `y_s` be the unique `C`-active `a`-label whose factor edge is incident
to `s`, and let `y'_s` be the other `a`-label at that port.  Then `y'_s` is
`C`-inactive.  The reverse-terminal set inside the singleton shore is
`W_a(S_s)={s}`.  Section 289 produces an odd nonempty subset of it, hence

```text
W_I={s}.                                            (1034)
```

The unique selected escape is nonempty, while the capacity bound (1010)
gives `|E(Pi_s)|<=|S_s|=1`.  Thus it consists of one edge.  By the exact
endpoint identification (987)--(989), its terminal label equals the
inactive companion:

```text
z(s)=y'_s,
Pi_s=[y'_s],
L^loc={s},
J_tot=[y'_s]!=0.                                   (1035)
```

The pointwise root defect is simultaneously forced into the local shape
of Sections 293 and 303.  Write

```text
N_c(y_s)={x_s,u_s},       x_s in C, u_s notin C.
```

The inactive pair cancels from the three-edge root chain, leaving

```text
T_s^def={u_s},
x_s --[y_s]-- u_s,
s   --[y'_s]-- o_s,       o_s notin {s}.            (1036)
```

Moreover `y'_s` is `C`-inactive, whereas every label in the root-star
chain `Y` and active chain `A` meets `C`.  Hence the explicit residue from
(1028) cannot vanish:

```text
Q_lab(S_s,a(s))=Y+A+[y'_s]!=0.                      (1037)
```

Thus no descent or large-shore cancellation analysis is needed to obtain
a charge.  **Every** residual port `s in O` admits some exterior color with
the same canonical local normal form: one active label routes a selected
root to a singleton outside-root defect, the inactive companion routes
`s` out of its singleton shore, and that companion survives as a private
label residue.  The remaining price problem can therefore be posed on the
family of `2q-15` singleton tickets (1032)--(1037), rather than on an
arbitrary recursively chosen shore.

## 317. The singleton tickets have a global odd private-label charge

The local charges in Section 316 cannot all cancel when the residual ports
are considered together.  For an exterior color `a`, let

```text
W_a^O:={s in O:deg_(H_a^C)(s)=1}.                   (1038)
```

At a fixed residual port, the degrees `deg_(H_a^C)(s)` lie in `{0,1,2}`
and sum to five, one edge from each root matching.  Therefore an odd number
of exterior colors have degree one at `s`.  Since `|O|=2q-15` is odd,

```text
sum_a |W_a^O|=1 mod 2.                              (1039)
```

For every pair `(s,a)` counted in (1038), let `y'_(s,a)` be the unique
`C`-inactive companion from the singleton normal form.  Form the binary
private-label chain

```text
J_O:=sum_a sum_(s in W_a^O)[y'_(s,a)].              (1040)
```

Repeated companion labels cancel only in pairs.  Taking augmentation in
the vector space on all exterior labels and using (1039) gives

```text
aug(J_O)=1,
|supp(J_O)|=1 mod 2,
J_O!=0.                                             (1041)
```

There is a factor-cut realization color by color.  Put
`Hbar_a^C:=F_a[e]\H_a^C`.  At `s in W_a^O`, the active graph has degree
one, so the edge indexed by `y'_(s,a)` is the unique incident edge of
`Hbar_a^C`.  Consequently

```text
J_a:=sum_(s in W_a^O)[y'_(s,a)]
    =delta_(Hbar_a^C)(W_a^O)                       (1042)
```

as an edge/label chain: an inactive edge with both endpoints in `W_a^O`
is counted twice and cancels, while a cut edge is counted once.  Equation
(1039) supplies at least one color `a_*` with `|W_(a_*)^O|` odd.  For every
such color,

```text
|J_(a_*)|=|W_(a_*)^O|=1 mod 2,                     (1043)
```

because `Hbar_(a_*)^C` has degree one at every vertex of that shore.
Thus the global residue contains an actual odd cut of `C`-inactive owner
factor edges.  Its far endpoints may lie in `Z`, in `B`, or in
`O\W_(a_*)^O`; only in the last case are they necessarily even-multiplicity
residual tickets.  The assertion is a noncancellation theorem for private
labels, not yet for their component profiles: applying `E_j` to the odd
chain may still cancel.  It nevertheless replaces `2q-15` separately
chosen local witnesses by one color-resolved odd inactive-factor cut on
which a final SRP price can act.

## 318. The full singleton ledger contains at least q minus seven labels

The odd chain in Section 317 also has an integer magnitude before binary
cancellation.  Let

```text
Sigma:={(s,a):s in O and deg_(H_a^C)(s)=1},
T:=|Sigma|=sum_a |W_a^O|.                           (1044)
```

At each residual port the exterior-color degrees belong to `{0,1,2}` and
sum to five.  The number of entries equal to one is therefore one, three,
or five.  Summing over the odd residual set gives

```text
2q-15<=T<=5(2q-15),
T=1 mod 2.                                         (1045)
```

Map a singleton occurrence `(s,a)` to its inactive companion label
`y'_(s,a)`.  A private label has exactly two `e`-endpoints, and its color is
fixed, so it can be the selected companion of at most two singleton
occurrences.  If `n_1` labels occur once and `n_2` occur twice in this
ledger, then

```text
T=n_1+2n_2,
N_dist:=n_1+n_2>=ceil(T/2)>=q-7.                   (1046)
```

Moreover the binary chain `J_O` from (1040) is supported precisely on the
labels of multiplicity one.  Hence

```text
|supp(J_O)|=n_1=1 mod 2.                            (1047)
```

Thus the singleton construction produces two complementary global
outputs.  At least `q-7` distinct `C`-inactive labels carry local charges
before cancellation, a magnitude growing linearly with the component
parameter; and an odd nonempty subfamily remains after every possible
pair cancellation.  Labels of multiplicity two are not spurious: their
factor edge has both endpoints among the corresponding fixed-color
singleton tickets and is exactly an internal edge removed from the cut
chain (1042).  A final magnitude price may therefore charge all
`N_dist` labels, while a parity price may act on the surviving odd cut
support (1047).

## 319. Inactive-factor paths carry an odd residual family to Z or B

The apparent residual-to-residual branch of the cut (1042) disappears if
one follows an entire component of the inactive complement.  Fix a color
`a` for which

```text
W:=W_a^O,
|W|=1 mod 2,                                       (1048)
```

and write `Hbar:=Hbar_a^C`.  Since `F_a[e]` is a two-factor, at every
`e`-endpoint `v` one has

```text
deg_Hbar(v)=2-deg_(H_a^C)(v).                      (1049)
```

Thus the endpoints of the nontrivial path components of `Hbar` are
exactly the vertices of `H_a^C`-degree one.  (The other components are
cycles or isolated vertices and have no such endpoint.)  Pair the two
endpoints of each nontrivial path component,
and let `tau_a` denote this fixed-point-free pairing on the degree-one
vertices.  Counting the endpoints in `W` path by path gives

```text
#{P nontrivial path component of Hbar:
    |Ends(P) intersect W|=1}=|W|=1 mod 2.          (1050)
```

Indeed a path with both endpoints in `W` contributes two, a crossing
path contributes one, and a path disjoint from `W` contributes zero.
For every crossing path its other endpoint `t=tau_a(s)` has
`deg_(H_a^C)(t)=1` and lies outside `W`.  It cannot lie in `O`: by
definition every residual port of degree one in this color belongs to
`W_a^O`.  Since

```text
e=Z disjoint_union B disjoint_union O,
t belongs to Z union B.                            (1051)
```

Consequently there is an odd family of pairwise edge-disjoint actual
`C`-inactive factor paths

```text
s in W_a^O  --[component of Hbar_a^C]-->  t in Z union B.   (1052)
```

The endpoint in `Z` is a degree-one, hence `01`, return to the selected
five-port component.  The endpoint in `B` is a degree-one private-owner
ticket.  An individual first cut edge may still enter a residual port of
active degree zero, but continuing through its inactive-complement path
must eventually reach one of these two terminal roles; there is no third
residual terminal class.  This is a path-level parity dichotomy, not yet
a contradiction: the terminal paths may still cancel after projection
to component profiles, and a final SRP price must distinguish or consume
their `Z` and `B` endpoints.

## 320. Every odd inactive terminal family returns to an odd selected shore

The two terminal roles in Section 319 can be composed into one selected
endpoint ledger.  Every private-owner port `b in B` has a unique
`A_e`-neighbor in `Z`: the ten ports of `B` are the disjoint union of the
two outside owner neighbors of each selected port.  Write this neighbor as

```text
p(b) in Z.                                          (1053)
```

For each crossing inactive-complement path `P` in the odd family (1052),
let `t(P)` be its endpoint in `Z union B` and put

```text
zeta(P):=t(P),       if t(P) in Z;
zeta(P):=p(t(P)),    if t(P) in B.                  (1054)
```

In the second case append the actual owner edge
`{t(P),p(t(P))}` to `P`; in the first case leave `P` unchanged.  This gives
an actual route `P_hat` from its residual singleton endpoint in `W_a^O` to
the selected port `zeta(P)`.  The inactive-factor part is indexed entirely
by `C`-inactive private labels, and at most the final edge is an `A_e` owner
edge.

Take the symmetric difference of the selected endpoint occurrences:

```text
Z_*:=triangle_(P crossing) {zeta(P)} subset Z.      (1055)
```

The number of crossing paths is odd by (1050).  Each contributes one
selected endpoint occurrence, so cancellation at a port can only remove
an even number and

```text
|Z_*|=1 mod 2,
Z_*!=empty.                                         (1056)
```

Equivalently, the mod-two sum of the extended routes has boundary

```text
W_* triangle Z_*,                                  (1057)
```

where `W_* subset W_a^O` is the odd set of their residual endpoints.
Repeated selected endpoints and any overlap of route interiors are already
handled by symmetric difference; the boundary identity remains exact.

The terminal activity is also concrete.  A path ending directly in `Z`
meets the unique strict `11` export of color `a` at that degree-one port.
A path ending in `B` meets a singleton color-`a` entry of the private-owner
ticket before its last owner step to `Z`.  Thus both cases carry an actual
root-indexed active label at the penultimate terminal, while (1055)--(1057)
put their final endpoints on one nonempty odd shore of the original
five-port component.

Section 319 therefore has no lasting `Z/B` escape branch: an odd family of
residual singleton charges always produces realized routes back to an odd
selected shore.  This is still a transport theorem rather than a
contradiction.  The remaining absorption step must compare `Z_*` with the
rigid strict-export permutation (777), or charge the private-owner ticket
encountered on the routes which use the final owner edge.

## 321. The selected shore induces a nonzero core boundary or the full curl

The odd shore in (1055) has an immediate interpretation on the original
five-cycle.  Index its selected ports and core vertices cyclically as
`Z={p_i:i in Z/5Z}` and `C={x_i:i in Z/5Z}`, so that the selected incidence
of `p_i` is the core edge

```text
E_i:={x_i,x_(i+1)}.                                (1058)
```

Project the selected endpoint ledger to the binary core-edge chain

```text
K_*:=sum_(p_i in Z_*) [E_i] in F_2^(E(C_5)).       (1059)
```

Because the five `E_i` are distinct, (1056) says that `K_*` has odd,
nonzero support.  The cycle space of a simple five-cycle consists only of
the zero chain and the full cycle.  Hence

```text
partial K_*=0  iff  K_*=sum_i [E_i]
                 iff  Z_*=Z.                       (1060)
```

In particular, exactly one of the following alternatives holds:

```text
Z_*=Z, and K_* is the full five-edge curl; or
|Z_*| in {1,3}, and partial K_* is a nonzero even core shore. (1061)
```

This is not merely an abstract parity projection.  Each occurrence of a
selected port in (1055) is the endpoint of an actual extended route
`P_hat` from Section 320, and its two core incidences are precisely the
edge `E_i` charged in (1059).  Thus the symmetric-difference route family
carries the singleton residual charge all the way back to the original
curl, where it either exposes a proper nonzero core boundary or consumes
every selected incidence once modulo two.

The remaining obstruction is consequently sharper than an arbitrary odd
selected shore.  The proper-shore branch must absorb a visible boundary on
the five core roots, while the boundary-free branch is forced to be the
unique full-cycle chain.  Any final strict-export or private-ticket price
may therefore be proved separately in these two rigid cases.

## 322. The returned routes leave an unavoidable odd root defect

The terminal activity retained in Section 320 removes the full-curl escape
in (1061).  Let `P` range over the odd family of crossing paths from
(1050).  Its terminal `t(P)` has `H_a^C`-degree one, so its unique active
color-`a` label meets a unique root of `C`; denote that root by `r(P)`.
Pair it with the selected endpoint `zeta(P)` from (1054).

This pair is never an incidence of the original core.  If `t(P)` lies in
`Z`, its active label is the strict export at that selected port, and the
strict permutation (777) assigns it to the opposite, nonincident root.  If
`t(P)` lies in `B`, its active label is the singleton color-`a` letter of
the ticket `tau(t(P))`; Section 267 says that all three ticket roots avoid
the two roots incident to the owner port `p(t(P))=zeta(P)`.  Thus

```text
(r(P),zeta(P)) belongs to
  (C times Z)\E(R_ce[C,Z])                          (1062)
```

for every crossing path.  Sum these terminal pairs over `F_2`:

```text
L_*:=sum_(P crossing) [(r(P),zeta(P))].             (1063)
```

The complement in (1062) has fifteen edges.  Since the number of crossing
paths is odd, cancellation of repeated pairs leaves

```text
|supp(L_*)|=1 mod 2,
L_*!=0.                                             (1064)
```

Let `R_* subset C` be the odd-degree root shore of this bipartite edge
chain.  Its selected-port boundary is exactly `Z_*`: both count the same
terminal occurrences, now grouped by `zeta(P)`.  On the two sides of the
chain one therefore has

```text
partial L_*=R_* disjoint_union Z_*,
|R_*|=|Z_*|=1 mod 2.                                (1065)
```

Now compare the root projection with the core-edge chain `K_*` from
(1059).  Define

```text
D_*:=R_* triangle partial K_* subset C.             (1066)
```

Every graph boundary has even cardinality, whereas `R_*` is odd.  Hence

```text
|D_*|=1 mod 2,
D_*!=empty.                                         (1067)
```

This defect is realized occurrence by occurrence.  Linearity of the two
projections gives

```text
D_*=triangle_(P crossing)
      ({r(P)} triangle Ends(E_(zeta(P)))).           (1068)
```

By (1062), each summand in (1068) is a set of three distinct core roots:
the terminal active root and the two roots incident to the returned
selected port.  An odd family of realized residual-to-selected routes
therefore leaves a located odd root defect after the selected incidences
are fully charged.

In particular the boundary-free alternative `Z_*=Z` in (1061) no longer
closes the ledger: then `partial K_*=0` and `D_*=R_*` is still odd and
nonzero.  The remaining terminal price may act directly on the actual
three-root contributions (1068); it need not split between a proper core
boundary and a supposedly harmless full curl.  This is still not itself a
contradiction, because an odd root shore can be exported through the
outside incidence components, but it removes the last cancellation
available wholly inside the original five-port component.

## 323. The odd core defect has an exact odd outside-root destination

The export mentioned at the end of Section 322 can be located without
introducing another arbitrary component profile.  For each crossing path
`P`, let `alpha(P)` be the unique active color-`a` label at its terminal
`t(P)`.  Section 252 gives `i_(alpha(P))=1`: in the `c`-factor this label
indexes an actual edge

```text
{r(P),v(P)} in F_a[c],       r(P) in C, v(P) notin C. (1069)
```

Take the symmetric difference of these terminal-label edges,

```text
A_T:=sum_(P crossing) [{r(P),v(P)}].                (1070)
```

Two occurrences cancel in `A_T` exactly when they use the same label,
because factor edges are indexed by their intermediate labels.  The
number of crossing paths is odd, so

```text
|supp(A_T)|=1 mod 2,
A_T!=0.                                             (1071)
```

Every surviving edge of `A_T` has exactly one endpoint in `C`.  Its
`C`-side boundary is the root shore `R_*` from (1065).  Write `V_*` for
its boundary outside `C`.  Then

```text
partial A_T=R_* triangle V_*,       V_* subset c\C,
|V_*|=|R_*|=1 mod 2.                                (1072)
```

In particular, cancellation among several terminal labels at one outside
root cannot erase all destinations: the parity of `V_*` is the parity of
the surviving factor edges.

Now add the charged curl edges from (1059).  The mixed-color root-graph
chain

```text
G_*:=A_T+K_*                                       (1073)
```

is completely realized: its first summand consists of actual `F_a[c]`
edges and its second of actual core `A_c` edges.  Equations (1066) and
(1072) give the exact boundary identity

```text
partial G_*=D_* triangle V_*.                       (1074)
```

Thus the unavoidable odd core defect of Section 322 is not merely
permitted to escape.  It is joined by an explicit binary root-edge chain
to a nonempty odd shore `V_*` outside the curl, with all repeated labels,
roots, and selected endpoints already cancelled in `F_2`.  Even in the
full-curl case `Z_*=Z`, the five core edges contribute zero boundary and
the same odd outside destination remains.

The terminal obstruction has therefore moved to a sharply defined place:
any completion must absorb the odd set `V_*` through the outside endpoints
of the very terminal labels used by the returned inactive paths.  A next
descent or capacity argument may work on those actual outside roots; it
does not have to choose a fresh defect support or reconstruct which
labels exported `D_*`.

## 324. The outside destination has a nonzero incidence-component profile

The actual shore `V_*` in (1072) cannot disappear when literal outside
root names are compressed to incidence components.  Recall the components
`(U_j,V_j)` of `R_ce`, indexed so that `U_0=C`.  Because
`V_* subset c\C`, the sets `U_j` for `j!=0` partition its possible
locations.  Define

```text
Theta_*(j):=|V_* intersect U_j| mod 2,       j!=0.  (1075)
```

Taking augmentation and using (1072) gives

```text
sum_(j!=0) Theta_*(j)=|V_*|=1 mod 2,
Theta_*!=0.                                         (1076)
```

Equivalently, an odd number of the outside incidence components contain
an odd part of the terminal-label destination shore.  This profile is not
an arbitrary lift: it is exactly the component projection of the outside
boundary of the realized factor-edge chain `A_T`, and hence of the
outside part of `partial G_*` in (1074):

```text
Theta_*(j)=|partial A_T intersect U_j|
          =|partial G_* intersect U_j| mod 2,
          j!=0.                                     (1077)
```

Thus the global singleton construction now survives both levels of
cancellation.  Sections 317--319 first forced an odd cut of actual
`C`-inactive labels; Sections 320--323 transported an odd subfamily
through actual factor and owner routes; and (1076) shows that the resulting
outside-root destination remains nonzero even after incidence-component
compression.  This does not assert that the direct component projection
of the original cut `J_a` was already nonzero--the intervening routes and
terminal active labels are essential.  The remaining obstruction is an
actual nonzero component tag with odd augmentation, rather than the earlier
possibility that all private-label charges cancel after projection.

## 325. Every odd root defect re-enters through an odd active path shore

The exact outside-port partition (835) applies to the odd core shore
`D_*` from (1066), not only to all five roots at once.  Put `d:=|D_*|`, so
`d` is one, three, or five.  For a residual port `s in O` and exterior
color `b`, define the restricted cell multiplicity

```text
d_s^b:=|{x in D_*:s in D_x^b}|.                    (1078)
```

At every root, (835) assigns `s` to exactly one exterior color.  Moreover
a fixed color occurs at most twice at a port by (848).  Therefore

```text
d_s^b in {0,1,2},
sum_b d_s^b=d=1 mod 2.                              (1079)
```

Let

```text
A_D(s):={b:d_s^b=1},
Sigma_D:={(s,b):s in O and b in A_D(s)},
T_D:=|Sigma_D|.                                     (1080)
```

The number of entries equal to one in (1079) is odd.  It lies between one
and `d`, so the odd residual set gives

```text
|O|=2q-15<=T_D<=d(2q-15),
T_D=1 mod 2.                                        (1081)
```

This ledger has an exact factor realization.  Let `H_b^D` be the subgraph
of `H_b^C` consisting of the edges whose root color belongs to `D_*`.
There are exactly two such edges for every root in `D_*`, and the routing
interpretation of (871) gives

```text
|E(H_b^D)|=2d,
deg_(H_b^D)(s)=d_s^b.                               (1082)
```

Consequently the color shore

```text
S_b(D):={s in O:deg_(H_b^D)(s)=1}                  (1083)
```

has size equal to the number of occurrences of `b` in `Sigma_D`.  Summing
over colors and using (1081), an odd number of colors have `|S_b(D)|` odd.
Also a graph with `2d` edges has at most `4d` degree-one vertices, so

```text
|S_b(D)|<=4d,
#{b:S_b(D)!=empty}>=ceil(T_D/(4d))
                    >=ceil((2q-15)/(4d)).           (1084)
```

Thus the odd-defect transport retains a q-growing color footprint even
though every individual root-restricted factor has constant size.

Fix any color `b` for which `S_b(D)` is odd.  The graph `H_b^D` has maximum
degree two.  Pair the degree-one endpoints along its nontrivial path
components.  Exactly as in (1050), an odd number of these paths have one
endpoint in `S_b(D)` and the other outside it.  The other endpoint cannot
lie in `O`, since (1083) contains every residual degree-one vertex of this
restricted graph.  It therefore lies in `Z union B`:

```text
s in S_b(D) --[path in H_b^D]--> t in Z union B,
an odd number of such paths.                        (1085)
```

These are `C`-active paths whose root labels all belong to the original
defect shore `D_*`.  As in Section 320, leave a `Z` terminal fixed and
append the unique owner edge from a `B` terminal to its selected neighbor.
The selected endpoint occurrences again have odd total, hence produce a
nonempty odd shore in `Z`.

Equation (1085) is an exact return map for an arbitrary odd core defect:
integer SRP sends it through an odd residual singleton ledger and back to
the selected five-port component using only root labels already in the
defect.  It is not yet a descent, because the new selected shore need not
be smaller and the chosen color need not be the color `a` used in
Sections 317--324.  The explicit capacity (1084) identifies the remaining
monotonicity question: a contradiction must make successive returns
consume distinct color/root-factor capacity, rather than merely cycle
through the same finite terminal data.

## 326. The terminal-label shore has an odd root-side return family

The outside destinations in Section 323 are not free endpoints of the
`c`-factor.  Return to the color `a` fixed in Section 319.  No `a`-label
meets two vertices of `C`, by (779), while every one of the five roots has
two `a`-neighbors.  Thus `C` is independent in `F_a[c]` and exactly ten
distinct active labels index its cut edges.

Delete `C` from the two-factor `F_a[c]`.  Every boundary-bearing component
of the remainder is a path, and its two endpoints are incident to two of
those ten cut labels.  The five paths therefore induce a fixed-point-free
involution

```text
nu_a^C:{ten C-active labels}->{ten C-active labels}. (1086)
```

This is the root-side analogue of the owner return pairing (837).  A path
may pair the two labels at one root, but no label or outside endpoint is
used by two different paths.

Let `T:=supp(A_T)` be the odd terminal-label support from (1070)--(1071).
Count the pairs of `nu_a^C` with exactly one endpoint in `T`.  Pair by
pair, their parity is the parity of `|T|`, so

```text
#{ {y,nu_a^C(y)}:|{y,nu_a^C(y)} intersect T|=1 }
  =|T|=1 mod 2.                                    (1087)
```

For every crossing pair, retain its outside path in `F_a[c]\C` and append
the two cut edges indexed by the paired labels.  This produces an odd
family of pairwise edge-disjoint actual `F_a[c]` trails

```text
r(y) --[y]-- v(y) --[outside F_a[c] path]--
  v(nu_a^C(y)) --[nu_a^C(y)]-- r(nu_a^C(y)),       (1088)
```

where exactly one of `y,nu_a^C(y)` belongs to the terminal support `T`.
Each trail is a core-to-core path when its two core roots differ, and a
closed return cycle when the pairing joins the two labels at one root.
The labels on the other ends form an odd subset of the complementary
active-label shore.  After cancellation, the two core-root endpoint
supports of the trail family are both odd and nonempty; their symmetric
difference is the exact boundary of the sum of the trails in (1088).

Consequently the nonzero outside-root destination of Sections 323--324
cannot terminate away from the curl: an odd subfamily of its terminal
labels is forced through concrete root-side factor paths back to other
active labels at `C`.  No role is assigned here to the other labels' two
`e`-endpoints.  The new finite object instead combines the `e`-side path
pairing on active endpoint occurrences with the root-side label involution
(1086).  These are not asserted to be two involutions on the same set: the
two `e`-endpoints of one active label may both occur in the first pairing.
Their incidence union nevertheless has only ten label vertices and at most
twenty endpoint occurrences, retains label identity, and is the appropriate
constant-size holonomy object for the next price.  Merely iterating
anonymous odd root shores would discard this extra structure.

## 327. The odd-defect return map sends every singleton to a triple

The final paragraph of Section 325 can be made into an exact finite-state
transition.  Start with any odd shore `D subset C`, choose a color `b` for
which `S_b(D)` is odd, and let `P_b(D)` be the odd crossing-path family in
(1085).  At the terminal `t(P)` of each path, the unique incident edge of
`H_b^D` has a root color

```text
r_D(P) in D.                                        (1089)
```

As before, put `zeta_D(P)=t(P)` for a `Z` terminal and
`zeta_D(P)=p(t(P))` for a `B` terminal.  The pair
`(r_D(P),zeta_D(P))` is off-incidence.  In the direct case it is the
strict cell at the selected port; in the owner case Section 267 excludes
the two roots incident to that port.  Form the binary terminal chain

```text
L_D:=sum_(P in P_b(D)) [(r_D(P),zeta_D(P))]
   in F_2^((C times Z)\E(R_ce[C,Z])).               (1090)
```

Its occurrence count is odd.  Therefore its support is odd and nonempty.
Let `R_D subset C` and `Z_D subset Z` be its two side boundaries.  The
same bipartite handshake used in (1065) gives

```text
partial L_D=R_D disjoint_union Z_D,
|R_D|=|Z_D|=1 mod 2,
R_D subset D.                                       (1091)
```

Charge the selected boundary by its core edges and define

```text
K_D:=sum_(p_i in Z_D)[E_i],
Phi(D):=R_D triangle partial K_D.                   (1092)
```

Since `R_D` is odd and every graph boundary is even, `Phi(D)` is another
odd nonempty shore of `C`.  Thus (1092), together with the choices of an
odd color shore and crossing family, is the set-valued return transition
implicit in Section 325.

It has a strict expansion law at the smallest state.  Suppose
`D={x}`.  Then the odd subset `R_D subset D` in (1091) is forced to be
`{x}`.  Every edge of `L_D` lies in the off-incidence neighborhood of
`x`, which consists of the three selected ports whose core edges do not
meet `x`.  Hence

```text
Z_D is an odd subset of those three ports,
|Z_D| in {1,3}.                                     (1093)
```

If `|Z_D|=1`, `K_D` is one core edge avoiding `x`, so its boundary is its
two other endpoints.  If `|Z_D|=3`, `K_D` is the three-edge path obtained
from `C_5` by deleting the two edges incident to `x`; its boundary again
has two vertices and avoids `x`.  In both cases

```text
|partial K_D|=2,
x notin partial K_D,
|Phi({x})|=3.                                       (1094)
```

Thus no singleton defect is a fixed point of the recursive SRP return, and
no one-step application beginning at a singleton can close at a singleton.
The first possible short recurrence is instead a `1 -> 3 -> 1` reversal;
the abstract off-incidence transition permits such reversals, so excluding
them requires the factor-label holonomy retained in Section 326 rather
than shore parity alone.  Equation (1094) isolates the shortest possible
loss of expansion: a monotonicity proof must in particular price a return
from a realized triple back to one of its singleton predecessors.

## 328. The ten active labels carry a canonical two-axis holonomy skeleton

The endpoint-occurrence caveat in Section 326 has an exact finite model.
Let `Y_a^C` be the ten color-`a` labels active at `C`, and form their
twenty target darts

```text
Ecal_e:={(y,t):y in Y_a^C, t in N_e(y)}.           (1095)
```

Write again `H=H_a^C` and `Hbar=F_a[e]\H`.  Every endpoint of an active
edge has `H`-degree one or two.  Define an involution `sigma_e` on
`Ecal_e` as follows.

* If `deg_H(t)=2`, pair `(y,t)` with the dart of the other active label
  at the same port `t`.
* If `deg_H(t)=1`, follow the nontrivial `Hbar`-path from `t` to its other
  endpoint `t'` and pair `(y,t)` with `(y',t')`, where `y'` is the unique
  active label at `t'`.

Both rules are symmetric, their cases are disjoint, and the second endpoint
in either rule differs from the first dart.  Hence

```text
sigma_e:Ecal_e -> Ecal_e
is a fixed-point-free involution.                   (1096)
```

Project each of its ten pairs through `(y,t)|->y`.  This gives a
two-regular multigraph `Lambda_e` on `Y_a^C`: every label has degree two,
one for each of its target darts.  A loop is allowed when an inactive
path pairs the two target darts of the same label, and parallel edges are
retained.  Each edge has a canonical actual lift, either

```text
y -- t -- y'                                       (deg_H(t)=2),
```

or

```text
y -- t --[Hbar path]-- t' -- y'                    (deg_H(t)=1). (1097)
```

The ten lifts are pairwise edge-disjoint in the `a--e` incidence graph.
In particular, the inactive crossing paths used in Sections 319--323 are
not anonymous: they are selected edges of the second type in this fixed
two-factor skeleton.

There is a parallel, simpler compression on the root side.  Let `kappa_c`
pair the two active labels incident to each root of `C`, and let `nu_a^C`
be the outside-path involution (1086).  Both are perfect matchings on
`Y_a^C`.  Their union

```text
Lambda_c:=kappa_c union nu_a^C                     (1098)
```

is a two-regular multigraph whose cycles alternate between the two
matchings and therefore all have even length.  Its matching edges also
have disjoint actual lifts: a `kappa_c` edge is the two-step trail through
its core root, and a `nu_a^C` edge is the outside return trail from
Section 326.

Consequently

```text
Omega_a^C:=Lambda_c union Lambda_e                 (1099)
```

is a canonically two-axis-colored four-regular multigraph on exactly ten
private labels, counting loops and parallel edges with their usual
multipities.  Within each axis its edges have pairwise disjoint ambient
lifts, and the two axes use the different `a--c` and `a--e` incidence
blocks.  The `c`-axis cycles are forced even; any unpaired holonomy is now
confined to the explicitly realized `e`-axis cycles and their overlay with
the two root matchings.

This is a structural compression, not yet a contradiction.  It replaces
the unbounded outside paths and the ambiguous endpoint-to-label projection
by a fixed ten-vertex object while retaining every transition used to make
the odd terminal shore and every return used in (1087).  The construction
applies separately to every exterior color used by (1085).  Thus an
individual color-`b` return is marked in `Omega_b^C`; a same-color
`1 -> 3 -> 1` reversal lies in one such skeleton, while a mixed-color
reversal requires the interface of the two corresponding ten-label
skeletons.  In either case shore parity alone no longer records the data
which a reversal must preserve.

## 329. A singleton defect returns through exactly one active edge

The singleton expansion in (1094) has a sharper realized normal form.
Take `D={x}` and a color `b` with `|S_b({x})|` odd.  The restricted graph
`H_b^{\{x\}}` consists of exactly the two `b`-factor edges colored by the
root `x`.  They are nonadjacent by (865), so they have four distinct
endpoints and are themselves the two nontrivial path components:

```text
H_b^{\{x\}}=e_x^0 disjoint_union e_x^1,
e_x^0 and e_x^1 are vertex-disjoint edges.          (1100)
```

Every endpoint has degree one in this restricted graph.  Consequently
`S_b({x})` is exactly the subset of the four endpoints which lie in `O`.
Its odd cardinality is therefore one or three.  Pairing endpoints along
the two edges, the number of edges with exactly one endpoint in `O` has
the same parity as `|S_b({x})|`; since there are only two edges, it is
exactly one:

```text
#{h in {0,1}:|e_x^h intersect O|=1}=1.             (1101)
```

The other edge has no residual endpoint when `|S_b({x})|=1`, and has two
residual endpoints when `|S_b({x})|=3`.  Thus the odd crossing family in
(1085) is not merely nonempty in the singleton case: it is the single
root-colored factor edge

```text
s --[one edge of H_b^{\{x\}}]-- t,
s in O,        t in Z union B.                     (1102)
```

After the optional owner step from a `B` terminal, there is one selected
endpoint `zeta`.  Hence the chains in (1090)--(1092) specialize to

```text
L_{\{x\}}=[(x,zeta)],
R_{\{x\}}={x},
Z_{\{x\}}={zeta},
Phi({x})={x} triangle Ends(E_zeta).                 (1103)
```

The pair `(x,zeta)` is off-incidence, so the three roots on the right of
(1103) are distinct.  This strengthens (1094): every singleton return is
a one-edge active-factor event followed by at most one owner edge, and its
triple successor is determined by one specific nonincident selected port.
There is no three-port cancellation branch at the first step.

Accordingly a realized `1 -> 3 -> 1` reversal must undo a fully located
one-edge expansion, not merely reverse an abstract odd shore.  In a
same-color reversal the edge (1102) selects one marked active-label vertex
and its two target darts in the ten-label skeleton `Omega_b^C`; in a
mixed-color reversal the second
skeleton must return the exact triple in (1103) while respecting the
root-matching disjointness across colors.  These are the two concrete
holonomy interfaces left by Sections 327--328.

## 330. A reversal to the original singleton has four boundary signatures

The one-edge normal form reduces a putative shortest reversal to a finite
`C_5` calculation.  Write the successor in (1103) as

```text
D={x,u,v},           E_zeta={u,v},                  (1104)
```

where the core edge `E_zeta` avoids `x`.  Apply the return transition
(1092) to `D`, and suppose that it returns to the original singleton:

```text
Phi(D)={x}.                                         (1105)
```

Its root boundary `R_D` is an odd nonempty subset of the three-element
set `D`.  Hence it is one of

```text
{x},       {u},       {v},       or D.              (1106)
```

For each choice, (1092) prescribes

```text
partial K_D=R_D triangle {x}.                       (1107)
```

On a five-cycle every even vertex shore has exactly two preimage edge
chains under `partial`; they differ by the full five-edge cycle.  Because
that cycle has odd size, exactly one of the two preimages has odd support.
The selected shore `Z_D` is odd by (1091), so (1107) determines it
uniquely.

The four possibilities are therefore:

```text
R_D={x}:     Z_D=Z, the full five-port shore;
R_D=D:       Z_D={zeta};
R_D={u}:     K_D is the unique odd x--u arc of C_5;
R_D={v}:     K_D is the unique odd x--v arc of C_5. (1108)
```

In the last two cases the odd arc has one or three edges, according as
the relevant endpoint of `E_zeta` is adjacent to `x` or at distance two.
Translating its edges back through `p_i |-> E_i`, this says
`|Z_D|` is respectively one or three.

Thus a realized `1 -> 3 -> 1` reversal cannot have an arbitrary odd
selected boundary.  Before any factor-label information is used, its
root/port projections must have exactly one of the four signatures in
(1108): full selected closure, exact reuse of the first selected port, or
one of two uniquely oriented odd arcs.  This classification is necessary,
not sufficient.  The off-incidence chain `L_D` must still realize the
listed side boundaries using active paths in one color, and a same- or
mixed-color realization must satisfy the holonomy interfaces of Section
328.  Those four cases are the finite targets for the next exclusion.

## 331. Every shortest reversal consumes three or five active path components

The boundary signatures already impose a nontrivial integer cost on the
six-edge graph `H_b^D`.  Let

```text
m:=|supp(L_D)|,
N:=|P_b(D)|                                          (1109)
```

for a putative reversal in Section 330.  Every odd-degree root and selected
port of `L_D` must be incident to a distinct support edge, so

```text
m>=max(|R_D|,|Z_D|).                                (1110)
```

This immediately gives `m>=3` in the `R_D=D` case and in either odd-arc
case with `|Z_D|=3`; the full-shore case gives `m>=5`.  The only remaining
possibility for `m=1` would be an endpoint-root signature, say
`R_D={u}`, whose odd arc has one edge.  That edge is the core edge joining
`x` to `u`; its selected port is therefore incident to `u`.  But every
edge of `L_D` is off-incidence by (1090), so the unique pair required by
a one-edge chain is forbidden.  Consequently

```text
m>=3 in every reversal signature,
m>=5 if R_D={x} and Z_D=Z.                          (1111)
```

Each support edge of `L_D` needs at least one distinct crossing path
occurrence, whence `m<=N`.  The crossing paths are distinct path components
of `H_b^D`; here `|D|=3`, so (1082) gives only six factor edges in total.
Finally `N` is odd by construction.  Thus

```text
3<=m<=N<=6,       N=1 mod 2,
so N in {3,5};
in the full-shore signature, N=5.                  (1112)
```

If `N=3` and `m=3`, the three terminal pairs are all distinct; no binary
cancellation has occurred.  If `N=5`, at least five of the six active
edges lie in different crossing path components.  In particular, in the
full-shore case `H_b^D` has no cycle and has at most one adjacency between
its six edges: it is five single-edge crossing components together with
either one unused single edge, or four single-edge components and one
two-edge crossing path.

Therefore the shortest recurrence left by Section 327 is not a cheap
parity reversal.  It must spend three or five disjoint active components
of one six-edge root-restricted factor, and the full selected closure has
the rigid near-matching normal form above.  The remaining label-holonomy
test may now be performed separately on the three-path and five-path
branches rather than on an arbitrary odd family.

## 332. A full-shore reversal has one forced and two binary root channels

The five-path branch of Section 331 has a still smaller terminal census.
Retain the notation

```text
D={x,u,v},        E_zeta={u,v},
R_D={x},          Z_D=Z                            (1113)
```

for the full-shore signature in (1108).  Equations (1111)--(1112) force
`m=N=5`.  Thus the five crossing-path occurrences give five distinct
support edges of `L_D`, and their selected endpoints are the five distinct
ports of `Z`, one each.

For `r in D`, let `n_r` be the number of these five terminal pairs whose
root coordinate is `r`.  Every such pair uses at its terminal a distinct
edge of `H_b^D` colored by `r`.  There are exactly two `b`-factor edges of
each root color, so

```text
0<=n_r<=2,
n_x+n_u+n_v=5.                                    (1114)
```

Because there is no cancellation and the root boundary is the singleton
`R_D={x}`, the occurrence parities are

```text
n_x=1 mod 2,       n_u=n_v=0 mod 2.                (1115)
```

The bounds and total in (1114) therefore leave only

```text
(n_x,n_u,n_v)=(1,2,2).                             (1116)
```

The unique `x`-rooted occurrence is also located.  The selected port
`zeta` represents the edge `{u,v}` and hence is incident to both `u` and
`v`.  Every terminal pair in `L_D` is off-incidence, while its root lies in
`D`.  Consequently the occurrence ending at `zeta` can use neither `u`
nor `v`, and must be the unique `x` occurrence:

```text
(x,zeta) in supp(L_D).                              (1117)
```

Remove `zeta` from the five-cycle of selected ports.  Of the remaining
four ports, the other port incident to `u` is forced to carry root `v`,
and the other port incident to `v` is forced to carry root `u`.  The last
two ports are incident to neither `u` nor `v`; (1116) assigns one to `u`
and the other to `v`.  Hence there are exactly two possible root--selected
support patterns for a full-shore reversal, exchanged by swapping those
last two assignments.

This conclusion is independent of whether a terminal reaches its selected
port directly or through a private-owner edge: the off-incidence statement
used in (1117) was proved for both terminal roles.  The formerly broad
five-path case is therefore reduced to two explicit cyclic patterns.  A
same-color holonomy exclusion need only test how the two root-colored
edges in each of the `u` and `v` channels can realize one of those patterns
inside `Omega_b^C`; a mixed-color exclusion must match the unique marked
pair `(x,zeta)` across the two color skeletons.

## 333. Every root has exactly seven singleton-return terminal tickets

The singleton returns across all exterior colors share a constant terminal
budget.  Fix `x in C`, and let `p_str(x)` be the unique selected port in
the strict-export cell of row `x` from (777).  Recall also the four-element
owner block `B_x` in (834).  For an exterior color `b`, the four entries
in its routing row at `x` are exactly the four endpoints of the two-edge
matching `H_b^{\{x\}}` from Section 329.

The exterior routing rows are support-disjoint.  On `Z` their union is the
single strict cell `p_str(x)`, while outside `Z` the exact partition (835)
gives `e\(Z union B_x)`.  Since

```text
e\(Z union B_x)=O disjoint_union (B\B_x),
|B\B_x|=6,                                         (1118)
```

the row endpoints satisfy the actual disjoint partition

```text
disjoint_union_(b exterior) V(H_b^{\{x\}})
 =O disjoint_union (B\B_x) disjoint_union {p_str(x)}. (1119)
```

Thus the terminal side of the singleton ledger is the fixed seven-point
set

```text
T_x:=(B\B_x) disjoint_union {p_str(x)},
|T_x|=7.                                           (1120)
```

For each color put

```text
o_x^b:=|V(H_b^{\{x\}}) intersect O|,
t_x^b:=|V(H_b^{\{x\}}) intersect T_x|.
```

Then (1119) gives the exact integer margins

```text
o_x^b+t_x^b=4,
sum_b o_x^b=2q-15,
sum_b t_x^b=7.                                     (1121)
```

The color `b` has an odd singleton shore precisely when `o_x^b` is odd,
equivalently when `t_x^b` is odd.  Consequently the number `k_x` of
colors available for a singleton return at `x` obeys

```text
k_x in {1,3,5,7}.                                  (1122)
```

For every such color, Section 329 supplies exactly one matching edge from
`O` to `T_x`.  These terminal endpoints are distinct across colors by
(1119), so the odd colors inject into the seven actual tickets rather than
merely into seven anonymous slots.

Their selected-port projection is equally rigid.  The six points of
`B\B_x` are the two private owner endpoints of each of the three selected
ports nonincident to `x`.  The strict port `p_str(x)` is one of those same
three ports.  After the optional owner append, the seven tickets therefore
project to the three possible singleton successors with multiplicities

```text
3,2,2,                                             (1123)
```

the multiplicity-three port being `p_str(x)`.  Hence all q-generic
singleton expansions at one root are controlled by a seven-ticket ledger
independent of `q`.  Any attempt to avoid the three-/five-path reversal
price of Section 331 by changing colors must still choose one of these
three located successor triples through one of the seven private terminal
tickets.

## 334. Exact selected-port reuse also has only two support patterns

Consider instead the second signature in (1108):

```text
R_D=D={x,u,v},       Z_D={zeta},       E_zeta={u,v}. (1124)
```

Let `n_r` again count crossing-path occurrences with terminal root `r`.
The root boundary now contains all three roots, so every `n_r` is odd.
Each is at most two because only the two root-`r` edges of `H_b^D` can
supply such terminals.  Hence

```text
n_x=n_u=n_v=1,
N=3.                                                (1125)
```

In particular the alternative `N=5` in (1112) is impossible for this
signature.  Equations (1111)--(1112) now give `m=N=3`, so the three
terminal pairs are distinct and no cancellation occurs.

Their selected-port occurrence multiset has total size three and binary
support the singleton `{zeta}`.  It cannot consist of three occurrences
at `zeta`: among the roots in `D`, only `x` is nonincident to the edge
`E_zeta={u,v}`, so off-incidence permits only the pair `(x,zeta)` there.
Consequently `zeta` occurs once and one other port `p` occurs twice.
The root counts (1125) then force

```text
supp(L_D)={(x,zeta),(u,p),(v,p)}.                  (1126)
```

The port `p` must be nonincident to both `u` and `v`.  On the five-cycle,
after deleting the edge `{u,v}` and its two endpoint-adjacent edges, there
are exactly two such ports: the two internal edges of the complementary
three-vertex path.  Either one can serve as `p` at the level of the
off-incidence boundary constraints.

Thus exact reuse of the selected port from the singleton expansion is not
an arbitrary three-path cancellation.  It has exactly two possible binary
support patterns, both consisting of the forced marked pair `(x,zeta)` and
a doubled selected endpoint carrying the two other root colors separately.
As in Section 332, existence inside the same- or mixed-color factor
skeleton remains to be tested; (1126) is the finite pattern that such a
holonomy realization must produce.

## 335. The seven tickets form one odd matching cut with a three-edge correction

The seven-ticket ledger is the terminal shore of one actual root matching.
Fix `x=x_i` and use the notation `T_x` from (1120).  The exterior-color
submatchings partition the matching `M_i` of Section 277, and (1119) says
that its exact support is

```text
V(M_i)=O disjoint_union T_x.                       (1127)
```

Both shores are odd.  Let

```text
C_x:=delta_(M_i)(O)=delta_(M_i)(T_x),
c_x:=|C_x|,
h_x:=|E(M_i[T_x])|.                                (1128)
```

Because `M_i` is a perfect matching on its support, every terminal ticket
is either the endpoint of one crossing edge or belongs to one internal
terminal pair.  Hence

```text
c_x=7-2h_x in {1,3,5,7},
h_x=(7-c_x)/2<=3.                                  (1129)
```

This is the aggregate version of the colorwise singleton returns.  If
`c_x^b` is the number of crossing edges in `H_b^{\{x\}}`, then

```text
c_x^b in {0,1,2},
c_x^b=t_x^b mod 2,
sum_b c_x^b=c_x.                                   (1130)
```

Thus every odd-return color from (1122) contributes its unique crossing
edge, while an even color contributes either zero or two.  Across all
colors the crossing endpoints are distinct actual tickets.

The optional owner append has an exact correction formula.  Let

```text
omega_x:T_x -> {the three selected ports nonincident to x}
```

send a private endpoint to its owner port and fix the strict ticket
`p_str(x)`.  By (1123), its three fibers have sizes `3,2,2`, with the
odd fiber over `p_str(x)`.  Construct a multigraph `J_x` on those three
selected ports by sending every internal terminal edge `{t,t'}` of
`M_i[T_x]` to an edge `{omega_x(t),omega_x(t')}`; retain parallel edges
and allow a loop when the two owners agree.  Then

```text
|E(J_x)|=h_x<=3.                                   (1131)
```

Let `Z_x^cross` be the symmetric difference of the selected endpoints
obtained by applying the owner append to all edges of `C_x`.  The seven
tickets split into the crossing endpoints and the paired endpoints of
`M_i[T_x]`.  Taking their owner images over `F_2`, the full `3,2,2`
ticket multiset reduces to `{p_str(x)}`, while every internal pair gives
one boundary contribution in `J_x`.  Therefore

```text
Z_x^cross={p_str(x)} triangle partial J_x.          (1132)
```

In particular `Z_x^cross` is odd and nonempty.  Equation (1132) replaces
an arbitrary choice among singleton-return colors by one canonical
rootwise route shore: it is the strict selected port corrected by the
boundary of at most three actual internal terminal pairs.  Any same- or
mixed-color reversal must refine this seven-ticket matching cut; changing
colors cannot alter the aggregate identity (1132), only how its crossing
edges are divided into one- and two-edge color contributions.

## 336. The two endpoint-root reversal signatures have seven supports

The two odd-arc cases left in (1108) can also be enumerated without any
factor-label choices.  Normalize the five-cycle as

```text
C=(x_0,x_1,x_2,x_3,x_4),
E_i={x_i,x_(i+1)},
x=x_0, u=x_1, v=x_2, zeta=p_1.                    (1133)
```

Thus `D={x_0,x_1,x_2}` and `E_zeta={u,v}`.  The nine allowed cells of the
off-incidence graph on `D times Z` are

```text
x_0: p_1,p_2,p_3;
u:   p_2,p_3,p_4;
v:   p_0,p_3,p_4.                                  (1134)
```

For the endpoint-root signature `R_D={u}`, the unique odd `x_0--u` arc is
`Z_D={p_0}`.  For `R_D={v}`, the unique odd `x_0--v` arc is its three-edge
complement `Z_D={p_2,p_3,p_4}`.  Section 331 says that the binary support
of `L_D` has weight three or five.  Solving the root and port parity
equations in the nine cells (1134) gives exactly the following supports.

For `R_D={u}` there are three:

```text
{(u,p_3),(v,p_0),(v,p_3)},
{(u,p_4),(v,p_0),(v,p_4)},
{(x_0,p_2),(x_0,p_3),(u,p_2),(v,p_0),(v,p_3)}.     (1135)
```

For `R_D={v}` there are four:

```text
{(x_0,p_2),(x_0,p_3),(v,p_4)},
{(u,p_2),(u,p_3),(v,p_4)},
{(u,p_2),(u,p_4),(v,p_3)},
{(x_0,p_2),(x_0,p_3),(u,p_3),(u,p_4),(v,p_3)}.     (1136)
```

For completeness, the enumeration is a short elimination rather than a
computer assumption.  In each row of (1134) the support parity is fixed
by `R_D`, and in each port column it is fixed by the displayed `Z_D`.
Choose the entries in the two three-cell rows for `x_0,u`; the `v` row is
then forced columnwise.  Rejecting weights other than three or five leaves
precisely (1135)--(1136), whose boundaries can be checked directly.

The occurrence census is compatible with this list.  If the endpoint root
is `r in {u,v}`, its crossing occurrence count is one, while the other two
root counts are even and at most two.  Hence a three-path realization uses
one of the other roots twice, whereas a five-path realization uses both
twice.  When `N=3`, `m=3` and there is no cancellation.  When `N=5`, either
`m=5`, or `m=3` and exactly one terminal pair occurs twice and cancels.

Together with Sections 332 and 334, (1135)--(1136) exhaust all binary
root--selected supports of a shortest `1 -> 3 -> 1` reversal: two patterns
in the full-shore case, two in the exact-reuse case, and these seven in the
two endpoint-root cases.  The remaining obstruction is therefore a finite
eleven-pattern holonomy test, with multiplicity ambiguity only in the
weight-three endpoint patterns realized by five crossing paths.

## 337. Only the strict ticket can support a terminal-correction loop

The loops allowed abstractly in `J_x` by Section 335 have only one
realizable source.  Suppose an internal matching edge `{t,t'}` of
`M_i[T_x]` joins two private tickets with the same owner port

```text
omega_x(t)=omega_x(t')=p.                           (1137)
```

Then `p` is adjacent in `A_e` to both `t` and `t'`.  The matching edge is
indexed by one exterior label `y`, which is also adjacent to both target
endpoints.  Thus `t,p,t',y` are four distinct vertices spanning the
four-cycle

```text
t -- p -- t' -- y -- t,                            (1138)
```

contrary to `C_4`-freeness.  Hence two private tickets in one owner fiber
can never form an internal terminal pair.

The two even fibers of `omega_x` have size two and consist entirely of
private tickets, so neither can produce a loop.  The odd fiber over
`p_str(x)` consists of the strict ticket itself and the two private owner
endpoints of that port.  Its only possible loop-producing pair therefore
uses the strict ticket and one of those two private tickets.  Since the
strict ticket belongs to at most one matching edge,

```text
J_x has at most one loop, and every loop is based at p_str(x). (1139)
```

Loops do not alter the boundary in (1132), but (1139) removes the only
spurious same-owner pairing multiplicity.  On the three nonincident
selected ports, `partial J_x` is either empty or a two-port set.  Therefore
the canonical aggregate return shore has the exact coarse form

```text
Z_x^cross is one of the three singleton ports, or all three ports. (1140)
```

The singleton `p_str(x)` occurs when `partial J_x=0`; another singleton
occurs when the boundary contains `p_str(x)` and that port; and the full
three-port shore occurs when the boundary is the other two ports.  This
does not yet choose among those four shores, because nonloop internal
pairs and parallel projected edges remain possible.  It does ensure that
any such correction is realized by cross-owner terminal pairs, apart from
at most one explicitly located strict/private loop.

## 338. Same-color endpoint reversals must erase or double the initial ticket

The initial singleton edge from Section 329 remains visible inside a
same-color second return.  Let its color be `b` and write it as

```text
e_0={s,t} in H_b^{\{x\}},
s in O,       t in Z union B,
zeta(t)=zeta,       D={x,u,v}, E_zeta={u,v}.       (1141)
```

At the terminal `t`, neither of the two new root colors `u,v` can supply
an edge of `H_b^D`.  If `t=zeta in Z`, its cells at the incident roots
`u,v` are core incidences, not exterior color-`b` cells.  If `t in B`,
Section 267 puts it in the owner blocks at precisely those same two roots,
again excluding exterior routing there.  The two root-`x` edges form a
matching, so no second one meets `t`.  Therefore

```text
deg_(H_b^D)(t)=1.                                  (1142)
```

Let `Q_0` be the path component of `H_b^D` containing `e_0`.  If its other
endpoint lies in `O`, then `Q_0` is one of the crossing paths in (1085),
and its terminal pair is exactly

```text
(x,zeta).                                          (1143)
```

Both endpoint-root signatures in Section 336 have selected boundary which
omits `zeta`, and none of their seven binary supports contains (1143).
Hence a same-color realization of one of those signatures has exactly two
ways to dispose of the initial ticket.

First, `Q_0` may cease to cross the residual shore.  Since its endpoint
`t` remains degree one outside `O`, its other endpoint must then also lie
outside `O`.  In particular the original residual endpoint `s` cannot
remain degree one: one of the new root colors attaches there, so

```text
deg_(H_b^D)(s)=2,
d_s^b=2,                                           (1144)
```

and `Q_0` becomes a terminal-to-terminal path.

Second, `Q_0` may remain crossing and contribute (1143), but that pair
must cancel with one further crossing occurrence having the same root and
selected endpoint.  Section 336 shows that cancellation is possible only
in its `N=5,m=3` branch, where there is exactly one doubled terminal pair.
That unique doubled pair is then forced to be `(x,zeta)`.

Thus an endpoint-arc reversal in one color cannot simply forget the marked
singleton edge.  It either pays the local double-hit (1144) and transports
the edge into a terminal--terminal component, or it uses the five-path
branch and spends its sole cancellation on a second realization of the
same marked ticket.  This dichotomy is specific to same-color reversal;
for a mixed-color second step the initial edge is not present in the new
restricted factor and the interface must instead be enforced through the
two color skeletons of Section 328.

## 339. A same-color full-shore reversal preserves the initial edge

The full-shore signature has no erase-or-double ambiguity.  Keep the
same-color notation (1141), and let `e_1` be the other root-`x` edge of
`H_b^{\{x\}}`.  Section 329 says that `e_0` is the unique crossing edge of
this two-edge matching.  Hence `e_1` is noncrossing: its two endpoints are
both in `O` or both outside `O`.

Section 331 gives five crossing path components in the six-edge graph
`H_b^D`.  Its near-matching classification leaves only two cases.  If all
six edges are isolated, `e_0` remains its original one-edge crossing
component.  Otherwise the graph has exactly five components: four isolated
edges and one two-edge path.  All five components must then be crossing.

The sole adjacency cannot meet `e_0`.  If it did, `e_1` would remain an
isolated noncrossing component, leaving at most four crossing components,
contrary to `N=5`.  In fact the adjacency must meet `e_1`; if it met neither
root-`x` edge, the same noncrossing isolated component would remain.
Consequently

```text
e_0 is an isolated crossing component of H_b^D.     (1145)
```

Its outside terminal is the same literal ticket `t` as in the singleton
step, not merely another ticket with the same owner projection.  Therefore
it contributes the terminal pair `(x,zeta)`.  Section 332 proved that a
full-shore reversal has exactly one root-`x` occurrence, so

```text
the unique x-rooted channel in (1117) is the original edge e_0. (1146)
```

Thus a same-color full selected closure preserves the marked singleton
edge rigidly while its other five factor edges arrange the two `u` and two
`v` channels and at most one adjacency.  Any holonomy contradiction for
the two full-shore patterns of Section 332 may treat `(x,zeta)` as a fixed
literal terminal ticket, rather than only a binary root--port pair.  This
strengthening is not asserted for a mixed-color reversal, where the second
restricted factor does not contain `e_0`.

## 340. The exact-reuse reversal survives the current holonomy skeleton

The persistence results of Sections 338--339 do not cover the exact-reuse
signature, and that omission is essential: the present invariant package
admits a nested same-color realization of either support in (1126).

Fix one of the two ports `p` nonincident to both `u` and `v`.  Choose three
terminal tickets

```text
t_x:=zeta in Z,
t_u,t_v in B,       omega(t_u)=omega(t_v)=p,        (1147)
```

where `t_u,t_v` are the two distinct private owner endpoints over `p`.
Choose nine distinct residual ports

```text
s_x,s_u,s_v,
a_x,b_x,a_u,b_u,a_v,b_v in O.                      (1148)
```

This is available already at the first surviving binary-power parameter,
where `|O|=2q-15>=17`.  Define the six root-colored edges of `H_b^D` by

```text
e_r^0={s_r,t_r},
e_r^1={a_r,b_r},             r in {x,u,v}.          (1149)
```

They form a matching, with exactly two edges of every root color.  In the
singleton restriction `H_b^{\{x\}}`, the residual degree-one shore is

```text
{s_x,a_x,b_x},                                      (1150)
```

so `e_x^0` is its unique crossing edge.  It is the one-edge expansion of
Section 329 through the strict ticket `zeta`, and its successor is exactly
`D={x,u,v}`.

In the triple restriction all six edges remain isolated.  Its residual
degree-one shore consists of the nine ports in (1148), and its three
crossing components are `e_x^0,e_u^0,e_v^0`.  Their terminal pairs are

```text
(x,zeta),       (u,p),       (v,p).                 (1151)
```

Thus `N=m=3`, the binary support is precisely (1126), and the selected
boundary is `{zeta}` because the two occurrences of `p` cancel.  Therefore

```text
Phi({x,u,v})={x,u,v} triangle Ends(E_zeta)={x}.     (1152)
```

All pointwise constraints used so far are respected.  The two private
tickets over `p` are not internally paired, so Section 337 creates no
four-cycle; each receives only its displayed root-`b` occurrence inside
`D`, and its other ticket letters may satisfy the nonmonochromatic cap.
The six active edges are disjoint, so the proper root coloring and every
root-matching condition hold.

The construction also extends to the ten-label skeleton of Section 328.
Add the four active edges belonging to the other two roots on fresh ports,
keeping all ten active edges disjoint.  Pair their twenty target darts by
`C`-inactive complement paths to complete `F_b[e]`; on the root side give
each active label a fresh outside root and pair those endpoints by outside
paths to complete `F_b[c]`.  This realizes the two involutions and their
four-regular overlay without introducing a shared active port.  The
choices may be made with single inactive edges or longer fresh paths; no
specific global completion is asserted.

Hence (1147)--(1152) are not a counterexample to the original graph
problem, but they are a countermodel to an exclusion based only on the
active-factor paths, ticket role census, and per-color ten-label holonomy
recorded through Section 339.  A proof cannot rule out all shortest
reversals by analyzing one `Omega_b^C` in isolation.  It must add a genuine
cross-factor constraint--for example the other letters of the two private
tickets, simultaneous root-matchings in their colors, or the global
component profile retained in Section 324.  This identifies the exact
information missing from the finite eleven-pattern test.

## 341. Full-shore persistence consumes two tickets at each new root

The same near-matching argument determines the four new root edges
individually.  Let `f_u^0,f_u^1` be the two root-`u` edges and
`f_v^0,f_v^1` the two root-`v` edges in `H_b^D`.  If all six edges of the
restricted graph are isolated, Section 339 leaves `e_1` as the unique
noncrossing component.  Hence each of the four `f` edges is itself an
`O`--terminal crossing edge.

Suppose instead that the sole adjacency joins `e_1` to one new edge `f`.
The two endpoints of the noncrossing edge `e_1` lie on the same physical
shore: both are in `O`, or both are outside `O`.  The two-edge component
`e_1 union f` must cross.  Its endpoint on `e_1` therefore lies on the
opposite shore from the free endpoint of `f`.  The shared endpoint of
`e_1` and `f` lies on the same shore as the first endpoint, so `f` itself
also has one endpoint in each shore.  The other three new edges are
isolated crossing components.  Thus in both near-matching cases

```text
each f_u^j and f_v^j is an O--terminal edge.        (1153)
```

Apply the singleton ticket notation of Section 333 at the roots `u,v`.
Equation (1153) says that the same exterior color `b` has

```text
c_u^b=c_v^b=2,
o_u^b=t_u^b=o_v^b=t_v^b=2.                         (1154)
```

In particular `b` is not an odd singleton-return color at either new root,
even though it was an odd return color at the predecessor root `x`.
Moreover the two `u` channels and the two `v` channels of (1116) use four
distinct literal terminal tickets, two in each root ledger; their selected
owner projections are exactly one of the two patterns in Section 332.

Consequently a same-color full-shore reversal has the exact rootwise ticket
profile

```text
x: one marked crossing edge e_0 and one noncrossing edge e_1;
u: two crossing edges;
v: two crossing edges.                             (1155)
```

This is stronger than the binary `(1,2,2)` terminal-root census: it records
that no cancellation or internal terminal pairing is hidden in the four
new channels.  A final same-color price may therefore charge the transition
from one odd ticket at `x` to two even ticket pairs at `u,v`; only the
mixed-color branch can avoid this literal six-edge profile.

## 342. Exact reuse forces a second color on a private terminal ticket

The local countermodel in Section 340 cannot be closed as a genuinely
one-color object once the other letters of its private tickets are
retained.  In the exact-reuse support (1126), the doubled selected port
`p` carries the two distinct terminal occurrences

```text
(u,p),        (v,p),                                (1156)
```

and `p` is incident to neither root.  Among all exterior routing colors,
the `C times Z` block contains only the one strict-export cell at `p` from
(777).  Therefore at most one occurrence in (1156) can terminate directly
at the selected port.  At least one must have the owner-return form

```text
r --[color b label]-- w --[A_e owner edge]-- p,
r in {u,v},       w in B,       p(w)=p.             (1157)
```

The root support of the private ticket `tau(w)` is

```text
C\Ends(E_p)={u,v,w_p}                              (1158)
```

for the third root `w_p` nonincident to `p`.  Notice that `w_p` equals
`x` for one of the two possible exact-reuse ports and differs from `x`
for the other; no identification with the predecessor triple is assumed.
The occurrence (1157) supplies a color-`b` letter at the ticket root `r`.
By the nonmonochromatic ticket theorem (844), the other two letters cannot
both also have color `b`.  Hence there exist

```text
r' in {u,v,w_p}\{r},       b'!=b,                  (1159)
```

and an actual color-`b'` label routing the cell `(r',w)`.

Thus every exact-reuse reversal, including the same-color realization of
Section 340, exposes at least one second exterior color at the same literal
private terminal used by the reversal.  If both occurrences in (1156) use
owner returns, the argument applies to both tickets, although their forced
side colors need not be distinct.

This is not yet a contradiction: Section 340 explicitly left those ticket
letters free, and they can satisfy nonmonochromaticity locally.  It is the
first unavoidable interface beyond the one-color skeleton `Omega_b^C`.
Any completion of that countermodel must extend the marked terminal `w`
into the root matching and ten-label skeleton of some `b'!=b`, or pay the
same cell through the coupled partition `SRP(b',e)`.  The next exclusion
may therefore work on this located two-color interface rather than on an
arbitrary choice of a second color.

## 343. The forced side color is absorbed strictly or exits the owner fiber

Retain the private ticket `w`, side root `r'`, and color `b'` from (1159),
and let `y'` be the actual intermediate label routing `(r',w)`.  Since
`y'` meets the selected root component `C` at `r'`, it indexes one edge of
the active factor `H_(b')^C`.  Write

```text
g'={w,w'} in H_(b')^C.                              (1160)
```

Let `w^sib` be the other private owner endpoint over the same selected port
`p`.  The new edge cannot join the two siblings:

```text
w'!=w^sib.                                         (1161)
```

Indeed `w` and `w^sib` are both adjacent to `p` in `A_e`.  If `y'` were
also adjacent to both, then

```text
w -- p -- w^sib -- y' -- w
```

would be a four-cycle, exactly as in the private/private loop exclusion of
Section 337.

There are now two exhaustive roles for the other endpoint.  If

```text
w'=p,                                               (1162)
```

then the cell `(r',p)` is an exterior active cell at a selected port.  By
the strict permutation (777), it is necessarily the unique strict export
at `p`; in particular its receiving color is `b'` and its strict root is
`r'`.  The forced side letter is absorbed by a completely located
strict--private factor edge.

Otherwise `w'` lies outside the three-point owner fiber

```text
{p,w,w^sib}.                                       (1163)
```

It may be residual, belong to another private owner fiber, or be a
different selected port, but in every case (1160) is an actual
color-`b'` active edge which exits the owner fiber supporting the
exact-reuse cancellation.

Thus the nonmonochromatic side letter from Section 342 cannot be hidden by
pairing the two private tickets which caused the doubled selected endpoint.
It obeys the exact dichotomy

```text
strict absorption at p,
or a b'-factor escape out of the owner fiber.       (1164)
```

If both occurrences in (1156) are private, applying the argument to both
tickets gives two distinct side edges: one label cannot join the siblings
by (1161), although the two side colors are still allowed to coincide.
The strict permutation has only one exterior cell at `p`, so these two
distinct edges cannot both satisfy (1162).  Consequently at most one is
absorbed at `p`, and at least one side edge exits the owner fiber.
Equation (1164) is the first genuine two-color propagation constraint on
the countermodel of Section 340.  A remaining completion must either spend
one of the five strict exports in the new color or propagate into a new
port role where the global matching and component ledgers can charge it.

## 344. A private reversal ticket has a singleton escape or a side-color path

The exact-reuse matching locates the color multiplicities at the private
ticket more sharply.  Retain `w` and its terminal root `r` from (1157).
In the six-edge matching `H_b^D` of Section 340, the terminal `w` has degree
one.  Therefore no other ticket root which lies in `D` can carry color `b`:

```text
rho in (C\Ends(E_p)) intersect D, rho!=r
implies the letter at (rho,w) has color different from b.  (1165)
```

If the third ticket root `w_p` lies outside `D`, it may still carry a
second color-`b` letter; (1165) is deliberately restricted to the roots
seen by the reversing factor.

Now inspect the three colors on `tau(w)`.  At least one is `b`, and the
ticket is nonmonochromatic.  Exactly one of the following alternatives
holds.

* Some side color `a!=b` occurs exactly once on the ticket.  Its active
  factor has degree one at `w`, so its edge is a genuine singleton side
  edge and obeys the strict-absorption/owner-fiber-escape dichotomy (1164).
* No non-`b` color occurs once.  Then `b` occurs exactly once and the two
  other ticket letters have one common color `a!=b`.

In the second case let their distinct labels be `y_1,y_2`, rooted at the
two non-`b` ticket roots.  They give two incident edges of `H_a^C` and hence
an actual two-edge path

```text
q_1 --[y_1]-- w --[y_2]-- q_2.                    (1166)
```

The far endpoints are distinct.  If `q_1=q_2`, the two labels `y_1,y_2`
would have the two common `e`-neighbors `w,q_1`, producing a four-cycle.
Thus

```text
q_1!=q_2,                                          (1167)
```

and the forced second color transports through `w` rather than terminating
there.

Consequently the freedom left in Section 342 is not an arbitrary coloring
of two unused ticket letters.  Every private exact-reuse terminal exposes
either a degree-one cross-color edge to which Section 343 applies, or a
proper two-edge path in one side color joining two distinct target ports.
When `w_p=x`, all three ticket roots lie in `D`, so (1165) forces `b` to
occur exactly once; the two remaining roots are both non-`b` and fall
directly into this dichotomy.  This singleton-or-path normal form is the
next interface for coupling the reversal to `SRP(a,e)` and the self factor
`A_a`.

## 345. Every exact-reuse reversal forces a side-color escape

The path alternative of Section 344 has the same owner-fiber consequence
as the singleton side edge.  Let `w^sib` again be the sibling private ticket
over `p`.  Neither far endpoint in (1166) can equal `w^sib`: either equality
would make `w,w^sib` share both the owner `p` and the corresponding side
label, giving the four-cycle from (1161).  Together with (1167),

```text
q_1,q_2 are distinct and neither is w^sib.          (1168)
```

At most one of them can equal the remaining point `p` of the owner fiber.
If one does, that edge is the uniquely located strict side-color absorption
described in (1162).  The other far endpoint necessarily lies outside
`{p,w,w^sib}`.  Hence the two-edge side-color path always contains at least
one actual edge which exits the owner fiber.

Combine this with the singleton alternative and (1164).  Every private
terminal ticket forced by exact reuse satisfies the sharp dichotomy

```text
one singleton side-color edge is absorbed strictly at p;
or at least one side-color edge exits {p,w,w^sib}.  (1169)
```

For an exact-reuse reversal, even the first line cannot eliminate every
escape.  If exactly one of the two occurrences `(u,p),(v,p)` is private,
the other occurrence is the unique direct strict cell at `p`, and its color
is the reversal color `b`.  Every side color supplied by the private ticket
is different from `b`, so strict uniqueness forbids its absorption at `p`.
The singleton side edge must escape by (1164), and the path alternative
already escapes by (1168).

If both occurrences are private, applying (1169) to both tickets again
forces an escape: the strict permutation supplies only one exterior cell at
`p`, so at most one ticket can use its first line.  Therefore in all cases

```text
every exact-reuse reversal has a marked side-color edge
leaving the owner fiber of its doubled selected port.       (1170)
```

Equation (1170) removes the last purely local completion of the private
ticket letters in Section 340.  The escaping edge can be fed into the
component profile of Section 324 or the simultaneous partition `SRP(a,e)`;
it cannot be absorbed by rearranging the two sibling tickets which caused
the selected-port cancellation or by spending the already occupied strict
cell.

## 346. Side-color escape either terminates or enters a thirty-state cycle

The escape in (1170) can be iterated without forgetting its incoming
label.  For a private ticket `w in B`, its three routed root occurrences
in (843) are three distinct active labels.  Define the finite arrival-state
set

```text
Scal_B:={(w,y):w in B and y is one of the three labels of tau(w)},
|Scal_B|=30.                                        (1171)
```

Suppose an active label `y_in` arrives at `w` from its other `e`-endpoint.
The ticket is nonmonochromatic, so among its other labels there is a label
`y_out` whose color differs from the color of `y_in`.  Follow the
`F_(color(y_out))[e]` edge indexed by `y_out` from `w` to its other
endpoint `w'`.

Two immediate returns are forbidden.  The endpoint `w'` cannot be the
sibling private ticket over `p(w)`, since those tickets already have their
owner port as a common neighbor and `y_out` would create the four-cycle of
(1161).  It also cannot be the preceding endpoint of `y_in`: otherwise
that endpoint and `w` would have the two distinct common labels `y_in` and
`y_out`.  Thus whenever `w'` is private,

```text
w' is in B, its owner fiber differs from that of w,
and the propagation does not immediately reverse.                 (1172)
```

If `w'` lies in `O`, propagation has reached a residual port.  If it lies
in `Z`, the exterior selected cell is necessarily a strict export.  These
are the two terminal roles.  If `w'` lies in `B`, continue from the new
arrival state `(w',y_out)`.

Because `Scal_B` has only thirty states, every such sequence has the exact
dichotomy

```text
reach O or a strict selected endpoint; or
repeat an arrival state and contain a directed state cycle.        (1173)
```

The cycle has length between three and thirty.  Length one is impossible
for a factor edge, and length two is excluded by the no-reversal part of
(1172).  At every state on it the outgoing label color differs from the
incoming label color, including at the closing state because the full
arrival state, not merely its ticket, is repeated.  Consecutive private
tickets also belong to different owner fibers.

Apply this construction to the mandatory escaping edge of (1170).  If its
far endpoint is residual or selected, the exact-reuse countermodel has
already paid a new located terminal role.  If it is private, (1173) gives
either such a terminal after further forced color changes, or a bounded
cross-color private-ticket holonomy cycle.  This is not yet an exclusion:
the same ticket may occur in a cycle with different incoming labels, so a
ten-ticket simple-cycle claim is not made.  The important reduction is
that indefinite propagation is confined to a q-independent thirty-state
object with no monochromatic transition and no immediate owner-fiber
reversal.

## 347. The owner/root/color projection already admits a three-state cycle

The cycle branch of (1173) cannot be excluded from only the owner ports,
core roots, and consecutive color changes.  There is a minimal explicit
model.  Index the selected core cyclically as before, and choose one private
ticket `w_i` over each of the three consecutive owner ports

```text
p_0=E_0,       p_1=E_1,       p_2=E_2.             (1174)
```

Introduce three distinct active labels `y_0,y_1,y_2` with three distinct
exterior colors and set their target-factor edges and core roots to be

```text
y_0: {w_0,w_1}, root x_3;
y_1: {w_1,w_2}, root x_0;
y_2: {w_2,w_0}, root x_4.                          (1175)
```

Every entry is a legitimate ticket letter.  The roots available at a
ticket over `p_i` are the three vertices outside `Ends(E_i)`.  Hence

```text
w_0 admits roots x_4,x_3,
w_1 admits roots x_3,x_0,
w_2 admits roots x_0,x_4,                           (1176)
```

and the two displayed roots at each ticket are distinct.  Complete each
ticket by its unused third root and any color consistent with the
nonmonochromatic cap; the two incident cycle colors are already distinct.

The three arrival states then form the directed cycle

```text
(w_0,y_2) -> (w_1,y_0) -> (w_2,y_1) -> (w_0,y_2). (1177)
```

Consecutive tickets have distinct owner fibers, no step hits a sibling,
and no step immediately reverses.  Any two tickets share only their one
displayed transition label, so the local common-neighbor constraints which
created (1172) are respected.  The unused darts of the three color factors
and the remaining ticket letters can be paired on fresh local states, just
as in the skeleton completion of Section 340.

This is an abstract countermodel to the projection retained in Section
346, not a completion of the ambient graph or of all simultaneous routing
partitions.  It proves that neither cycle length, owner sequence, core-root
incidence, nor the rule of consecutive color change can by itself price the
cycle branch.  Any exclusion must use information absent from (1174)--
(1177), such as the self factors `A_(color(y_i))`, the coupled partitions
`SRP(color(y_i),e)`, or the outside component tags of the displayed labels.

## 348. Even two colors admit a four-state propagation cycle

Boundedness in (1173) is not itself a contradiction.  There is already a
four-state cycle satisfying every owner, root-support, color-change, and
immediate-return constraint used in Section 346.  Take both private tickets
in each of two consecutive owner fibers,

```text
T_0={w_0,w'_0},             T_1={w_1,w'_1}.         (1178)
```

The routed root supports from (841) are

```text
supp tau(T_0)={x_2,x_3,x_4},
supp tau(T_1)={x_3,x_4,x_0}.                         (1179)
```

Choose four distinct exterior labels with the following private endpoints,
roots, and two alternating colors `a!=b`:

```text
y_0: {w_0,w_1},   root x_3, color a;
y_1: {w_1,w'_0},  root x_4, color b;
y_2: {w'_0,w'_1}, root x_3, color a;
y_3: {w'_1,w_0},  root x_4, color b.                (1180)
```

Every displayed root belongs to both endpoint tickets' supports.  At each
ticket the two cycle labels occupy the distinct roots `x_3,x_4`, and their
colors differ.  Consecutive tickets have different owners; the only pairs
with a common owner are the opposite pairs `{w_0,w'_0}` and
`{w_1,w'_1}`, and (1180) does not join either pair.  No two tickets share
two displayed labels, and no two displayed labels share two tickets, so
the local incidence pattern creates an alternating eight-cycle rather than
a forbidden four-cycle.

Complete each of the four tickets' unused third root occurrence by a fresh
label with a fresh residual far endpoint.  Its color can be chosen so that
the ticket multiplicity cap (844) remains at most two.  Then the transition
rule may follow

```text
(w_0,y_3) -> (w_1,y_0) -> (w'_0,y_1)
 -> (w'_1,y_2) -> (w_0,y_3),                        (1181)
```

and every step changes color and avoids both the sibling and the preceding
ticket.  Thus (1181) is a literal four-cycle in the arrival-state dynamics.

This construction is deliberately a local ticket-layer realization, not a
completion of all factor degrees or the full simultaneous routing
partition.  It proves that owner projection, root support (841), ticket
nonmonochromaticity, and the C4 exclusions of Section 346 do not eliminate
the cycle branch of (1173), even with only two side colors.  Any next price
must use information omitted here--for example the exact per-color cut
census (787), the self factors `A_a,A_b`, or the incidence-component profile
of Section 324--rather than only the thirty-state transition graph.

## 349. Coupled SRP forces a fifth selected-cell tag on every ticket transition

The local cycle countermodels leave one selected cell in a different
simultaneous partition unspecified.  Let a propagation label `y` have
color `a`, core root `r in C`, and private target endpoints

```text
N_e(y)={w,w'},       p(w)=p, p(w')=p',       p!=p'. (1182)
```

The two owner ports are distinct by (1172).  Apply `SRP(a,e)` and inspect
the row indexed by the endpoint vertex `y in a`, restricted to `Z`.

First consider routing color `c`.  The label `y` has exactly one
`c`-neighbor in `C`, namely `r`, and its other `c`-neighbor lies outside
`C` by (779).  Since `(C,Z)` is a whole component of `R_ce`, only `r`
contributes selected endpoints.  Therefore

```text
supp((R_ac R_ce)[y,-]) intersect Z
 =N_e(r) intersect Z,                              (1183)
```

the two selected ports incident to `r`.

Next consider endpoint color `e`.  Each private ticket has exactly one
`A_e`-neighbor in `Z`, its owner port, so

```text
supp((R_ae A_e)[y,-]) intersect Z={p,p'}.           (1184)
```

Because `r` is a ticket root at both `w` and `w'`, it is incident to
neither owner port.  Thus the two sets in (1183)--(1184) are disjoint and
occupy four of the five selected columns.  Let `q(y)` be the remaining
port.  Equivalently,

```text
q(y) is the third selected port nonincident to r,
distinct from p and p'.                             (1185)
```

The exact support partition now assigns the cell `(y,q(y))` to a unique
intermediate component

```text
kappa(y) notin {c,e}.                               (1186)
```

If `kappa(y)=a`, this is an endpoint-layer path through an actual internal
neighbor of `y` in `A_a`; otherwise it is a path through an actual vertex
of a fourth component:

```text
y --[vertex in kappa(y)]-- q(y).                    (1187)
```

Hence every private-to-private propagation edge carries a canonical
fifth-cell tag `(q(y),kappa(y))` supplied by `SRP(a,e)`.  It is not visible
in the owner/root/color words of Sections 347--348: those words determine
`q(y)` but do not choose the paying layer `kappa(y)`.  In particular the
three- and four-state cycle countermodels are not full-SRP countermodels
until all their fifth cells are paid compatibly with the reused self and
cross blocks.

This is still a forcing statement rather than an exclusion.  Its point is
to place the missing invariant exactly: a cycle branch must admit a
simultaneous assignment of the tags (1186), where choosing the endpoint
layer consumes `A_a` at the propagation label and choosing another color
creates a new cross-color route.  The next price can act on those actual
layer tags instead of adding another projection of the already exhausted
owner/root cycle.

## 350. Repeated transition signatures force fifth-cell saturation

The tag in Section 349 has a sharp collision rule.  Let `y_0,y_1` be two
distinct propagation labels in one color `a` with the same core root `r`
and the same unordered pair of private owners `{p,p'}`.  Their four forced
selected cells in (1183)--(1184) coincide, so

```text
q(y_0)=q(y_1)=:q.                                  (1188)
```

For `i in {0,1}`, write the uniquely tagged fifth-cell route as

```text
y_i -- z_i -- q,       z_i in kappa(y_i).           (1189)
```

The payment vertices are distinct.  Indeed, `y_0,y_1` already have the
common neighbor `r`.  If `z_0=z_1`, that vertex would be their second common
neighbor and would produce the four-cycle

```text
y_0 -- r -- y_1 -- z_0 -- y_0.
```

Consequently, if the two layer tags agree, say

```text
kappa(y_0)=kappa(y_1)=k,                            (1190)
```

then `z_0,z_1` are exactly the two `k`-neighbors of `q`: every cross block
has degree two, and both slots have now been used.  Thus a repeated
owner/root/color signature cannot hide two fifth-cell payments in one
vertex.  Equal tags consume the whole `q`--`k` fiber; unequal tags create
two separately located cross-color obligations.

The two-color cycle of Section 348 contains this collision twice.  With
the cyclic convention that `x_i` is incident to `p_(i-1),p_i`, its two
color-`a` labels have root `x_3` and owners `{p_0,p_1}`, while its two
color-`b` labels have root `x_4` and the same owner pair.  Hence

```text
q(y_0)=q(y_2)=p_4,
q(y_1)=q(y_3)=p_2.                                  (1191)
```

For either pair, agreeing tags saturate the corresponding selected port in
that payment layer by (1190); disagreeing tags force two different payment
layers at the same selected port.  This does not yet exclude the abstract
cycle, but it upgrades each repeated transition from a free fifth cell to
an exact degree-two capacity event.  A full completion of Section 348 must
now realize both saturation-or-splitting decisions simultaneously with the
self factors and the other SRP rows.

## 351. Endpoint-layer saturation forms a three-axis rectangle

Apply Section 349 to the two-color four-state cycle (1180).  The two
color-`a` labels `y_0,y_2` have the same root `x_3` and the same pair of
owner ports `{p_0,p_1}`.  Therefore

```text
q(y_0)=q(y_2)=p_4.                                 (1192)
```

Suppose first that either fifth cell has `kappa(y_i)!=a`.  Then (1187)
already supplies a genuine exterior-component tag on the cycle.  The only
remaining case has

```text
kappa(y_0)=kappa(y_2)=a.                           (1193)
```

Let `z_0,z_2` be the actual `A_a` neighbors paying the two cells:

```text
y_0 --[A_a]-- z_0 -- p_4,
y_2 --[A_a]-- z_2 -- p_4.                          (1194)
```

They are distinct.  If `z_0=z_2`, the propagation labels `y_0,y_2`
would have the two common neighbors `x_3` and `z_0`, giving a four-cycle.
Since a selected `e`-port has exactly two neighbors in color `a`, the two
distinct payments saturate its cross fiber:

```text
N_a(p_4)={z_0,z_2}.                                (1195)
```

Equivalently, the repeated root gives the root-axis edge
`y_0--y_2` in `F_c[a]`, the saturated port gives the target-axis edge
`z_0--z_2` in `F_e[a]`, and the self factor supplies the two cross edges
in (1194).  Their ambient lifts form the actual six-cycle

```text
y_0 -- x_3 -- y_2 -- z_2 -- p_4 -- z_0 -- y_0.    (1196)
```

Thus two endpoint-layer payments do not disappear into arbitrary self
neighbors: they create a rigid three-axis rectangle on four color-`a`
labels and consume the whole `a`-fiber of the fifth selected port.

The color-`b` pair is identical after replacing

```text
(y_0,y_2,x_3,p_4,a) by (y_1,y_3,x_4,p_2,b).        (1197)
```

Consequently every full-SRP completion of the four-state witness has the
exact dichotomy

```text
some propagation label carries an exterior fifth-cell tag; or
both colors form the saturated rectangles (1196)--(1197). (1198)
```

This still does not declare the ticket cycle impossible: a six-cycle is
allowed by `C_4`-freeness.  It does, however, replace the free self-factor
completion suggested after (1181) by two explicit constant-size objects.
The exterior branch can be charged by component/color propagation, while
the endpoint-layer branch must realize two saturated selected fibers and
their paired `A_a,A_b` cross edges simultaneously.

## 352. Every fifth-cell payer is strict or core-inactive

The actual intermediate in (1187) has a useful dichotomy relative to the
original core.  Write the uniquely witnessed fifth-cell route as

```text
y -- z(y) -- q(y),       z(y) in kappa(y).          (1199)
```

If `z(y)` has a neighbor `r' in C`, then `(r',q(y))` is an exterior
`C`-by-`Z` cell paid through `z(y)`.  The rigid support permutation (777)
has exactly one such cell in the column `q(y)`.  Hence `z(y)` is precisely
the unique strict export at that selected port.  Otherwise

```text
N_c(z(y)) intersect C = emptyset.                  (1200)
```

Call the latter payer core-inactive.  Thus every fifth-cell tag has the
exhaustive refinement

```text
z(y) is the strict export at q(y), or z(y) is core-inactive. (1201)
```

This refinement also has exact local capacities.  Fix the endpoint color
`a`, a paying layer `k notin {c,e}`, and a selected port `q`.  The column
of the routing product

```text
Q_k^(a,e)=R_ak R_ke
```

has integer sum four: `q` has two `k`-neighbors and each of them has two
neighbors in `a` (with `R_aa=A_a` when `k=a`).  Since the simultaneous
partition is entrywise exact, its four contributions occupy four distinct
rows.  Consequently

```text
#{propagation y in a : (kappa(y),q(y))=(k,q)} <= 4. (1202)
```

There is a sharper bound in the strict branch.  A selected port `q` has
one strict-export label `z_q`, in one determined component `k`.  For fixed
endpoint color `a`, the rows whose fifth cell is paid through `z_q` are
neighbors of `z_q` in `R_ka` (or in `A_a` if `k=a`).  That degree is two,
so

```text
#{propagation y in a : z(y)=z_q} <= 2.              (1203)
```

Therefore a tagged propagation cycle cannot reuse fifth cells without
cost: each fixed layer--port tag has four row slots in total, and its
strict half has only two.  Any further occurrences at that tag must use
core-inactive payers.  This does not yet bound those inactive labels
globally, but separates the five already-accounted strict exports from the
new exterior population that a full completion must supply.

## 353. Every repeated transition signature forces an inactive payer

Combine the collision rule of Section 350 with the strict/inactive
dichotomy.  Let `y_0,y_1` be a repeated owner/root/color signature and let
`q` be their common fifth port.  Their payment intermediates `z_0,z_1` are
distinct by the four-cycle argument following (1189).  But Section 352
gives only one strict-export label at `q`, across all payment layers.
Therefore

```text
at least one of z_0,z_1 is core-inactive.           (1204)
```

This conclusion does not require the tags `kappa(y_0),kappa(y_1)` to
agree.  If they agree, the two payers saturate that layer's fiber at `q`
and its strict/inactive profile is either `(1,1)` or `(0,2)`.  If the tags
differ, at most one of the two layers can contain the globally unique
strict label at `q`, so the other tagged route is inactive.

Apply (1204) to the two repeated pairs in Section 348.  Choose

```text
z_4 in {z(y_0),z(y_2)} with
     z_4 adjacent to p_4 and N_c(z_4) intersect C=emptyset;
z_2 in {z(y_1),z(y_3)} with
     z_2 adjacent to p_2 and N_c(z_2) intersect C=emptyset. (1205)
```

These two inactive labels are distinct.  Indeed every exterior label has
at most one selected `e`-neighbor by (785), whereas `p_4!=p_2`.  Thus the
two-color four-state cycle forces at least two different, fully located
port-only cut labels:

```text
z_4 contributes an N_01 occurrence at p_4,
z_2 contributes an N_01 occurrence at p_2.         (1206)
```

The endpoint-layer rectangles of Section 351 do not evade this price.  In
each rectangle the two distinct self-layer payers share the fifth port, so
at most one can be that port's strict export and the other is one of the
inactive labels in (1205).  Likewise an exterior tag is already classified
by (1201).  Hence every full-SRP completion of the two-color cycle adds two
new inactive port-only labels beyond the strict five-cell permutation.

This is still a capacity charge, not a contradiction: the exact census
`N_01^k=10-k_k` in (787) can contain inactive labels.  The gain is that the
cycle branch now has two concrete outside witnesses at different selected
ports, which can be fed into the inactive-label telescopes of Sections
303--309 or compared against the simultaneous component profile of Section
324.  They are no longer anonymous fifth-cell layer choices.

## 354. The payer menu at each selected port is exact

The inactive witnesses in Section 353 belong to an already enumerated cut
sector, and that sector has a portwise rather than merely global census.
Fix an exterior component `k` and a selected port `q in Z`.  Its two
neighbors in `k` are distinct labels; call their set

```text
P_k(q):=N_k(q),             |P_k(q)|=2.             (1207)
```

Every `z in P_k(q)` has `j_z=1` by the pointwise port bound (785).  If it
meets `C`, then Section 352 identifies it with the unique strict export at
`q`; otherwise `i_z=0`, so it is literally an `N_01^k` port-only label.
Let `epsilon_k(q)` be one exactly when the strict export at `q` lies in
component `k`, and zero otherwise.  Then the two-element payer menu splits
exactly as

```text
#{z in P_k(q):(i_z,j_z)=(1,1)}=epsilon_k(q),
#{z in P_k(q):(i_z,j_z)=(0,1)}=2-epsilon_k(q).       (1208)
```

In particular the menu is `{strict, inactive}` when `k` receives the
strict export at `q`, and `{inactive, inactive}` otherwise.  Summing the
second identity over the five selected ports recovers, now label by label,

```text
sum_(q in Z)(2-epsilon_k(q))=10-k_k=N_01^k,         (1209)
```

because `sum_q epsilon_k(q)=k_k` is the number of strict exports received
by `k`.  Thus there are no additional kinds of selected-port payer hidden
inside the aggregate census (787).

This makes equal-tag saturation completely explicit.  If two repeated
propagation labels have common tag `(k,q)`, Section 350 says their distinct
intermediates exhaust `P_k(q)`.  Hence their payer profile is forced to be

```text
(strict,inactive) if epsilon_k(q)=1,
(inactive,inactive) if epsilon_k(q)=0.              (1210)
```

The same conclusion applies to either saturated endpoint-layer rectangle
of Section 351.  Unequal tags still occupy separate two-element menus, but
each menu carries the exact strict indicator (1208).  Consequently the
remaining cycle-completion problem may be stated entirely as reuse of the
finite `N_01` labels from (1209), rather than as an unspecified population
of core-inactive intermediates.

## 355. An inactive fifth-cell payer has a forced outside companion

A port-only payer cannot terminate its contribution at the selected port.
Fix an inactive `z in P_k(q)`.  The cross block `R_ke` has degree two at
`z`, while `j_z=1` says that exactly one of those two neighbors lies in
`Z`.  Hence there is a unique outside endpoint

```text
o(z) in e\Z,            N_e(z)={q,o(z)}.            (1211)
```

Now suppose `z=z(y)` pays the fifth cell of a propagation row `y in a`.
The same actual intermediate which witnesses `y--z--q` also witnesses the
companion cell

```text
y -- z -- o(z)                                           (1212)
```

in the same layer `Q_k^(a,e)=R_ak R_ke`.  Thus the forced fifth-cell tag
has an exact two-column support at its payer: one selected endpoint `q` and
one endpoint outside the selected target cycle.  Entrywise exactness of SRP
prevents this companion path from being cancelled or reassigned to another
layer.

The outside endpoint has one of the two concrete roles from the partition
of the target component:

```text
o(z) in O,  a residual endpoint; or
o(z) in B,  a private owner endpoint.                (1213)
```

In the second case `z` is not one of the three rooted letters of
`tau(o(z))`, because it is core-inactive; it is a genuinely new inactive
incidence at that private ticket rather than another step of the rooted
transition graph (1171).

Apply (1211) to the two labels forced in (1205).  There are actual paths

```text
y_4 -- z_4 -- p_4, o_4,
y_2 -- z_2 -- p_2, o_2,       o_4,o_2 in e\Z,       (1214)
```

where `y_4` and `y_2` denote whichever propagation labels use the chosen
inactive payers.  The outside endpoints need not be distinct, so no parity
claim is made here.  Nevertheless every full-SRP completion of the
two-color cycle now contains two literal companion cells outside `Z`, in
addition to the selected fifth cells.

This converts the `N_01` census cost into target geometry.  If a companion
lands in `O`, it is already a located residual terminal of the kind used by
the outside-destination chains in Sections 319--324.  If it lands in `B`,
the completion acquires an inactive incidence at a named private ticket,
which must coexist with that ticket's three rooted active letters and its
owner return.  The remaining price may therefore split on (1213), rather
than treating the inactive payer as an isolated cut label.
## 356. Each payer menu is a canonical blue owner pair

The two labels in `P_k(q)` are not merely a capacity set.  The pointwise
bound `j_z<=1` makes `Z` independent in the target owner factor `F_k[e]`.
Consequently the maximal `Z`-run containing `q` is the singleton `{q}`,
and its two boundary labels are exactly the two labels incident to `q`:

```text
P_k(q)={z,mu_Z(z)}.                                 (1215)
```

Thus `P_k(q)` is the canonical blue edge at `q` in the alternating graph
`P_k(C,Z)` of Section 241.  The strict indicator of Section 354 determines
the whole alternating component containing this edge.

If `epsilon_k(q)=1`, let `s_q` be the strict export at `q`.  Its other blue
endpoint is the canonical port-only mate `v_q` of Section 255, and the red
mate `u_q` of `s_q` is root-only.  Hence

```text
u_q --red-- s_q --blue-- v_q,
P_k(q)={s_q,v_q},                                   (1216)
```

the isolated `10--11--01` path (795).  If `epsilon_k(q)=0`, both vertices
of `P_k(q)` are port-only.  They have no red incidences, so their blue edge
is itself an isolated alternating component:

```text
P_k(q) is an isolated N_01--N_01 blue edge.         (1217)
```

Now take an equal-tag repeated transition at `(k,q)`.  Its two distinct
payers exhaust `P_k(q)` by Section 350.  Equations (1216)--(1217) therefore
upgrade the two capacity profiles in (1210) to an exact owner-run statement:

```text
epsilon_k(q)=1: the transition uses the strict export and its blue mate;
epsilon_k(q)=0: the transition uses both ends of one isolated blue edge.
                                                               (1218)
```

In particular there is no freedom to choose two unrelated inactive labels
when a repeated signature keeps one layer tag.  It consumes one complete
canonical target-run boundary component, and in the strict case it also
selects the root-only mate `u_q` through (1216).  Unequal layer tags remain
split between different blue pairs; the statement deliberately makes no
claim that those pairs lie in a common alternating component.

## 357. A private inactive companion restarts rooted propagation

The `B` branch of (1213) cannot absorb the inactive companion without
affecting its rooted ticket.  Let

```text
y -- z -- q,o,       z in k core-inactive,       o in B,          (1219)
```

and let `o^sib` and `p(o)` be the sibling and owner of `o`.  The vertex
`o` has cross degree two into component `k`, one incidence already being
the inactive label `z`.  Therefore among the three rooted labels of
`tau(o)`, at most one has color `k`:

```text
#{ell in tau(o):color(ell)=k}<=1.                  (1220)
```

In particular at least two rooted ticket labels have a color different
from `k`.  Choose one such label `ell`, and write its active target-factor
edge as

```text
{o,o'} indexed by ell.                             (1221)
```

The new endpoint cannot return to the preceding selected port:

```text
o'!=q.                                             (1222)
```

Otherwise `o,q` would have the two distinct common neighbors `z,ell`,
giving a four-cycle.  Nor can it hit the sibling `o^sib`, because
`o,o^sib` already share the owner `p(o)` and `ell` would be a second common
neighbor.  Thus

```text
o' notin {q,o^sib}.                                (1223)
```

The outgoing label changes color away from the inactive arrival layer
`k`.  If `o'` is selected, its rooted cell is a strict export; if it is
residual, propagation reaches `O`; and if it is private, it enters another
ticket without reversing to `q` or pairing the current siblings.  The
owner `p(o)` itself remains possible when it differs from `q`, in which
case (1221) is the sharply located strict-absorption alternative at that
owner.  When `q=p(o)`, (1222) excludes even that alternative and the new
edge must leave the whole owner fiber.

Consequently a fifth-cell companion landing in `B` is not a terminal
inactive decoration.  It supplies the exact restart

```text
inactive k-arrival at o
  -> a rooted label of color different from k
  -> O, a strict selected cell, or another B ticket,              (1224)
```

with both immediate payer reversal and sibling closure forbidden.  This
extends the cross-color propagation mechanism beyond the thirty active
arrival states of Section 346: inactive payer companions either terminate
in `O`, or re-enter the same strict/escape geometry through an actual
rooted ticket label.

## 358. A shared inactive companion consumes its arrival colors

Section 355 deliberately allowed the two inactive payers forced by the
four-state cycle to have the same outside endpoint.  That collision has an
exact cross-degree price.  Retain the labels at the two distinct selected
ports from (1205), and write

```text
N_e(z_4)={p_4,o_4},       z_4 in k_4,
N_e(z_2)={p_2,o_2},       z_2 in k_2.               (1225)
```

The labels `z_4,z_2` are distinct by Section 353.  Suppose their outside
companions coincide:

```text
o_4=o_2=:o.                                       (1226)
```

If the arrival layers also coincide, `k_4=k_2=:k`, then the two distinct
labels already exhaust the two `k`-neighbors of `o`.  Since both labels are
core-inactive, neither belongs to the rooted word at `o`, and no rooted
label of color `k` remains:

```text
#{ell in RootWord(o):color(ell)=k}=0.               (1227)
```

Here `RootWord(o)` means the three-letter ticket `tau(o)` when `o in B`
and the five rooted labels from (847) when `o in O`.  These are the only
two possibilities because `o` lies outside `Z`.

If instead `k_4!=k_2`, each inactive incidence consumes one of the two
slots in its own arrival layer.  Therefore

```text
#{ell in RootWord(o):color(ell)=k_4}<=1,
#{ell in RootWord(o):color(ell)=k_2}<=1.             (1228)
```

Thus coincidence of the outside companions never merges the two charges
for free.  Equal arrival colors delete that color entirely from the rooted
word; unequal colors impose two simultaneous multiplicity-one caps.  In
the private branch, (1227) strengthens the restart of Section 357 from
"at least two" to all three outgoing rooted labels changing away from
`k`.  In the residual branch it removes `k` from all five rooted cells.

If `o_4!=o_2`, the two located companion cells remain separate and no
cross-degree coupling between their rooted words is asserted.  Hence
(1226)--(1228) exactly price the only endpoint collision left open in
(1214), without assuming that the two fifth-cell layer tags agree.

## 359. A residual endpoint also restarts propagation

The apparent `O` terminal in Sections 346 and 357 has the same restart
mechanism, without an owner sibling.  Fix `s in O`.  For each of the five
roots `x in C`, the exact outside partition (835) gives one rooted active
label `ell_x(s)` for the cell `(x,s)`.  These five labels are distinct by
(779), and a fixed exterior color occurs among them at most twice because
`s` has cross degree two into that component:

```text
#{x in C:color(ell_x(s))=a}<=2.                    (1229)
```

First suppose an active label `ell_in` arrives at `s` from a preceding
endpoint `s_-`.  It is one of the five rooted labels.  Equation (1229)
ensures that some other rooted label `ell_out` has a different color.
Following its target-factor edge from `s` to `s_+`, one has

```text
s_+!=s_-.                                          (1230)
```

Indeed equality would make `s,s_-` share the two distinct common labels
`ell_in,ell_out`, producing a four-cycle.

Now suppose instead that `s=o(z)` is reached through a core-inactive payer
`z in k` as in (1211).  The inactive incidence already consumes one of the
two `k`-neighbors of `s`, so at most one rooted `ell_x(s)` has color `k`.
There are therefore at least four choices of a rooted label with color
different from `k`.  For any such choice, its far endpoint is not the
preceding selected port `q`, since `s,q` already share `z` and a return
would give them a second common neighbor.

Thus both arrival types have a common continuation rule:

```text
active or inactive arrival at s in O
  -> a rooted label of a different color
  -> an endpoint in O, B, or Z, without immediate reversal.       (1231)
```

An endpoint in `Z` is again a strict export because the outgoing label is
rooted in `C`; endpoints in `O` and `B` continue by this section and
Section 357.  Consequently residual arrival is not a terminal alternative
for the cross-color dynamics.  After adjoining the inactive companion
states, propagation can stop only at a strict selected cell; otherwise it
continues through the finite target component and eventually enters a
nonbacktracking cross-color state cycle.

The last sentence is a finite-state conclusion, not yet an exclusion: the
enlarged state space includes rooted arrivals at every vertex of `O` and
inactive arrivals supplied by fifth-cell payers.  Its value is to remove
the residual escape hatch from (1173).  Any full completion of the exact
reuse reversal must either hit one of the five strict selected cells or
support a genuine global colored holonomy cycle in the target component.
## 360. Every inactive companion opens an injective rooted fan

The restart in Section 357 can be applied simultaneously to every rooted
letter at the companion endpoint.  Let

```text
y -- z -- q,o,       z in k core-inactive,
o in B disjoint_union O,                            (1232)
```

and let `RootWord(o)` have its meaning from Section 358.  For each rooted
label `ell` in this word, denote the other endpoint of its target-factor
edge by `f_o(ell)`:

```text
N_e(ell)={o,f_o(ell)}.                              (1233)
```

Every fan endpoint avoids the preceding selected port:

```text
f_o(ell)!=q.                                        (1234)
```

Indeed `z` and `ell` are distinct--the former is core-inactive and the
latter meets a root in `C`.  If (1234) failed, they would be two common
neighbors of `o` and `q`, producing a four-cycle.

The endpoint map is injective.  If distinct rooted labels `ell,m` had
`f_o(ell)=f_o(m)`, then `ell,m` would be two common neighbors of `o` and
that far endpoint.  Therefore

```text
ell!=m implies f_o(ell)!=f_o(m).                    (1235)
```

When `o in B`, every far endpoint also avoids the sibling `o^sib`, because
`o,o^sib` already share the owner `p(o)`.  Thus a private companion opens
three distinct rooted edges whose far endpoints avoid `{q,o^sib}`.  A
residual companion opens five distinct rooted edges whose far endpoints
avoid `q`:

```text
o in B: |f_o(RootWord(o))|=3,
o in O: |f_o(RootWord(o))|=5.                       (1236)
```

The arrival label `z` already consumes one of the two `k`-neighbors of
`o`, so at most one fan edge has color `k`.  Consequently at least two of
the three private fan edges, or at least four of the five residual fan
edges, change color away from `k`.  A far endpoint in `Z` is a strict cell
because its indexing label is rooted; every other far endpoint lies in
`B` or `O`.

Hence an inactive fifth-cell companion is never a one-edge terminal.  It
forces an injective three- or five-way rooted fan with an explicit forbidden
back edge and a large color-changing subfan.  The remaining propagation
argument may now count distinct far endpoints, rather than choosing one
restart and losing the other rooted incidences.

## 361. The inactive payer row has an exact selected restart partition

The companion geometry can also be read from the simultaneous partition
whose source is the payer component itself.  Fix an inactive payer as in
(1211):

```text
z in k,       N_e(z)={q,o},       q in Z,       o in B disjoint_union O.
```

Apply `SRP(k,e)` to the row indexed by `z` and restrict its columns to
`Z`.  The routing layer through the original core color vanishes:

```text
supp((R_kc R_ce)[z,-]) intersect Z=emptyset.        (1237)
```

Indeed core-inactivity says that neither `c`-neighbor of `z` belongs to
`C`, while `(C,Z)` is a whole component of the cross factor `R_ce`; a
`c`-vertex outside `C` has no `e`-neighbor in `Z`.

The target endpoint layer is equally explicit.  The selected port `q` has
no `A_e`-neighbor in `Z` because `e_e(Z)=0`.  If `o in O`, it has no
`A_e`-neighbor in `Z` by the definition of the residual set.  If `o in B`,
its unique selected `A_e`-neighbor is its owner `p(o)`.  Consequently

```text
supp((R_ke A_e)[z,-]) intersect Z
 = emptyset                 if o in O,
 = {p(o)}                   if o in B.              (1238)
```

For every exterior component `h notin {k,e,c}`, put

```text
S_h(z):=supp((R_kh R_he)[z,-]) intersect Z,
S_k(z):=supp((A_k R_ke)[z,-]) intersect Z.          (1239)
```

All terms of the integer identity `SRP(k,e)` are nonnegative and sum
entrywise to `J`.  Equations (1237)--(1238) therefore give the exact
disjoint support partition

```text
o in O: Z = S_k(z) disjoint_union
              disjoint_union_(h notin {k,e,c}) S_h(z),

o in B: Z = {p(o)} disjoint_union S_k(z) disjoint_union
              disjoint_union_(h notin {k,e,c}) S_h(z).            (1240)
```

In particular the inactive payer row forces five selected cells in the
residual branch and four beyond the already located owner cell in the
private branch:

```text
sum_h |S_h(z)|=5 if o in O,       =4 if o in B,     (1241)
```

where the sum includes the self layer `h=k` as defined in (1239).  Each
occupied cell has a unique actual intermediate in its displayed product,
since its nonnegative entry is one.

Thus an inactive fifth-cell payer does more than open the rooted fan at its
outside endpoint.  Its own coupled SRP row simultaneously opens a complete
selected-column restart: either all five selected ports must be paid by
self/other exterior layers, or exactly the private owner port is paid by
the endpoint layer and the other four are paid elsewhere.  No contribution
can be hidden in the original core color or reassigned across layers.  This
is an exact support law, not yet a claim that the four or five payment
intermediates are globally new.

## 362. Every global propagation edge has one to three selected tags

The fifth-cell calculation of Section 349 extends uniformly from `B--B`
transitions to every rooted edge in the global propagation of Section 359.
Let `y in a` have core root `r in C` and two target endpoints

```text
N_e(y)={s,t} subset e\Z.                           (1242)
```

Assume the edge occurs in the nonbacktracking propagation, so if both
endpoints are private they are not siblings.  Let

```text
b(y):=|{s,t} intersect B| in {0,1,2}.              (1243)
```

In the selected columns of `SRP(a,e)`, the routing layer through `c`
occupies exactly the two ports incident to `r`, as in (1183).  The endpoint
layer through `e` contributes no selected port for an endpoint in `O`, and
contributes exactly its owner for an endpoint in `B`.  The private owners
are distinct when there are two, and each is nonincident to `r` because
`r` is a rooted letter of that private ticket.  Hence the two supports are
disjoint and have total size

```text
2+b(y).                                             (1244)
```

Exact integer SRP assigns every remaining selected cell to a unique layer
different from `c,e`.  Therefore the row `y` carries exactly

```text
3-b(y) selected payment tags beyond the c/e layers. (1245)
```

Equivalently, the transition types have the exact price

```text
B--B: one tag;
B--O: two tags;
O--O: three tags.                                  (1246)
```

Each tagged cell has a unique actual intermediate in its displayed product.
For payment layers outside the distinguished secondary component `d`, the
intermediates at different selected columns are distinct by the pointwise
bound (785).  No such distinctness is asserted in layer `d`: a `d`-label
may have two selected neighbors.  Thus (1246) counts exact tagged cells;
only outside `d` does it also count distinct payment vertices.

Section 349 is precisely the `B--B` line of (1246).  The other two lines
show that allowing the propagation cycle to enter the residual sector does
not loosen its coupled-SRP price; it doubles or triples the selected restart
data attached to that edge.  Consequently every nonstrict global holonomy
cycle from Section 359 comes decorated by at least one actual selected tag
per edge, with an additional tag for each residual endpoint.  The remaining
obstruction may now count tag reuse around the whole cycle rather than
treating only private-to-private transitions.

## 363. A residual companion has a nonstrict continuation

The five-way fan in the residual branch cannot terminate entirely at
strict selected cells.  Let `o in O` be the outside companion of an
inactive payer arriving from `q in Z`.  By (1234)--(1236), the set

```text
F(o):={f_o(ell):ell in RootWord(o)}                 (1247)
```

has five distinct elements and is disjoint from `{q}`.  But the selected
shore has only five ports, so

```text
|F(o) intersect Z|<=|Z\{q}|=4.                     (1248)
```

Consequently at least one rooted fan edge has its far endpoint outside the
selected shore:

```text
exists ell in RootWord(o),
  f_o(ell) in B disjoint_union O.                   (1249)
```

Thus a residual inactive companion cannot discharge all of its rooted
incidences through the five strict exports.  At least one branch continues
to another private or residual endpoint, even if the other four branches
hit every available selected port.

There is a useful color refinement in the collision case of Section 358.
If `o` is the common companion of two inactive payers in the same arrival
layer `k`, then (1227) removes color `k` from the entire five-letter rooted
word.  The continuation in (1249) may therefore be chosen from a fan all of
whose edges change color away from `k`:

```text
same-layer shared companion in O
  -> a nonstrict continuation of color different from k.        (1250)
```

This is a genuine nontermination statement rather than a capacity charge.
The continuation may still enter a finite colored holonomy cycle, but the
residual branch can no longer be declared finished merely because it has
reached `O` or because four strict exits are available.

## 364. The distinguished secondary layer has an exact double-payer form

The exception to payer distinctness in Section 362 is completely rigid.
Let `D(y)` be the set of the `3-b(y)` selected cells in (1245), and let
`D_d(y)` be the subset whose payment layer is the distinguished secondary
component `d`.  Every `d`-label `u` has even selected incidence because

```text
R_de 1_Z=0 over F_2,
```

while its total cross degree into `e` is two.  Therefore a `d`-intermediate
which pays any selected cell pays exactly two of them:

```text
u contributes to D_d(y)  implies  |N_e(u) intersect Z|=2.        (1251)
```

Both columns in (1251) must belong to `D(y)`.  If one were already occupied
by the `c`- or `e`-endpoint support from (1244), that entry of the
nonnegative integer SRP identity would be at least two.  Likewise the
two-port supports of distinct contributing `d`-intermediates are disjoint;
otherwise their common column would have product entry at least two.  Thus

```text
|D_d(y)|=2 times #{d-intermediates paying D(y)}.                  (1252)
```

Since `|D(y)|` is only one, two, or three, (1252) leaves exactly the
following payer profiles:

```text
B--B: one non-d singleton payer;

B--O: one d double-payer,
       or two distinct non-d singleton payers;

O--O: one d double-payer plus one non-d singleton payer,
       or three distinct non-d singleton payers.                  (1253)
```

Here a non-`d` payer is singleton on `Z` by (785), so different tagged
columns require different intermediates.  Conversely a `d` payer in
(1253) is one actual intermediate witnessing both of its two tagged cells;
there cannot be a mixture with only one `d`-tag.

Equation (1253) repairs the only reuse ambiguity in the global tag count.
In particular every `B--B` propagation edge has the single non-`d` literal
payer already used in Section 349, so its canonical fifth-cell tag satisfies
`kappa(y)!=d`.  A residual endpoint introduces either new
singleton payer vertices or one sharply identified secondary double-payer;
it never permits arbitrary merging of the two or three selected tags.  No
claim is made yet that double-payers on different propagation rows are
distinct.

## 365. Secondary double-payers have a unique geometric location

The complementary five-cycle normal form locates the exceptional profile
of Section 364 exactly.  Use the cyclic indexing (726), so the root `x_i`
is incident to the two selected ports

```text
{p_(i-1),p_i},                                      (1254)
```

and the distinguished `d`-edges on `Z` are
`{p_j,p_(j+2)}`.  Let a rooted propagation label `y` have core root `x_i`.
After removing its two forced core-layer columns, the three nonincident
selected ports are

```text
T_i={p_(i+1),p_(i+2),p_(i+3)}.                     (1255)
```

There is exactly one distinguished `d`-edge contained in this triple:

```text
{p_(i+1),p_(i+3)},                                 (1256)
```

and its complementary vertex in `T_i` is the offset port `p_(i+2)`.  This
is also the strict-export column paired with row `x_i` by (777), although
the payer of a propagation tag at that column need not itself be strict.

For an `O--O` propagation edge, `D(y)=T_i`.  Hence the double-payer branch
of (1253), if it occurs, is forced to use exactly (1256), and the remaining
non-`d` singleton tag is forced to lie at `p_(i+2)`:

```text
O--O with a d double-payer:
  d support={p_(i+1),p_(i+3)},
  non-d singleton column=p_(i+2).                  (1257)
```

For a `B--O` propagation edge, let `p_h` be the owner of its private
endpoint.  Since `x_i` is a ticket root there, `p_h` is one of the three
ports in `T_i`, and

```text
D(y)=T_i\{p_h}.                                     (1258)
```

The two-element set in (1258) is a distinguished `d`-edge exactly when

```text
p_h=p_(i+2).                                        (1259)
```

Therefore an actual `d` double-payer in the `B--O` line of (1253) forces
the private owner to be the offset port `p_(i+2)`.  If the owner is either
of the other two nonincident ports, both remaining tags must be paid by
distinct non-`d` singleton intermediates.  When the owner is the offset,
the geometry permits the unique double support (1256) but does not force
that profile instead of two singleton payers.

Thus secondary reuse is not only a parity alternative.  In the residual
row it selects one fixed diagonal of the nonincident triple, and in the
mixed row it is available only at one of the three possible private-owner
positions.  All other tagged columns retain literal payer distinctness.

## 366. The exceptional mixed owner creates a strict-offset five-cycle

The owner position singled out by (1259) has an ambient geometric meaning.
Let a `B--O` propagation label `y` have root `x_i`, private endpoint `w`,
residual endpoint `o`, and suppose

```text
p(w)=p_(i+2).                                       (1260)
```

Let `s_i` be the unique strict-export label in the rigid cell
`(x_i,p_(i+2))` from (777).  Then the five actual graph edges

```text
x_i--y,       y--w,       w--p_(i+2),
p_(i+2)--s_i,             s_i--x_i                (1261)
```

form the cycle

```text
x_i -- y -- w -- p_(i+2) -- s_i -- x_i.           (1262)
```

The vertices are distinct.  In particular `y!=s_i`: the propagation edge
of `y` has both endpoints outside `Z`, whereas the strict label `s_i` has
the selected endpoint `p_(i+2)`.  Thus every `B--O` secondary double-payer
allowed by Section 365 sits on a completely located strict-offset
five-cycle.  The same cycle is present whenever the mixed owner has the
offset position, even if its two tags choose non-`d` singleton payers.

There is also a forced endpoint disjointness.  The two labels `y,s_i`
already share the core neighbor `x_i`.  If their target neighborhoods met,
that common target would be a second common neighbor and create a four-cycle.
Hence

```text
N_e(y) intersect N_e(s_i)=emptyset.                (1263)
```

Write `N_e(s_i)={p_(i+2),v_i}`.  Since
`N_e(y)={w,o}`, (1263) gives

```text
v_i notin {w,o}.                                   (1264)
```

Thus the exceptional mixed geometry does not recycle either propagation
endpoint as the outside endpoint of the strict export.  It simultaneously
uses the private owner edge in (1262) and forces the strict label to a third
outside target role `v_i` distinct from both `w` and `o`.

This remains a located cost rather than a contradiction: five-cycles are
allowed.  But the only owner position at which a distinguished double-payer
can occur is now coupled to a named strict export and an endpoint-disjoint
outside mate.  A global holonomy completion must account for that strict
mate in addition to the double-payer support (1256), rather than treating
the offset owner as a purely columnwise coincidence.

## 367. Equal-root residual edges collide at the offset port

The offset singleton in Section 365 is present even when the secondary
double-payer is not used.  Let `y` be an `O--O` rooted propagation label
with core root `x_i`.  Its three residual tagged columns are `T_i`.  In the
double-payer profile, (1257) leaves `p_(i+2)` as the non-`d` singleton; in
the three-singleton profile of (1253), every column of `T_i` is non-`d`.
Thus in all cases there is a uniquely tagged actual path

```text
y -- z(y) -- p_(i+2),       z(y) in h(y),
h(y) notin {c,e,d}.                                    (1265)
```

Now take two distinct `O--O` propagation labels `y_0,y_1` with the same
core root `x_i`.  Their offset payers are distinct:

```text
z(y_0)!=z(y_1).                                      (1266)
```

Indeed the two source labels already have the common neighbor `x_i`.  If
their offset payer were also common, those two vertices would give a
four-cycle through `y_0,y_1`.

Consequently the layer tags have the sharp collision dichotomy

```text
h(y_0)=h(y_1)=h
  implies N_h(p_(i+2))={z(y_0),z(y_1)};

h(y_0)!=h(y_1)
  gives two separately located non-d payment obligations
  at the same offset port p_(i+2).                    (1267)
```

The first line uses the cross degree two of the selected port into `h`:
the distinct payers in (1266) exhaust that entire fiber.  Thus the repeated
signature collision of Section 350 has a residual analogue requiring only
a repeated root, not a repeated pair of private owners:

```text
two O--O edges rooted at x_i
  -> saturation or layer splitting at p_(i+2).       (1268)
```

This is again a capacity event rather than an exclusion.  Its gain is that
residual propagation cannot evade the selected-port collision mechanism by
changing both target endpoints: the core root alone fixes a canonical
non-secondary singleton column on every `O--O` row.  Further repetition of
one root may therefore be counted against the finite two-slot fibers at its
offset port.

## 368. Repeated residual roots force inactive offset companions

The canonical offset payer in (1265) has the strict/inactive dichotomy of
Section 352.  If `z(y)` meets `C`, then its selected incidence at
`p_(i+2)` is the unique strict cell in that column.  The rigid permutation
(777) identifies its root as `x_i`; hence

```text
z(y)=s_i, the strict-export label in (x_i,p_(i+2)).  (1269)
```

Otherwise `z(y)` is core-inactive.  Since it has exactly one selected
`e`-neighbor, it has a unique outside companion

```text
N_e(z(y))={p_(i+2),o(y)},       o(y) in B disjoint_union O,       (1270)
```

and Sections 357--363 apply to that located companion.  Thus every `O--O`
propagation row has the exact alternative

```text
its offset tag is paid by s_i, or it opens an inactive outside companion.
                                                               (1271)
```

This becomes a counting statement for repeated roots.  Let `Y_i` be any
set of distinct `O--O` propagation labels rooted at `x_i`.  Equation (1266)
applies pairwise, so their offset payers are all distinct.  But only the
single label `s_i` can be strict at `p_(i+2)`.  Therefore

```text
#{y in Y_i:z(y) is core-inactive}>=|Y_i|-1.          (1272)
```

In particular two residual edges with the same core root force at least
one literal inactive companion, independently of whether their layer tags
agree or split in (1267).  More generally every repetition beyond the first
pays another distinct inactive offset label.  The outside endpoints in
(1270) may still collide, but Section 358 then imposes the corresponding
arrival-color capacity, while distinct endpoints retain separate restart
fans.

Hence the exceptional secondary layer does not shield repeated residual
propagation.  It can absorb two of the three tagged columns, but the fixed
offset column still yields either the one already-accounted strict export
or a quantitatively growing family of inactive companions.

## 369. Six residual edges force a new inactive companion

The rootwise estimate (1272) has a global form independent of colors and
payment layers.  Let `Y` be any finite set of distinct `O--O` rooted
propagation labels and partition it by core root:

```text
Y=disjoint_union_(i in Z/5) Y_i.                   (1273)
```

For a fixed `i`, all offset payers of `Y_i` are distinct by Section 367,
and at most the one strict label `s_i` is core-active.  Payers belonging to
different nonempty root classes are also distinct: their selected offset
ports `p_(i+2)` differ, while every non-`d` offset payer has only one
selected neighbor by (785).  Therefore the inactive payer sets from the
five classes are disjoint and

```text
#{distinct core-inactive offset payers forced by Y}
 >= sum_i max(|Y_i|-1,0)
 = |Y|-#{i:Y_i nonempty}
 >= |Y|-5.                                         (1274)
```

Equivalently, among all distinct residual-to-residual propagation labels,
at most five can pay their canonical offset tags through strict exports:

```text
|Y|>=6 implies Y forces at least one inactive payer
and hence an outside companion in B disjoint_union O.            (1275)
```

More generally every label beyond the first five increases the lower bound
in (1274) by one.  This conclusion does not require two labels to have the
same source color, the same secondary-payer profile, or the same layer tag;
only the five available core roots can shelter one strict offset payment
each.

For a global holonomy cycle, apply (1274) to the set of its distinct
`O--O` indexing labels.  If that set has size at least six, the cycle cannot
close solely through the already-accounted strict exports and secondary
double-payers: it opens an inactive companion, whose injective fan and
nonstrict continuation are governed by Sections 360--363.  If it has size
at most five, the residual-residual part of the cycle is now uniformly
bounded.  Thus the cycle branch splits into a constant-size residual core
or a quantitatively forced inactive expansion.

## 370. Every root has an odd residual boundary after its strict mate

There is a rootwise parity law on the global propagation graph.  Fix a
core root `x_i`, and consider the target-factor edges indexed by labels
which meet `x_i`.  For `X,Y in {O,B,Z}`, let `E_i(X,Y)` denote the number
of such edges with one endpoint in `X` and the other in `Y`.

Every residual endpoint `s in O` is incident to exactly one edge in this
rooted family.  Indeed the exact outside partition (835) assigns the cell
`(x_i,s)` to one unique exterior intermediate, which is the rooted label
from (847).  Counting rooted-edge incidences on `O` therefore gives the
integer identity

```text
|O|=2 E_i(O,O)+E_i(O,B)+E_i(O,Z).                  (1276)
```

The last term is completely located.  A label meeting both `x_i` and a
selected port is a strict export, and (777) supplies exactly the label
`s_i` at the offset port `p_(i+2)`.  Write

```text
N_e(s_i)={p_(i+2),v_i},       v_i in B disjoint_union O.
```

It follows that

```text
E_i(O,Z)=1 if v_i in O,       E_i(O,Z)=0 if v_i in B.             (1277)
```

Since `|O|=2q-15` by (846), the left side of (1276) is odd.  Reducing
(1276) modulo two and using (1277) yields

```text
E_i(O,B)+1_[v_i in O]=1                         (mod 2).          (1278)
```

Equivalently the rootwise residual boundary has the exact dichotomy

```text
v_i in B  implies E_i(O,B) is odd, hence nonzero;
v_i in O  implies E_i(O,B) is even.                 (1279)
```

Thus whenever the strict outside mate lies in a private ticket, the same
root necessarily supports an odd family of additional `O--B` propagation
edges.  Each such edge carries the two selected tags of the mixed line in
(1246), with the distinguished-double geometry controlled by Sections
365--366.  If the strict mate lies in `O`, it accounts for the odd boundary
itself and the remaining `O--B` edges pair evenly.

This is an exact per-root statement, not merely a global handshake.  It
does not yet bound the number of `O--O` edges, which disappear twice in
(1273), but it prevents all five residual rooted families from closing
inside `O` independently of the locations of their strict mates.

## 371. Arbitrary companion collisions obey an exact color-capacity law

The two-payer collision of Section 358 extends without loss to any family
of inactive companions.  Fix an outside endpoint

```text
o in B disjoint_union O,
```

and let `I(o)` be a set of distinct core-inactive payer labels whose unique
outside companion is `o`.  For each exterior component `k`, define

```text
n_k(o):=#{z in I(o):z in k},
t_k(o):=#{ell in RootWord(o):color(ell)=k}.          (1280)
```

Every label counted by either term is a distinct `k`-neighbor of `o`: the
first family is core-inactive, while the rooted-word family meets `C`.
Since the `k--e` cross block has degree two at `o`, one has the pointwise
capacity law

```text
0<=n_k(o)<=2,       n_k(o)+t_k(o)<=2.               (1281)
```

Thus two inactive arrivals in one color delete that color from the rooted
word, while one inactive arrival leaves room for at most one rooted letter
of that color.  Section 358 is exactly the two-arrival specialization of
(1281), but no assumption on the total collision multiplicity or on equal
arrival layers is needed here.

Let

```text
K(o):={k:n_k(o)>0}.
```

Summing `n_k(o)<=2` over its support gives

```text
|K(o)|>=ceil(|I(o)|/2).                             (1282)
```

Equivalently, a collision of `m` inactive companions at one outside
endpoint must occupy at least `ceil(m/2)` distinct arrival colors.  The
same data impose the rooted-word deficit

```text
sum_(k in K(o)) (2-t_k(o)) >= |I(o)|.               (1283)
```

Hence outside-endpoint reuse cannot erase the global inactive-payer count
of Section 369.  It converts that count into color diversity and explicit
missing capacity in the three-letter `B` ticket or five-letter `O` word.
Distinct companions retain separate restart fans; coincident companions
obey (1281)--(1283).  This is a local capacity law, not yet a global lower
bound on the number of different outside endpoints.

## 372. A strict selected hit reflects to an outside rooted restart

The selected alternative in the propagation rules is not a genuine terminal
once the other endpoint of its strict label is retained.  Let `s_i` be the
strict export in `(x_i,p_(i+2))`.  Its selected incidence count is one and
its total cross degree into `e` is two, so

```text
N_e(s_i)={p_(i+2),v_i},       v_i in e\Z=B disjoint_union O.      (1284)
```

At `v_i`, the label `s_i` is an actual rooted active arrival from `x_i`.
If `v_i in B`, it is one of the three labels of `tau(v_i)`; if `v_i in O`,
it is one of the five rooted residual labels.  In the private case ticket
nonmonochromaticity supplies a rooted label `ell` of color different from
`color(s_i)`; in the residual case the multiplicity cap (1229) does the
same.  Let `v'` be its other target endpoint.

The restart cannot return to the selected port:

```text
v'!=p_(i+2).                                        (1285)
```

Otherwise `v_i,p_(i+2)` would have the two distinct common neighbors
`s_i,ell`, producing a four-cycle.  If `v_i in B`, the same owner argument
as in Section 357 also forbids the sibling ticket.

Thus a propagation step which reaches the strict cell through `s_i` may be
continued at the canonical outside mate: reflect along the already known
strict incidence to the arrival state `(v_i,s_i)`, then leave through a
different-color rooted label `ell`.  The reflected strict edge itself is
not counted as a new color transition; the transition at `v_i` is, and
(1285) prevents an immediate second hit of the same selected port.  In
symbols,

```text
strict hit at p_(i+2) through s_i
  -> rooted arrival (v_i,s_i)
  -> different-color edge to B, O, or another strict Z cell.     (1286)
```

Combine (1286) with the `B` and `O` restart rules of Sections 357 and 359.
Every rooted arrival state now has a successor: outside endpoints choose a
different-color rooted edge, and selected endpoints reflect through their
unique strict label to its outside mate.  Since the target component and
its rooted incidence set are finite, every infinite choice sequence repeats
a rooted arrival state and contains a directed colored state cycle:

```text
the exact-reuse reversal forces a global reflected holonomy cycle.       (1287)
```

This strengthens (1173): there is no terminal branch after strict
reflection.  It does not yet assert a simple cycle in the underlying target
factor, because a selected reflection traverses one strict incidence back
to its outside mate.  The cycle is in the exact rooted-arrival dynamics,
with every genuine departure changing color and every nonselected immediate
reversal excluded.  This is the global finite object which a final coupled
SRP/component argument must rule out.

## 373. Inactive companions have a global endpoint-capacity bound

The local collision law of Section 371 can be summed over all exterior
colors.  There are `r=q/2` component colors in total and `r-2` components
outside the fixed pair `{c,e}`.  For an outside endpoint `o`, summing
(1281) over those colors gives

```text
|I(o)|+|RootWord(o)|<=2(r-2).                       (1288)
```

The rooted word has size three on a private ticket and size five on a
residual endpoint.  Using `q=2r`, (1288) becomes the role-sensitive bound

```text
o in B implies |I(o)|<=q-7;
o in O implies |I(o)|<=q-9.                         (1289)
```

Thus even collisions spread over many arrival colors cannot place
arbitrarily many inactive payers at one target endpoint.  Let `I` be any
finite set of distinct inactive payer labels, let `Comp(I)` be the set of
their outside companions, and split it into `Comp_B(I),Comp_O(I)`.  Summing
(1289) over the companion fibers yields

```text
|I| <= (q-7)|Comp_B(I)|+(q-9)|Comp_O(I)|.           (1290)
```

Apply this to the inactive offset payers forced by a family `Y` of distinct
`O--O` propagation labels in Section 369.  Since that section supplies at
least `max(|Y|-5,0)` distinct inactive payers, their companion endpoints
satisfy

```text
(q-7)|Comp_B|+(q-9)|Comp_O| >= max(|Y|-5,0),

|Comp_B|+|Comp_O|
  >= ceil(max(|Y|-5,0)/(q-7)).                      (1291)
```

If all companions lie in `O`, the sharper denominator `q-9` applies.
Equations (1290)--(1291) are global noncollapse bounds: the many inactive
labels forced by repeated residual roots cannot all merge into fewer
outside endpoints than the available cross-color slots permit.

This estimate is quantitative rather than terminal; its denominator grows
with `q`.  Its role is to preserve actual target support when passing from
the distinct inactive labels of Section 369 to the reflected holonomy of
Section 372.  Any stronger contradiction must exploit the rooted deficits
in (1283), the injective fans at those companion endpoints, or overlap
between their restarted edges, not merely the number of labels.

## 374. Reflected holonomy is stationary strict or contains a tagged move

The state cycle forced in Section 372 has an exact physical dichotomy.
Represent a rooted arrival state as `(v,ell_in)` with `v in B disjoint_union
O`.  A departure label `ell_out` has color different from `ell_in`.  If its
far endpoint is selected, strict reflection returns to a state
`(v,ell_out)` at the same physical vertex; otherwise it reaches a new
physical vertex in `B disjoint_union O`.

Choose a directed state cycle with no repeated state except at closure.
Either every transition is a strict reflection, or at least one transition
is a genuine outside-to-outside move.  In the first case all physical
vertices on the cycle are one vertex `v`, and every arrival label on the
cycle is a distinct strict export whose outside mate is `v`:

```text
stationary branch:
  (v,s_(i_0))->(v,s_(i_1))->...->(v,s_(i_(L-1)))
  ->(v,s_(i_0)).                                    (1292)
```

Adjacent strict-label colors in (1292) differ, including at closure.  The
far selected endpoints are pairwise distinct by the injective fan theorem
(1235), so the strict labels and their roots are pairwise distinct as well.
There is no one-state cycle because every departure changes label color.
Consequently

```text
v in B implies 2<=L<=3,
v in O implies 2<=L<=5.                             (1293)
```

Thus the stationary possibility is a constant-size cyclic word of strict
exports sharing one outside mate, not an arbitrary global recurrence.

In the second case the cycle contains a rooted label `y` with

```text
N_e(y)={s,t} subset B disjoint_union O.             (1294)
```

This is precisely a global propagation edge of Section 362.  According to
its endpoint roles it carries the exact one-, two-, or three-cell selected
tag profile (1246), with secondary reuse classified by Sections 364--365.
Hence the reflected cycle dichotomy is

```text
a stationary strict word of length at most five at one outside vertex;
or a moving cycle containing at least one fully tagged B/O edge. (1295)
```

The distinction is dynamical: every physical move directly exposes a row
of Section 362, while a stationary word must be charged through the strict
labels themselves.  Section 375 supplies that separate charge.  No claim
is made here that the moving cycle is simple or that its physical edges are
distinct.

## 375. Every strict-reflection label has two or three selected tags

Strict reflection does not remove the coupled-SRP cost of its indexing
label.  Let `s_i in k` be the strict label with

```text
N_c(s_i) intersect C={x_i},
N_e(s_i)={p_(i+2),v_i},       v_i in B disjoint_union O.          (1296)
```

Apply `SRP(k,e)` to row `s_i` and restrict to `Z`.  The core layer occupies
the two ports incident to `x_i`:

```text
supp((R_kc R_ce)[s_i,-]) intersect Z={p_(i-1),p_i}. (1297)
```

For the endpoint layer, the selected neighbor `p_(i+2)` contributes no
selected `A_e` endpoint because `Z` is independent.  The outside mate
contributes none when `v_i in O`, and contributes exactly its owner when
`v_i in B`.  Hence

```text
supp((R_ke A_e)[s_i,-]) intersect Z
 =emptyset             if v_i in O,
 ={p(v_i)}             if v_i in B.                (1298)
```

In the private case `x_i` is a rooted ticket occurrence at `v_i`, so its
owner is nonincident to `x_i`; the supports (1297)--(1298) are disjoint.
Exact SRP therefore leaves

```text
v_i in O: three selected tag cells;
v_i in B: two selected tag cells.                  (1299)
```

Their columns are exactly the same nonincident sets analyzed before:
`T_i` in the residual-mate case and `T_i\{p(v_i)}` in the private-mate
case.  Consequently the payer profiles of Sections 364--365 apply verbatim:

```text
strict mate in O:
  one d double-payer plus the offset non-d singleton,
  or three non-d singleton payers;

strict mate in B:
  a d double-payer is possible only when p(v_i)=p_(i+2),
  otherwise the two tags have distinct non-d singleton payers.  (1300)
```

Thus every label in the stationary strict word (1292) carries a literal
two- or three-cell selected tag profile.  The stationary branch is bounded
in length but not unpriced: a word of length `L` contributes `L` such
coupled rows, each with its forced secondary/singleton geometry.  The moving
and stationary branches of Section 374 are therefore both exposed to the
same tag-reuse and inactive-payer mechanisms, through propagation rows in
one case and strict rows in the other.

## 376. Reflected holonomy has a finite rooted cyclic-word normal form

The state-cycle formulation can be converted into one concrete cyclic word
without mistaking strict reflection for an ordinary target edge.  Put

```text
U:=B disjoint_union O.
```

Form a rooted multigraph `H_ref` on `U`.  A rooted label `ell` whose two
target endpoints lie in `U` contributes its ordinary target-factor edge.
A strict label `s_i`, with target endpoints `{p_(i+2),v_i}`, contributes
instead one loop at its outside mate `v_i`.  The loop records the excursion
from `v_i` to the selected leaf and its forced reflection back; it is not an
edge or loop of the original graph.

A transition from state `(v,ell_in)` chooses a different-color rooted label
`ell_out` at `v`.  In `H_ref`, it then traverses the edge indexed by
`ell_out`: an ordinary edge reaches its other outside endpoint, while a loop
returns to `v`.  Therefore, after cyclically indexing each chosen departure,
a shortest directed state cycle from Section 372 gives a cyclic word

```text
v_0 --[ell_0]-- v_1 --[ell_1]-- ...
    --[ell_(L-1)]-- v_0.                            (1301)
```

where the edge indexed by `ell_j` joins `v_j` to `v_(j+1)` in `H_ref`
(indices modulo `L`).  The corresponding arrival state is
`(v_(j+1),ell_j)`.  At every transition vertex, the arriving label
`ell_(j-1)` and departing label `ell_j` have different component colors.
They also have different core roots: the rooted word at a private or
residual endpoint contains at most one label for each root.  Thus
consecutive letters of the cyclic word change both color and root.

Choose the state cycle with no repeated state before closure.  The total
number of rooted arrival states on `U` is exactly

```text
3|B|+5|O|=30+5(2q-15)=10q-45.                      (1302)
```

Consequently

```text
2<=L<=10q-45.                                      (1303)
```

The stationary branch of Section 374 is precisely the case in which every
letter of (1301) is a strict loop at one vertex.  The moving branch contains
at least one ordinary rooted edge, and each such letter carries the selected
tag profile of Sections 362--365.  Ordinary edges or underlying vertices
may repeat later in the word, but the directed arrival states do not.

Hence the remaining terminal is now an explicitly bounded cyclic word on
rooted labels, with adjacent root/color changes, strict reflections marked
as formal loops, and every physical move decorated by its exact SRP tag row.
This is a normal form rather than an exclusion; its purpose is to give the
cycle-wide tag identity a precise indexing object.

## 377. A strict row's offset tag cannot pay through its own strict label

The offset column in a strict row has a stronger version of the
strict/inactive dichotomy.  Suppose first that `v_i in O`.  By (1300), the
column `p_(i+2)` has a unique non-`d` singleton payer; call it `z_i`.  If
`z_i` met `C`, Section 352 would identify it with the unique strict export
at that column, namely the source label itself:

```text
z_i=s_i.                                            (1304)
```

But a payment by `s_i in k` in row `s_i` would belong to the self layer
`A_k R_ke` and require the diagonal entry `A_k(s_i,s_i)=1`.  The self
factor has no loops.  Hence (1304) is impossible and

```text
z_i is core-inactive.                               (1305)
```

The same proof applies when `v_i in B` provided its owner is not the offset
port.  In that case `p_(i+2)` remains one of the two non-`d` singleton tag
columns in (1300), and its only possible core-active payer is again the
source `s_i`.  The sole exception is

```text
v_i in B and p(v_i)=p_(i+2),                        (1306)
```

when the endpoint layer already occupies the offset column and there is no
offset tag to price.

Thus every strict-reflection row has a forced inactive offset payer except
possibly the owner-equals-offset private row.  These forced payers have
unique outside companions by Section 355.  They are distinct for different
roots: their selected offset ports differ and every non-`d` payer has
selected incidence one.

Apply this to a stationary word (1292) of length `L`.  If its common outside
mate `v` lies in `O`, all `L` rows satisfy (1305).  If `v in B`, its owner is
fixed, and the bijection `x_i mapsto p_(i+2)` shows that at most one of the
distinct roots in the word can satisfy (1306).  Therefore

```text
stationary word at v in O forces L distinct inactive payers;
stationary word at v in B forces at least L-1 distinct inactive payers.
                                                               (1307)
```

Since `L>=2`, even the smallest stationary reflected cycle opens at least one
inactive outside companion.  Thus stationary holonomy is not a closed
strict-export phenomenon: it
necessarily feeds the companion collision and restart machinery of Sections
355--373.  This does not yet rule out the enlarged recurrence, but removes
the last branch whose selected tags might all have been paid by already
accounted strict labels.

## 378. A stationary word's inactive companions leave its center

The inactive offset payers forced in Section 377 cannot return their
outside endpoints to the stationary vertex.  Let `s_i` be one strict label
in a stationary word centered at `v`, and let `z_i` be its forced inactive
offset payer.  Write

```text
N_e(s_i)={p_(i+2),v},
N_e(z_i)={p_(i+2),o_i}.                             (1308)
```

Then

```text
o_i!=v.                                             (1309)
```

Indeed equality would make the selected port `p_(i+2)` and the outside
vertex `v` have the two distinct common neighbors `s_i,z_i`, producing a
four-cycle.  Thus every inactive payer counted in (1307) opens a companion
away from the physical center of the reflected word.

Different payers may still share one new companion, but such collisions
obey the exact arrival-color capacity law (1281)--(1283).  In particular
the companion set is nonempty, and the global endpoint bound of Section 373
applies to it.  Quantitatively,

```text
v in O: L inactive payers have companions in (B union O)\{v};
v in B: at least L-1 inactive payers do so.         (1310)
```

Since `L>=2`, the stationary branch always creates at least one genuinely
new outside vertex carrying an inactive arrival and the injective rooted
fan of Section 360.  Therefore a stationary strict word is stationary only
inside the reflected state cycle itself; its mandatory coupled-SRP
completion immediately leaves the center.  The full holonomy obstruction
may consequently be sought in the moving, companion-expanded geometry even
when the minimal reflected cycle has no ordinary target edge.

## 379. Private-owner terms cancel from the cycle-wide tag parity

The cyclic word (1301) has a selected-column invariant which is independent
of all private endpoints on its ordinary edges.  For `v in U`, define the
owner vector over `F_2^Z`

```text
beta(v):=[p(v)] if v in B,       beta(v):=0 if v in O.            (1311)
```

For the letter `ell_j` rooted at `x_(i_j)`, let `D_j subset Z` be its
selected tag support outside the forced `c/e` layers.  If `ell_j` is an
ordinary edge from `v_j` to `v_(j+1)`, Sections 362 and 365 give

```text
[D_j]=[T_(i_j)]+beta(v_j)+beta(v_(j+1))       in F_2^Z.           (1312)
```

Indeed `T_(i_j)` is the three-port nonincident set, and each private
endpoint removes its distinct owner column.  If `ell_j=s_(i_j)` is a strict
loop, Section 375 instead gives

```text
[D_j]=[T_(i_j)]+beta(v_j),                          (1313)
```

because the selected endpoint contributes no owner column and the unique
outside mate is `v_j=v_(j+1)`.

Now sum around the cyclic word.  After deleting its formal strict loops,
the ordinary letters form a closed walk on `U`; hence every physical vertex
has even ordinary-edge incidence.  All owner vectors in (1312) cancel.
Only the one-copy correction from each strict loop remains, giving the exact
cycle identity

```text
sum_(j mod L) [D_j]
 =sum_(j mod L) [T_(i_j)]
  +sum_(j:ell_j strict and v_j in B) [p(v_j)]       in F_2^Z.     (1314)
```

Thus ordinary motion through private tickets contributes no endpoint noise
to the total tag parity.  In a moving word with no strict letters, the tag
sum is determined solely by the root word.  In a stationary strict word at
`v`, the correction is zero for `v in O` and is `L[p(v)]` for `v in B`.
Mixed reflected cycles have exactly the displayed private strict-mate
correction and no others.

Equation (1314) is a conservation law rather than a vanishing assertion:
the left side need not yet be zero.  Its value is that any cycle-wide reuse
or cancellation theorem for the actual payment tags can now be compared
against a five-dimensional root expression with one explicitly located
strict-owner correction, instead of against the full sequence of private
and residual endpoints.

## 380. Each root induces an odd involution with five fixed points

The reflected normal form has a common-domain permutation model.  Put

```text
U:=B disjoint_union O,       |U|=10+(2q-15)=2q-5.   (1315)
```

Fix a root `x_i`.  Every residual vertex in `O` has exactly one
`x_i`-rooted active label.  Among the private tickets, exactly the four
vertices

```text
B_(x_i)=T_(i-1) disjoint_union T_i                 (1316)
```

belong to the endpoint layer and have no exterior rooted letter at `x_i`;
the other six have exactly one.  The rooted target-factor edges pair all
active vertices in `U`, except that the unique strict label joins its
outside mate `v_i` to the selected port `p_(i+2)`.

Define `sigma_i:U->U` by pairing the two outside endpoints of each ordinary
`x_i`-rooted label, fixing `v_i` to encode strict reflection, and fixing
the four inactive vertices of `B_(x_i)`.  The factor edges are disjoint, so
this is an involution.  Its fixed set is exactly

```text
Fix(sigma_i)=B_(x_i) disjoint_union {v_i},
|Fix(sigma_i)|=5.                                  (1317)
```

The union is disjoint: `v_i` carries the rooted strict label at `x_i`, so
if it is private it cannot lie in the endpoint-layer set `B_(x_i)`.
Consequently `sigma_i` has

```text
(|U|-5)/2=q-5                                      (1318)
```

transpositions.  Since the binary parameter `q` is even,

```text
sign(sigma_i)=(-1)^(q-5)=-1.                       (1319)
```

Thus the five core roots produce five odd involutions on the same odd set
`U`, each with five explicitly located fixed points.

The cyclic word (1301) is an admissible word in these involutions.  If the
letter `ell_j` has root `x_(r_j)`, then

```text
v_(j+1)=sigma_(r_j)(v_j).                          (1320)
```

An ordinary label is a transposition step and a strict reflection is the
fixed point `v_(r_j)`.  The four artificial fixed points in `B_(x_(r_j))`
are never chosen as steps, because those tickets have no rooted letter at
that root.  Consecutive indices `r_j` differ: the rooted word at a target
vertex has only one letter per core root, while consecutive transition
labels are distinct (indeed have different colors).

This recasts the remaining obstruction as a colored reduced cyclic word in
five common-domain odd involutions, with the forbidden fixed points and all
SRP tag decorations retained.  It is not yet a sign contradiction--an odd
permutation may have fixed points--but it is the precise bridge from the
ticket propagation audit to the Baer-involution/coupling formulation of the
q-generic A-REG-NONBIP lane.

## 381. The five nonincident triples form a root-parity basis

The root term in the cycle identity (1314) retains all five root parities,
not only their total augmentation.  Recall

```text
T_i={p_(i+1),p_(i+2),p_(i+3)} subset Z.             (1321)
```

The five incidence vectors `[T_i]` are linearly independent over `F_2`.
Indeed suppose

```text
sum_(i mod 5) a_i[T_i]=0.                           (1322)
```

Reading coordinate `p_j` gives

```text
a_(j-1)+a_(j-2)+a_(j-3)=0.                         (1323)
```

Adding the equations for `j` and `j+1` yields `a_j=a_(j-3)`.  Since three
generates the cyclic group of order five, all five coefficients are equal.
Substitution into (1323) then gives `a_i=0` for every `i`.  Thus

```text
([T_0],...,[T_4]) is a basis of F_2^Z.              (1324)
```

For the reflected word, let

```text
a_i:=#{j:i_j=i} mod 2
```

be the parity with which root `x_i` occurs, and define the corrected tag
vector

```text
W:=sum_(j mod L)[D_j]
   +sum_(j:ell_j strict and v_j in B)[p(v_j)].       (1325)
```

Equation (1314) and the basis property give

```text
W=sum_(i mod 5) a_i[T_i],                           (1326)
```

so `W` uniquely determines the full root-parity vector
`(a_0,...,a_4)`.  In particular

```text
W=0 implies every root occurs evenly and L is even. (1327)
```

More generally any proposed cycle-wide cancellation law for the actual tag
payments translates, through the explicit strict-owner correction in
(1325), into five separate root constraints.  A scalar tag count would see
only `L mod 2`; the basis (1324) prevents cancellation between different
root triples and is the exact linear interface needed by the common-domain
involutions of Section 380.

## 382. Pair products fix exactly the common root-fixed vertices

The five involutions of Section 380 have an exact pairwise fixed-set law.
Write

```text
F_i:=Fix(sigma_i)=B_(x_i) disjoint_union {v_i}.      (1328)
```

For distinct roots `i!=j` and any `u in U`, involutivity gives

```text
(sigma_j sigma_i)(u)=u  iff  sigma_i(u)=sigma_j(u). (1329)
```

Suppose the common image in (1329) were `w!=u`.  Then both maps use
ordinary rooted labels: one meeting `x_i`, the other meeting `x_j`.  The
labels are distinct by the one-root bound (779), and they would be two
common neighbors of `u,w`, producing a four-cycle.  Therefore equality of
the two images is possible only at `w=u`, when both involutions fix `u`.
Conversely a common fixed point plainly fixes the product.  Hence

```text
Fix(sigma_j sigma_i)=F_i intersect F_j.             (1330)
```

The endpoint-layer part of this intersection is already explicit.  The
four vertices `B_(x_i)` are the two private tickets over each of the two
selected ports incident to `x_i`.  Two adjacent core roots share one such
port, while two nonadjacent roots share none.  Thus

```text
|B_(x_i) intersect B_(x_j)|
 =2 if x_i,x_j are adjacent on C,
 =0 otherwise.                                     (1331)
```

Combining (1328)--(1331), the full pair-product fixed set is

```text
(B_(x_i) intersect B_(x_j))
 union ({v_i} intersect F_j)
 union ({v_j} intersect B_(x_i)).                  (1332)
```

The last two terms are the only strict-mate corrections; they include the
possibility `v_i=v_j`.  In particular an adjacent root pair always gives
at least the two common private fixed points, while a nonadjacent pair has
no fixed point unless one of these explicitly located strict corrections
occurs.

This is stronger than knowing that every `sigma_i` is odd.  It determines
the fixed points of every reduced two-letter word and shows that no
additional coincidence of moving images can occur.  Longer-word analysis
may therefore start from a completely controlled pair geometry rather than
from arbitrary products of five involutions.

## 383. Only common strict mates support admissible two-letter cycles

The fixed points in (1332) separate into algebraic and dynamically
admissible roles.  For distinct roots `i,j`, put

```text
alpha_(i,j):=1_[v_i in B_(x_j)],
delta_(i,j):=1_[v_i=v_j].                           (1333)
```

The four pieces in (1332) are disjoint.  For example `v_i` does not belong
to `B_(x_i)`, and if `v_i=v_j` then that common strict mate belongs to
neither endpoint-layer block.  Hence (1331)--(1332) give the exact count

```text
|Fix(sigma_j sigma_i)|
 =2*1_[x_i,x_j adjacent on C]
  +alpha_(i,j)+alpha_(j,i)+delta_(i,j).             (1334)
```

Most of these product fixed points cannot occur as states of the rooted
holonomy.  A vertex in `B_(x_i) intersect B_(x_j)` is artificial for both
roots: neither rooted letter exists there.  A correction counted by
`alpha_(i,j)` is the strict mate for root `i` but is artificial for root
`j`, and symmetrically for `alpha_(j,i)`.  The only fixed point carrying
actual rooted strict letters for both roots is therefore a common strict
mate

```text
v_i=v_j.                                             (1335)
```

Let `col(s_i)` denote the exterior component of the strict label.  A
stationary two-letter state cycle alternates the departures `s_i,s_j` at
one outside vertex.  The transition rule requires their colors to differ.
Conversely, if (1335) holds and the colors differ, both strict departures
are available at the common mate and each reflects back there, producing
the literal state cycle.  Thus

```text
an admissible stationary 2-cycle on roots i,j exists
 iff v_i=v_j and col(s_i)!=col(s_j).                 (1336)
```

This distinguishes fixed points of the permutation product from legal
rooted-arrival recurrence.  The two base fixed points for adjacent roots,
and all one-sided strict corrections, contribute to the group action but
can never by themselves realize the shortest stationary holonomy.  Any
two-letter obstruction is concentrated at equality of two explicitly
located strict outside mates together with their color separation.

## 384. Every two-root product has five unpaired orbit components

The fixed-set law has an exact orbit-level refinement.  Fix distinct roots
`i,j`, put

```text
c_ij:=|F_i intersect F_j|,
pi_ij:=sigma_j sigma_i,
```

and form the two-colored graph `Gamma_ij` on `U` whose `i`-edges are the
transpositions of `sigma_i` and whose `j`-edges are the transpositions of
`sigma_j`.  A vertex outside `F_i union F_j` has one edge of each color, a
vertex in the symmetric difference has degree one, and a common fixed
vertex is isolated.  Moreover an `i`-edge and a `j`-edge can never coincide:
such a shared transposition would give equal moving images, excluded by
(1330).  Hence every nontrivial component is either an alternating path or
an alternating even cycle.

There are `5-c_ij` vertices of each of the two types
`F_i setminus F_j` and `F_j setminus F_i`.  These are precisely the degree-one
vertices of `Gamma_ij`, so the component census is

```text
c_ij isolated common fixed vertices;
5-c_ij alternating path components;
h_ij alternating cycle components                 (1337)
```

for some `h_ij>=0`.  This statement does not require a path to join opposite
fixed-set types: paths with two endpoints of the same type may occur, but
the total endpoint balance pairs them globally.

The action of `pi_ij` on these components is standard but useful here.  On
an alternating path, successively applying the `i`- and `j`-matchings walks
through all path vertices and closes them into one permutation cycle.  On
an alternating cycle of length `2m`, it advances by two edges and therefore
splits the component into two permutation cycles of the same length `m`.
Each isolated vertex is a fixed point.  Consequently

```text
#Orbits(pi_ij on U)
 =c_ij+(5-c_ij)+2h_ij
 =5+2h_ij.                                         (1338)
```

In particular every two-root product has an odd number of permutation
orbits, with exactly five unpaired component-orbits; every remaining orbit
occurs with an equal-length partner coming from the other parity class of
one alternating cycle.  The vertex count also gives the coarse capacity

```text
2q-5>=c_ij+2(5-c_ij)+4h_ij,
h_ij<=floor((2q-15+c_ij)/4).                       (1339)
```

Equations (1337)--(1339) upgrade the pairwise trace data `|Fix(pi_ij)|` to
an exact cycle-type normal form.  They still do not force a contradiction:
the five path/fixed orbits may have arbitrary lengths.  Their value is that
any longer holonomy or character argument may treat all closed alternating
components in paired blocks and isolate a bounded set of exactly five
unpaired two-root orbits.

## 385. Stationary holonomy is a common-mate color-cycle test

The same admissibility distinction classifies every stationary word, not
only length two.  For an outside vertex `v in U`, define

```text
S(v):={i:v_i=v},       gamma_i:=col(s_i).            (1340)
```

A stationary state cycle at `v` uses distinct strict labels by Section 374.
Hence its root indices are distinct elements of `S(v)`.  Conversely every
chosen strict label with index in `S(v)` reflects from its selected port
back to `v`, so the only transition condition between consecutive chosen
indices is change of component color.  Therefore

```text
stationary words at v
 <-> cyclic orderings of distinct indices in S(v)
     whose adjacent gamma-colors differ.            (1341)
```

Fix a subset `R subset S(v)` of size `L>=2`, and let `m_a(R)` be the number
of its strict labels in exterior component `a`.  Such a cyclic ordering
exists exactly when

```text
max_a m_a(R)<=floor(L/2).                           (1342)
```

Necessity follows because occurrences of a most frequent color require at
least as many separating positions of other colors around the circle.  For
`L<=5`, which is the only range allowed by (1293), sufficiency is the
following exhaustive list of multiplicity partitions:

```text
L=2: 1+1;
L=3: 1+1+1;
L=4: 2+2, 2+1+1, or 1+1+1+1;
L=5: 2+2+1, 2+1+1+1, or 1+1+1+1+1.                (1343)
```

Each displayed partition has an immediate cyclic ordering with the repeated
colors separated, while every omitted partition violates (1342).

Thus the stationary branch is completely finite.  Length two is precisely
the common-mate/different-color criterion (1336); length three requires
three pairwise different strict colors; and lengths four or five permit no
color more than twice.  All roots in the word share the one explicit
outside mate `v`, and Sections 377--378 then force their inactive companions
away from that center.  No group-product fixed point which is artificial
for one of the roots enters this classification.

## 386. Live alternating components classify all two-root holonomy

The component decomposition of Section 384 also has an exact dynamic
admissibility test.  For a root `i` and vertex `u in U`, define an actual
root action whenever `u` is not one of the four artificial fixed points:

```text
L_i(u):=the ordinary x_i-rooted label at u, if sigma_i(u)!=u;
        s_i,                                  if u=v_i.
                                                        (1344)
```

Thus `L_i(u)` is undefined exactly on `B_(x_i)`.  Write `kappa_i(u)` for
its exterior component color.  For distinct roots `i,j`, call a component
`K` of `Gamma_ij` **live** when

```text
L_i(u),L_j(u) are both defined and
kappa_i(u)!=kappa_j(u) for every u in K.             (1345)
```

This condition has a concrete form on each component type.  On an
alternating cycle both actions are ordinary everywhere, so only the color
inequalities remain.  At an endpoint `u in F_i setminus F_j` of an
alternating path, the missing `i`-action is defined exactly when `u=v_i`;
otherwise it is an artificial fixed point in `B_(x_i)`.  The symmetric
statement holds at an endpoint in `F_j setminus F_i`.  At an isolate, both
actions are defined exactly when `u=v_i=v_j`, recovering the common-mate
condition of Section 383.  In particular a path whose two endpoints lie in
the same fixed-set difference is never live: both distinct endpoints would
have to equal the one strict mate of the same root.  Every live path
therefore joins the two opposite fixed-set differences, with endpoints
`v_i` and `v_j`.

Now consider a rooted state cycle whose root alphabet is exactly `{i,j}`.
Consecutive roots must differ, so its departures alternate between the two
actions.  Every ordinary departure traverses the corresponding colored edge
of `Gamma_ij`, while every strict departure uses the formal reflection at a
path endpoint or isolate.  The transition rule is precisely the color
inequality in (1345).  It follows that

```text
there is a holonomy cycle using exactly roots i,j
 <-> Gamma_ij has a live component.                 (1346)
```

For completeness, the construction in the reverse direction is explicit.
A live alternating cycle of length `2m` is traversed once and gives a word
of length `2m`.  A live path with `n` ordinary edges is traversed to one
end, reflected through its strict action, traversed back, and reflected at
the other end, giving a word of length

```text
2(n+1).                                             (1347)
```

A live isolate gives the stationary two-letter word of (1336).  In each
case successive arrivals determine the next, opposite-root departure, so
the construction closes without introducing any third root.  Conversely a
two-root state cycle cannot jump between components, cannot pass an
artificial endpoint, and cannot cross a vertex where the two action colors
agree; its supporting component is therefore live.

Hence exclusion of the entire two-root branch is equivalent to the finite
local obstruction

```text
every component of every Gamma_ij contains either
an artificial path/isolate endpoint or a same-color transition vertex.
                                                        (1348)
```

This criterion includes stationary and moving cycles uniformly.  It does
not assert that (1348) always holds; rather, it identifies the exact extra
component-color datum that must be coupled to the five-unpaired-orbit law
before a three-or-more-root terminal can be invoked.

## 387. Same-side path orbits occur in balanced even pairs

The path caveat in Section 384 has an exact parity form.  Fix distinct
roots `i,j`, abbreviate `c:=c_ij`, and classify the `5-c` alternating paths
of `Gamma_ij` by their endpoint types.  Let

```text
a   := number with one endpoint in each of
       F_i setminus F_j and F_j setminus F_i;
b_i := number with both endpoints in F_i setminus F_j;
b_j := number with both endpoints in F_j setminus F_i.
```

Each fixed-set difference contains exactly `5-c` path endpoints.  Counting
the two endpoint types separately gives

```text
a+2b_i=5-c=a+2b_j.
```

Consequently `b_i=b_j=:b` and

```text
a=5-c-2b.                                           (1349)
```

This balance also determines the parity of the associated product orbits.
Along an alternating path, endpoints of opposite fixed-set types have
incident edges of opposite colors, so the path has an even number of edges
and an odd number of vertices.  Endpoints of the same type have incident
edges of the same color, so the path has an odd number of edges and an even
number of vertices.  By (1338), all vertices of one path form one orbit of
`pi_ij`.  The `c` common-fixed isolates are singleton orbits.  Hence among
the five unpaired path/isolate orbits of `pi_ij` there are exactly

```text
c+a=5-2b odd-cardinality orbits;
b_i+b_j=2b even-cardinality orbits.                 (1350)
```

In particular the even unpaired orbits occur in a balanced pair: one
same-side path of each endpoint type.  The alternating-cycle contribution
remains a collection of equal-length pairs as in Section 384, irrespective
of whether those paired orbit lengths are odd or even.  Thus (1350) makes
no false cross-type matching assertion; it isolates precisely the balanced
same-side obstruction that prevents the five distinguished product orbits
from all having odd cardinality.

## 388. No stationary holonomy forces three distinct strict mates

The stationary classification has a useful endpoint-spread contrapositive.
For `v in U` and an exterior component color `a`, put

```text
r_a(v):=|{i in S(v):gamma_i=a}|.
```

Every strict label counted here is one of the rooted labels at `v`.  If
`v in B`, the private ticket bound (844) applies; if `v in O`, the residual
rooted-word bound (1229) applies.  In both cases

```text
r_a(v)<=2 for every v in U and every color a.       (1351)
```

By (1341), two roots in one strict-mate fiber with different colors already
give the stationary two-letter word.  Conversely, if `S(v)` is
monochromatic, no cyclic ordering of two or more of its roots can change
color at every transition.  Thus

```text
there is no stationary holonomy cycle
 iff every nonempty S(v) is monochromatic.          (1352)
```

Combining (1351)--(1352), absence of stationary holonomy forces

```text
|S(v)|<=2 for every v in U.                         (1353)
```

The five root indices occur in exactly one strict-mate fiber each, so their
nonzero fiber sizes form a partition of five.  Under (1353) the only
possibilities are

```text
2+2+1,       2+1+1+1,       or 1+1+1+1+1.          (1354)
```

In particular the five strict mates occupy at least three distinct outside
vertices.  Equivalently, the reflected dynamics has the sharp dichotomy:
either two roots already close a stationary color-changing cycle at a
common mate, or the strict exports spread over at least three outside
endpoints with every repeated endpoint carrying one monochromatic pair.
This conclusion is uniform in the binary parameter and uses no order-64
enumeration.  It turns the stationary branch into a literal finite spread
condition that can be combined with the inactive-companion bounds of
Sections 369 and 373; the remaining holonomy problem is then moving.

## 389. The five ordinary root matchings have linear cycle rank

The pair decompositions sit inside one dense global graph.  Let `M` be the
simple graph on `U` obtained by taking, for all five roots, every ordinary
transposition edge of `sigma_i` and omitting its fixed points.  Each root
contributes `q-5` edges by (1318).  Edges from distinct roots cannot
coincide: a common edge `{u,w}` would give
`sigma_i(u)=w=sigma_j(u)` with `w!=u`, contrary to (1330).  Therefore

```text
|V(M)|=2q-5,             |E(M)|=5(q-5).             (1355)
```

Put `m(u):=|{i:u in F_i}|`.  Root `i` contributes an incident ordinary edge
at `u` exactly when it does not fix `u`, so

```text
deg_M(u)=5-m(u),
sum_(u in U)m(u)=sum_i|F_i|=25.                     (1356)
```

The degree identity is consistent with (1355): summing it gives
`2|E(M)|=5(2q-5)-25=10q-50`.  If `kappa(M)` is the number of connected
components, the binary cycle-space dimension is consequently

```text
dim Z_1(M;F_2)
 =|E(M)|-|V(M)|+kappa(M)
 =3q-20+kappa(M)
 >=3q-19.                                          (1357)
```

This graph carries two independent labels on every edge: its core root
`i`, and the exterior component containing the actual rooted label whose
two target endpoints form that edge.  The latter is a genuine edge color,
not a half-edge color: the two endpoints are paired by the same label, so
its exterior component is identical at both ends.

At any vertex of an `M`-cycle, the two incident cycle edges automatically
have different roots, since each root class is a matching.  The cycle is a
literal ordinary reflected-holonomy cycle exactly when their exterior
component colors also differ at every vertex, including at closure.  Thus

```text
properly exterior-colored cycles of M
 <-> holonomy cycles having only ordinary moves.    (1358)
```

In particular, if the reflected dynamics has no all-ordinary moving cycle,
then every nonzero member of a cycle space of dimension at least `3q-19`
contains a same-component transition at some vertex.  This is a global
obstruction
ledger rather than a counting contradiction: one bad transition may meet
many cycles.  Its purpose is to replace ten separate pair graphs by one
linear-size cycle space to which a properly-colored-cycle or forbidden-
transition theorem can be applied.  Strict reflections remain outside `M`
and must be reattached through Sections 385 and 388.

## 390. Every matching-union component has an exact fixed-mass rank

The global cycle rank localizes to every cut.  For `A subset U`, let
`e_M(A)` be the number of `M`-edges with both endpoints in `A`, let
`partial_M(A)` be the number with exactly one endpoint in `A`, and put

```text
mu(A):=sum_(u in A)m(u).
```

For one root matching, each vertex of `A` is either fixed, lies on an
internal matching edge, or lies on a cut edge.  Counting vertices in these
three roles and then summing over the five roots gives

```text
5|A|=mu(A)+2e_M(A)+partial_M(A).                    (1359)
```

In particular

```text
partial_M(A)=5|A|-mu(A)-2e_M(A),
partial_M(A)=|A|-mu(A) mod 2.                       (1360)
```

If `K` is a connected component of `M`, its cut is empty.  Writing
`rho(K):=e_M(K)-|K|+1` for its cycle rank, (1359) becomes the exact local
identity

```text
rho(K)=(3|K|-mu(K)+2)/2,
mu(K)=3|K|+2-2rho(K).                               (1361)
```

Summing (1361) over the components recovers (1357), but (1361) retains
where the twenty-five fixed incidences occur.  It also interfaces directly
with the stationary alternative.  At a residual vertex `u in O`, fixed-set
membership is precisely strict-mate membership, so `m(u)=|S(u)|`.  At a
private vertex `u in B`, exactly the two roots incident to its owner port
count `u` artificially in their endpoint blocks; the remaining fixed-set
memberships are its strict mates.  Hence

```text
u in O: m(u)=|S(u)|;
u in B: m(u)=2+|S(u)|.                              (1362)
```

If there is no stationary holonomy, (1353), (1356), and (1362) imply

```text
u in O: deg_M(u)>=3;
u in B: deg_M(u)>=1,
and deg_M(u)=1 only if |S(u)|=2.                    (1363)
```

Thus `M` has no isolated vertex in the no-stationary branch.  Every leaf is
a private endpoint carrying a monochromatic strict-mate pair, and every
tree component has at least two such leaves.  Since `|B|=10`, there are at
most five tree components.  This does not yet force a properly colored
cycle, but it sharply localizes any low-degree terminal of a cycle-
elimination argument: it cannot lie in the residual set, and at a leaf it
must spend one of the finitely many repeated strict-mate fibers from
Section 388.

## 391. Yeo elimination forces an ordinary moving cycle for `q>=16`

The global ledger has a sharp properly-colored-cycle terminal.  We use the
following theorem of Anders Yeo, *A Note on Alternating Cycles in
Edge-Coloured Graphs*, J. Combin. Theory Ser. B 69 (1997), 222--225,
doi:10.1006/jctb.1997.1728:

```text
if an edge-colored graph H has no properly colored cycle,
then some vertex z has the property that every component of H-z
is joined to z by edges of at most one color.         (1364)
```

The hypothesis applies literally to the exterior-component coloring of
`M` from Section 389.  Moreover the rooted color cap (1351) says that at
every vertex of `M`, at most two incident edges have any prescribed color.
This cap is inherited by every subgraph.

We now induct on the order of a connected subgraph `H subset M` having no
properly colored cycle.  The one-vertex case is immediate.  Choose `z` by
(1364), and let `C_1,...,C_t` be the components of `H-z`.  Induction gives
`e(C_s)<=2(|C_s|-1)`.  All edges from `z` to a fixed `C_s` have one color,
so the color cap gives at most two such edges.  Therefore

```text
|E(H)|
 <=sum_s (2(|C_s|-1)+2)
 =2(|V(H)|-1).                                     (1365)
```

Applying (1365) separately to the `kappa(M)` components yields the uniform
extremal bound

```text
M has no properly colored cycle
 implies |E(M)|<=2(|V(M)|-kappa(M))
                 <=4q-12.                         (1366)
```

But the exact matching count (1355) is `|E(M)|=5q-25`.  Combining it with
(1366) would give `q<=13`.  Hence

```text
q>=14 implies M has a properly exterior-colored cycle;
in the binary range, q>=16 forces an all-ordinary moving holonomy.
                                                        (1367)
```

This removes every strict-reflection and stationary complication from the
large binary branch: by (1358), the forced cycle is already a literal
rooted holonomy made entirely of ordinary `B/O` moves, and every one of its
edges carries the exact coupled SRP tag profile of Sections 362--365.  The
remaining small binary value is outside this inequality and must retain its
separate finite treatment.  No order-specific enumeration enters (1367).

## 392. Ordinary holonomy has linear transversal mass

The existence theorem is robust under deletions.  First sharpen the Yeo
bound by one.  Let `H subset M` be connected, PC-cycle-free, and have
`n>=2` vertices.  Choose the Yeo vertex `z` from (1364), and let
`C_1,...,C_t` be the components of `H-z`.  Inductively, a component of
order at least two has at most `2|C_s|-3` edges.  A singleton has no
internal edge.  Since the edges from `z` to a fixed component have one
color, the monochromatic degree cap gives at most two such edges; for a
singleton, simplicity improves this to at most one.  Thus every component,
together with its edges to `z`, contributes at most `2|C_s|-1`, and

```text
|E(H)|<=sum_s(2|C_s|-1)
       =2(n-1)-t<=2n-3.                            (1368)
```

Applying (1368) to the nontrivial components of an arbitrary PC-cycle-free
subgraph (isolated vertices contribute no edges) gives, on `n>=2` vertices,

```text
|E(H)|<=2n-3.                                       (1369)
```

Let `X subset E(M)` meet every properly colored cycle.  Then `M-X` is
PC-cycle-free, so (1355) and (1369) give

```text
|X| >= |E(M)|-(2|U|-3)
     = (5q-25)-(4q-13)
     = q-12.                                        (1370)
```

There is a fixed-mass version for vertex transversals.  Suppose
`S subset U` meets every properly colored cycle and `|U setminus S|>=2`.
Deleting `S` removes at most `sum_(u in S)deg_M(u)` edges.  Applying (1369)
to `M-S`, then using (1356), yields

```text
5q-25-sum_(u in S)(5-m(u))
 <=2(2q-5-|S|)-3,

sum_(u in S)(3-m(u)) >= q-12.                      (1371)
```

If fewer than two vertices remain, the resulting cardinality bound below
is automatic.  Since every summand in (1371) is at most three, every vertex
transversal satisfies

```text
|S|>=ceil((q-12)/3).                               (1372)
```

The private set gives a stronger role-specific consequence.  Every
`u in B` is artificially fixed by two roots, so `m(u)>=2` and

```text
sum_(u in B)(3-m(u))<=|B|=10.                       (1373)
```

For `q>22`, equations (1371)--(1373) show that `B` cannot meet every
properly colored cycle.  Therefore

```text
q>=23 implies M[O] contains a properly colored cycle;
in the binary range q>=32, there is a simple all-O ordinary holonomy.
                                                        (1374)
```

Every edge of the cycle in (1374) is an `O--O` propagation row.  It
therefore carries three selected tags, with the canonical non-`d` offset
singleton of Sections 364, 365, and 367, and the cycle has no private-owner
or strict-loop correction in (1314).  Equations (1370)--(1374) do not yet
cancel those tags; they supply the linear support and the residual-only
normal form that the remaining payer-reuse argument must exploit.

## 393. A simple ordinary cycle has an exact tag-mass identity

The simplicity supplied by the properly colored cycle theorem makes the
rowwise tag price additive without vertex multiplicities.  Let `Q` be a
simple properly exterior-colored cycle of `M`, let

```text
L:=|E(Q)|=|V(Q)|,       b_Q:=|V(Q) intersect B|,
```

and for an edge `y of Q` retain the endpoint count `b(y)` from (1243) and
the selected tag set `D(y)` from (1245).  Every private vertex of `Q` is an
endpoint of exactly its two incident cycle edges, while residual vertices
contribute zero.  Therefore

```text
sum_(y in E(Q)) b(y)=2b_Q.                          (1375)
```

Using the exact row price `|D(y)|=3-b(y)` from (1245) gives the cycle-wide
integer identity

```text
sum_(y in E(Q)) |D(y)|=3L-2b_Q.                    (1376)
```

Thus every simple ordinary holonomy carries an odd number of selected tag
cells exactly when its length is odd, independently of how it passes
through the ten private vertices.  More importantly, (1376) is an exact
cell count: it does not identify two cells merely because their payer label
or payment layer later agrees.

There is also an exact vector specialization.  If `r(y)` is the core root
of edge `y` and

```text
a_i(Q):=#{y in E(Q):r(y)=i} mod 2,
```

then the cycle has neither a strict-loop term nor an uncancelled private
owner term in (1314).  Consequently

```text
sum_(y in E(Q))[D(y)]
 =sum_i a_i(Q)[T_i]              in F_2^Z.          (1377)
```

Since the five `[T_i]` form the basis (1324), the parity with which every
root occurs on `Q` is recoverable from the five selected-column parities.
In particular

```text
sum_(y in E(Q))[D(y)]=0
 implies every root occurs evenly and L is even.    (1378)
```

For the residual-only cycle forced by (1374), `b_Q=0`, so (1376) becomes

```text
sum_(y in E(Q))|D(y)|=3L.                          (1379)
```

Hence every binary `q>=32` admits a simple all-`O` ordinary holonomy with
three literal selected tag cells on every edge and with its complete root-
frequency parity encoded by (1377).  This sharpens the qualitative tag
decoration after (1367), but it is still not a cancellation theorem: the
next step must use the offset-payer distinctness and shelter bound of
Sections 367--369 to convert these cells into new geometry.

## 394. Large residual holonomy can avoid every strict shelter

The residual-only cycle can be chosen so that every canonical offset tag
opens new geometry.  Call an `O--O` edge `y` rooted at `x_i` **sheltered**
when its offset payer from (1265) is the strict export `s_i`, rather than a
core-inactive label.  Offset payers of distinct `O--O` edges with the same
root are distinct by (1266), so at most one edge per root is sheltered.
Thus the global sheltered set `S_sh` satisfies

```text
|S_sh|<=5.                                          (1380)
```

Delete the ten private vertices and then the edges in `S_sh`.  The first
operation removes at most

```text
sum_(u in B)deg_M(u)=50-mu(B)<=30                  (1381)
```

edges, because every private vertex has the two artificial fixed
memberships in (1362), so `mu(B)>=20`.  Double-counting an edge internal to
`B` only makes (1381) a safer upper bound.  Therefore the residual graph

```text
G_sh:=M[O]-S_sh
```

has

```text
|V(G_sh)|=2q-15,
|E(G_sh)|>=5q-25-30-5=5q-60.                      (1382)
```

If `G_sh` had no properly colored cycle, the sharpened Yeo bound (1369)
would give

```text
5q-60<=2(2q-15)-3=4q-33,
```

and hence `q<=27`.  Consequently

```text
q>=28 implies G_sh has a simple properly colored cycle;
in the binary range this holds for every q>=32.     (1383)
```

Let `Q` be the cycle in (1383), of length `L`.  Every one of its edges is
`O--O` and unsheltered.  By (1271), its canonical offset payer is therefore
core-inactive.  The distinctness argument of (1274) applies without the
usual one-per-root loss: same-root payers are distinct by (1266), and
different-root payers occupy different selected offset ports while having
selected incidence one.  Hence

```text
Q forces exactly L distinct core-inactive offset payers.        (1384)
```

Each payer in (1384) has its unique outside companion in `B union O`.
If `Comp_B(Q),Comp_O(Q)` denote the distinct companion endpoints by role,
the global collision capacity (1290) specializes to

```text
L<=(q-7)|Comp_B(Q)|+(q-9)|Comp_O(Q)|.              (1385)
```

Thus the `q>=32` large binary branch no longer merely has an all-residual
three-tag cycle.  It has one whose every edge contributes a different
literal inactive payer and whose companion collisions retain the exact
capacity price (1385).  The only unresolved merging is now at those named
outside companions; none of the cycle's offset obligations can be absorbed
by the five already-accounted strict exports.

## 395. Unsheltered residual holonomy has linear transversal mass

The cycle in Section 394 is not an isolated consequence of one density
comparison.  Every edge of `G_sh` has a core-inactive canonical offset
payer.  Moreover the distinctness proof used for (1384) applies to the
entire edge set: equal-root payers are distinct by (1266), while
different-root payers meet different selected offset ports and each has
selected incidence one.  Hence the payer map is injective and (1382) gives

```text
z:E(G_sh) -> {core-inactive labels} is injective,
|z(E(G_sh))|>=5q-60.                               (1386)
```

Now let `X subset E(G_sh)` meet every properly colored cycle of `G_sh`.
The graph `G_sh-X` is PC-cycle-free, so the sharpened Yeo bound (1369)
and (1382) imply

```text
5q-60-|X|<=2(2q-15)-3=4q-33,
|X|>=q-27.                                         (1387)
```

There is again a weighted vertex version.  If `S subset O` meets every
properly colored cycle and at least two vertices remain, deletion removes
at most

```text
sum_(u in S)deg_M(u)=sum_(u in S)(5-m(u))
```

edges of `G_sh`.  Comparing the remaining lower bound with (1369) gives

```text
sum_(u in S)(3-m(u))>=q-27,
|S|>=ceil((q-27)/3).                               (1388)
```

If fewer than two vertices remain, the cardinality conclusion is
automatic.  Thus no bounded set of residual endpoints accounts for all
unsheltered cycles as `q` grows.

The injection (1386) transfers (1387) directly to the payer side.  If a
set `P` of inactive labels meets the offset-payer set of every properly
colored cycle of `G_sh`, its inverse edge set is a cycle transversal.
Therefore

```text
|P|>=q-27.                                         (1389)
```

Finally apply the companion capacity (1290) to all labels in (1386), not
only to one chosen cycle.  Writing `Comp_B(G_sh),Comp_O(G_sh)` for their
distinct outside companions gives

```text
5q-60
 <=(q-7)|Comp_B(G_sh)|+(q-9)|Comp_O(G_sh)|.        (1390)
```

Equations (1386)--(1390) turn the large-binary residual branch into a
linear family of named inactive obligations: at least `5q-60` different
payer labels exist globally, and at least `q-27` payer labels or ordinary
edges are needed to hit all of their properly colored cycles.  This is
still a support theorem rather than the final contradiction; the next
step must couple the nearly saturated offset-port layers or the companion
fans across different cycles.

## 396. The offset-payer map misses at most five labels per port

The inactive payer population in (1386) has an exact ambient size.  There
are `r-3` exterior components outside `{c,e,d}`.  For each such component
`a` and selected port `p`, the cross degree gives exactly two `a`-labels
meeting `p`, and (785) says that each meets no other selected port.  Hence
the non-`d` selected-singleton population at one port has size

```text
2(r-3)=q-6.                                         (1391)
```

The strict-support permutation (777) places exactly one of the five strict
exports at each selected port.  Section 352 says that every other label in
(1391) is core-inactive.  Equivalently, summing the exact census
`N_01^a=10-k_a` from (787)--(788), the core-inactive pool is

```text
q-7 labels at each selected port;
5(q-7)=5q-35 labels over all five ports.            (1392)
```

The unsheltered offset map nearly exhausts this pool root by root.  Fix
`x_i`.  Its ordinary matching has `q-5` edges.  Exactly four private
vertices are artificial fixed points for this root, so only the other six
vertices of `B` can lie on its ordinary edges.  Deleting all edges meeting
`B` therefore removes at most six root-`i` edges.  Deleting the possible
single sheltered edge removes at most one more.  If `E_i(G_sh)` is the
remaining root-`i` edge set, then

```text
|E_i(G_sh)|>=(q-5)-6-1=q-12.                       (1393)
```

Every edge in `E_i(G_sh)` maps injectively to a core-inactive payer at the
one offset port `p_(i+2)`.  Comparing (1393) with the exact `q-7` labels
available there proves

```text
0 <= (q-7)-|z(E_i(G_sh))| <= 5.                    (1394)
```

Thus at every selected port, not merely in aggregate, all but at most five
core-inactive selected labels occur as canonical offset payers of
unsheltered residual edges.  Summing (1394) recovers the global constant
slack

```text
|(core-inactive selected pool) setminus z(E(G_sh))|<=25.
```

This is substantially tighter than a linear lower bound alone: any final
companion or layer argument may discard only five exceptional inactive
labels per port before it must account for the entire residual matching
family.  The constant `25` is independent of `q`, while the covered pool
has size `5q-35`.

## 397. Several roots saturate one common payer layer

The five-label slack in Section 396 forces a cross-root layer collision.
Fix `x_i`, and for an allowed payer layer `h notin {c,e,d}` put

```text
n_i(h):=#{y in E_i(G_sh):h(y)=h}.
```

Let `gamma_i` be the exterior color of the strict export `s_i`.  At the
offset port `p_(i+2)`, the inactive-label capacity of layer `h` is

```text
c_i(h):=2-1_[h=gamma_i].
```

Thus `sum_h c_i(h)=q-7`, exactly (1392), and Section 396 gives

```text
0<=n_i(h)<=c_i(h),
Delta_i:=sum_h(c_i(h)-n_i(h))<=5.                 (1395)
```

There are `r-4` layers other than `gamma_i`, each with inactive capacity
two.  Every such layer which is not filled by two offset payers costs at
least one unit of `Delta_i`.  Hence root `i` saturates at least

```text
(r-4)-5=r-9                                      (1396)
```

two-slot layers.  Average (1396) over the five roots.  Some allowed layer
`h` is saturated at at least

```text
t(q):=ceil(5(r-9)/(r-3))                           (1397)
```

different roots.  In the binary ranges this gives the staircase

```text
q>=32  -> t(q)>=3;
q>=64  -> t(q)>=4;
q>=128 -> t(q)=5.                                  (1398)
```

For each of these `t(q)` roots, the two payer labels in layer `h` exhaust
the entire `h`-fiber of its selected offset port.  The two labels have
different outside companions: otherwise that companion and the selected
port would have the same two common payer neighbors, a four-cycle.  Across
different roots a companion may be reused, but its cross degree into `h`
is two, so at most two of the `2t(q)` payer labels can meet it.  Hence the
common saturated layer supplies

```text
2t(q) distinct inactive payer labels in h,
at least t(q) distinct outside companions.          (1399)
```

Whenever two labels collide at one companion, they exhaust its two
`h`-neighbors; because both payers are core-inactive, that companion then
has no rooted active label of color `h`, exactly the deletion phenomenon
of (1227).

Thus the residual unsheltered graph is not merely large in aggregate.
Every root misses at most five inactive offset-payer slots, forcing a common layer
which simultaneously saturates three, four, or all five selected offset
ports as the binary parameter grows.  This is the first cross-root layer
coupling extracted from the ordinary-cycle expansion; the remaining task
is to feed the companion deletions in (1399) back into the rooted matching
or SRP tag system.

## 398. The unused payer slack is exactly private-boundary loss

The five-slot bound in (1394) has an exact geometric formula.  Fix root
`x_i`, and write

```text
h_i:=# root-i ordinary edges meeting B,
s_i^sh:=# sheltered root-i O--O edges in {0,1},
epsilon_i:=1_[v_i in B].
```

Among the ten private tickets, four are the artificial fixed block
`B_(x_i)`.  The other six carry actual root-`i` labels, except that the
strict mate `v_i`, when private, is fixed rather than ordinary.  Therefore
the ordinary root-`i` incidence count on `B` is

```text
2E_i(B,B)+E_i(O,B)=6-epsilon_i.                    (1400)
```

Since `h_i=E_i(B,B)+E_i(O,B)`, this also gives

```text
h_i=(6-epsilon_i+E_i(O,B))/2.                      (1401)
```

The residual boundary parity (1278) says that `E_i(O,B)` is even when
`v_i in O` and odd when `v_i in B`.  Together with (1400), its possible
values and the corresponding private-edge losses are

```text
v_i in O: E_i(O,B) in {0,2,4,6},  h_i in {3,4,5,6};
v_i in B: E_i(O,B) in {1,3,5},    h_i in {3,4,5}.  (1402)
```

Now let `delta_i` be the number of core-inactive labels at `p_(i+2)` not
hit by the unsheltered offset-payer map.  The root matching has `q-5`
ordinary edges, partitioned exactly into the `h_i` edges meeting `B`, the
`s_i^sh` sheltered `O--O` edges, and the unsheltered edges of `G_sh`.
Comparing this exact partition with the `q-7` inactive labels available at
the offset port gives

```text
delta_i
 =(q-7)-((q-5)-h_i-s_i^sh)
 =h_i+s_i^sh-2.                                    (1403)
```

Consequently the slack cannot vanish:

```text
1<=delta_i<=5 for every root i,
5<=sum_i delta_i<=25.                              (1404)
```

Thus the exceptions to the near-bijection are neither arbitrary labels nor
an asymptotic error term.  They count, root by root, exactly the ordinary
matching edges diverted through private tickets, together with the optional
strict-sheltered residual edge, minus the fixed two-unit baseline.  Any
attempt to improve the saturation staircase of Section 397 must therefore
act on the finite `B--B/B--O` boundary geometry or exclude shelters; there
is no hidden residual source of payer slack.

## 399. Every exterior color contributes five to ten ordinary edges

The exterior-component coloring of `M` has an exact class-size census.
Let `h` be one of the `r-2` components outside `{c,e}`, and put

```text
k_h:=#{i:gamma_i=h},
```

the number of strict exports whose exterior color is `h`.  The cross
factor from the five-cycle `C` into `h` has degree two at every core root.
The one-root bound (779) makes its ten neighbors distinct, so there are
exactly ten `h`-labels which carry a core root.

The rigid support permutation (777) says that a rooted label meets the
selected set `Z` exactly when it is one of the five strict exports.  Thus
exactly `k_h` of the ten rooted `h`-labels have one endpoint in `Z` and
their other endpoint at the corresponding strict mate in `U`.  Each of the
remaining `10-k_h` labels has both target endpoints in `U` and contributes
one ordinary edge of `M`.  Consequently

```text
|E_h(M)|=10-k_h.                                   (1405)
```

Here `E_h(M)` denotes the set of ordinary matching edges whose actual
rooted label lies in exterior component `h`.  Since the five strict exports
have exactly one exterior color each,

```text
sum_(h outside {c,e}) k_h=5,
0<=k_h<=5.                                         (1406)
```

Equations (1405)--(1406) recover the global edge count color by color:

```text
sum_h |E_h(M)|
 =10(r-2)-5
 =5q-25
 =|E(M)|.                                          (1407)
```

The distinguished secondary component has an additional exact value.  A
strict export has selected incidence one, whereas every `d`-label has even
selected incidence by Section 364.  Hence `k_d=0` and

```text
|E_d(M)|=10.                                       (1408)
```

More generally every exterior color class of `M` has between five and ten
edges.  Its maximum degree is at most two, by the same cross-degree cap
used in the Yeo argument, so each color class is a disjoint union of paths
and cycles with this explicitly bounded total size.  The properly colored
cycle problem therefore has many constant-size color classes rather than a
few large ones: all of the growth in `|E(M)|` comes from the `r-2` different
exterior components.  This histogram is independent of the payer-layer
saturation in Sections 396--398 and supplies a second finite interface for
any sharpened alternating-cycle or transversal argument.

## 400. Total payer slack is an exact private matching statistic

The rootwise formula (1403) sums to one global identity.  Put

```text
b_B:=#{i:v_i in B},
e_BB:=|E(M[B])|,
S_sh:=sum_i s_i^sh.
```

By (1362), the fixed incidence mass on the private set is

```text
mu(B)=20+b_B.
```

Hence (1356) gives

```text
sum_(u in B)deg_M(u)=50-mu(B)=30-b_B.              (1409)
```

The left side of (1409) counts a `B--O` edge once and a `B--B` edge twice,
whereas `sum_i h_i` counts every edge meeting `B` once.  Therefore

```text
sum_i h_i=30-b_B-e_BB.                             (1410)
```

Summing `delta_i=h_i+s_i^sh-2` from (1403) now yields the exact total
unused-pool formula

```text
Delta:=sum_i delta_i
      =20-b_B-e_BB+S_sh.                           (1411)
```

Thus a private strict mate or a private-to-private ordinary edge removes
one unit of global payer slack, while a sheltered residual edge restores
one.  These are the only corrections to the baseline twenty.

There is a direct refinement of the saturation staircase.  For root `i`,
among the `r-4` two-slot layers different from `gamma_i`, every layer not
filled by two offset payers costs at least one unit of `delta_i`.  If `A`
is the number of saturated root--layer pairs, then

```text
A>=sum_i(r-4-delta_i)
  =5r-40+b_B+e_BB-S_sh.                            (1412)
```

Consequently some one of the `r-3` allowed payer layers is saturated at at
least

```text
ceil((5r-40+b_B+e_BB-S_sh)/(r-3))
```

roots.  The coarse staircase (1398) is recovered from `Delta<=25`; (1412)
records exactly when private strict concentration or `B--B` matching mass
forces a stronger common-layer collision.  The remaining finite data are
only the five strict-mate roles, the private matching `M[B]`, and the five
possible shelters.

## 401. Ordinary holonomy avoids any bounded color or payer-layer set

The constant-size exterior color classes convert the edge-transversal
bound into a color-transversal bound.  Let `A` be a set of exterior source
colors and suppose that every properly colored cycle of `M` uses an edge
whose rooted label color lies in `A`.  Then the union of those color classes
is an edge transversal, so (1370) and (1405) give

```text
sum_(h in A)(10-k_h)>=q-12,
|A|>=ceil((q-12)/10).                              (1413)
```

The residual unsheltered graph has the analogous stronger-role statement.
If every properly colored cycle of `G_sh` uses a source color in `A`, then
(1387) gives

```text
sum_(h in A)(10-k_h)>=q-27.                        (1414)
```

There is also a payer-layer version of (1414).  Fix an allowed payment
layer `h`.  At each of the five offset ports there are at most two inactive
selected-singleton labels in `h`, and the offset-payer map is injective.
Thus at most ten edges of `G_sh` have canonical payer layer `h`.  If a set
`P` of payer layers meets the canonical payer layer of every properly
colored cycle, its edge union is again a transversal, and

```text
10|P|>=q-27,
|P|>=ceil((q-27)/10).                              (1415)
```

Equivalently, any source-color set with weight less than `q-27`, or any
set of fewer than `ceil((q-27)/10)` payer layers, can be avoided by one
simple residual unsheltered holonomy cycle.  Two useful uniform
specializations follow.  Since `|E_d(M)|=10`,

```text
binary q>=64
 -> G_sh has a simple PC cycle with no source edge of color d.   (1416)
```

Let `Gamma:={h:k_h>0}` be the strict-export color support.  By (1406),

```text
sum_(h in Gamma)(10-k_h)=10|Gamma|-5<=45.
```

Therefore

```text
binary q>=128
 -> G_sh has a simple PC cycle whose source colors
    avoid every strict-export color.               (1417)
```

The cycles in (1416)--(1417) remain all-`O` and unsheltered, so every edge
still has its distinct core-inactive offset payer from Section 394.  These
avoidance statements separate three notions which need not agree--root,
source component, and payer layer--and show that no bounded collection in
either of the latter two coordinates can control all ordinary holonomy as
`q` grows.  In particular the distinguished double-payer component and the
five strict-export colors can be removed from the source alphabet of a
clean large-binary cycle without any enumeration.

## 402. Exact residual density isolates the `q=16` obstruction

The private slack formula also makes the residual graph size exact.  The
total number of ordinary edges meeting `B` is `sum_i h_i`, so (1355) and
(1410) give

```text
|E(M[O])|
 =5q-25-(30-b_B-e_BB)
 =5q-55+b_B+e_BB.                                  (1418)
```

Every sheltered edge lies in `M[O]`, and `S_sh` counts them exactly.
Consequently

```text
|E(G_sh)|
 =5q-55+b_B+e_BB-S_sh
 =5q-35-Delta,                                     (1419)
```

where the second form uses (1411).  Thus the earlier lower bound `5q-60`
is attained only at the maximum possible slack `Delta=25`; every unit of
private matching or strict-mate concentration retained by (1411) raises
the residual edge count literally.

The graph `G_sh` has `2q-15` vertices.  If it were PC-cycle-free, (1369)
would impose

```text
|E(G_sh)|<=2(2q-15)-3=4q-33.                       (1420)
```

Comparing (1419) and (1420) gives the exact sufficient density condition

```text
q-22+b_B+e_BB-S_sh>0
 -> G_sh contains a simple properly colored cycle. (1421)
```

This is a sufficient condition from the sharp Yeo edge bound, not a
characterization of PC-cycle existence.  For the small binary value left
outside the automatic residual range, it becomes

```text
q=16 and b_B+e_BB-S_sh>=7
 -> a simple all-O unsheltered ordinary holonomy exists.         (1422)
```

Hence the only `q=16` configurations not settled by this density comparison
obey the explicit finite inequality

```text
b_B+e_BB-S_sh<=6.                                  (1423)
```

The large branch still follows at once (indeed `q>=28` works without any
private correction), while (1423) identifies the precise finite geometry
that a `q=16` argument must analyze: few private strict mates and `B--B`
ordinary edges relative to the sheltered residual count.  No residual
endpoint or payer-layer variable remains in that small-value density gap.

## 403. Near-total payer coverage forces linear triple companion reuse

The offset-payer map is also injective after passing to companions at one
fixed port.  For root `i`, let

```text
I_i:=z(E_i(G_sh)),
C_i:=the set of outside companions of labels in I_i.
```

Two distinct labels in `I_i` both meet the selected offset port
`p_(i+2)`.  They cannot also have the same outside companion `o`, since
then `p_(i+2)` and `o` would have those two labels as common neighbors and
would form a four-cycle.  Hence the companion map is injective on `I_i` and

```text
|C_i|=|I_i|
     =q-7-delta_i
     >=q-12.                                       (1424)
```

This is a portwise linear companion bound, much stronger than applying the
mixed-layer capacity estimate to the five ports only in aggregate.  Reuse
is possible only across different ports.  For `o in U`, define

```text
m(o):=#{i:o in C_i}.
```

Portwise injectivity gives `0<=m(o)<=5`.  Payers belonging to different
ports are themselves distinct, and (1419), (1394) give the exact incidence
mass

```text
sum_(o in U)m(o)
 =sum_i|I_i|
 =|E(G_sh)|
 =5q-35-Delta.                                    (1425)
```

Only `|U|=2q-5` outside vertices are available.  Splitting every
multiplicity into its first two slots and its excess therefore yields

```text
sum_(o in U) max(m(o)-2,0)
 >=(5q-35-Delta)-2(2q-5)
 =q-25-Delta
 >=q-50.                                          (1426)
```

Let `H_3:={o:m(o)>=3}`.  Since `m(o)<=5`, one vertex contributes at most
three units to the left side of (1426).  Consequently

```text
|H_3|>=ceil(max(q-25-Delta,0)/3)
     >=ceil(max(q-50,0)/3).                        (1427)
```

In particular binary `q>=64` forces at least five outside vertices which
simultaneously receive inactive offset payers from three or more distinct
selected ports; at `q>=128` it forces at least twenty-six.

These high-multiplicity endpoints retain the color cost of Section 371.
At an endpoint with multiplicity `m`, no payer layer can occur more than
twice, so at least `ceil(m/2)` distinct arrival layers are present, and the
rooted-word deficit satisfies

```text
sum_k(2-t_k(o))>=m(o).                             (1428)
```

Thus the near-bijection cannot realize its linear payer population by
keeping the five port families essentially disjoint.  It forces a linear
set of literal cross-port collision endpoints, each with multi-layer
arrival data and at least three units of missing rooted capacity.  The
remaining terminal may now focus on these named triple-reuse vertices
rather than on arbitrary companion merging.

## 404. A saturated payer layer has a twin active boundary

The common payer layer from Section 397 simultaneously controls rooted
active labels of the same exterior color.  Suppose `h` is saturated at a
set `I` of `t` roots.  Saturation uses two core-inactive `h`-labels at the
offset port of each `i in I`, so necessarily

```text
h!=gamma_i for every i in I.                       (1429)
```

The cross factor from root `x_i` into component `h` has exactly two rooted
labels.  By (1429), neither is the strict export; both therefore have two
target endpoints in `U` and give ordinary `h`-colored edges of `M`.
Consequently component `h` contains two disjoint populations:

```text
2t rooted active labels, each with target type U--U;
2t core-inactive offset payers, each with target type Z--U.      (1430)
```

They are disjoint because the second population does not meet `C`.  The
active population contributes `4t` incidences at `U`, and the payer
population contributes its `2t` outside-companion incidences.  Every
vertex of `U` has cross degree two into component `h`, so their combined
support satisfies

```text
|U endpoints used by the two populations|>=3t.     (1431)
```

This gives support at least nine, twelve, and fifteen in the three
saturation ranges of (1398).

At `q>=128`, Section 397 gives `t=5`.  Then (1429) says `k_h=0`, and the
exterior-color census (1405) says that the ten active labels in (1430) are
exactly all ten ordinary edges of color `h`.  The ten payer labels are also
exactly all `h`-labels meeting `Z`, two at each selected port.  Thus

```text
q>=128:
  h has ten rooted U--U labels and ten inactive Z--U labels,
  with no strict h-export.                          (1432)
```

There is a canonical path pairing behind (1432).  The incidence graph
between the vertices of component `h` and the target component `e` is
bipartite and two-regular: every label has two `e`-neighbors and every
`e`-vertex has two `h`-neighbors.  Delete the five selected vertices `Z`.
The ten payer labels in (1432) become the only degree-one vertices.  Each
two-regular cycle which met `Z` breaks into paths, and altogether the five
deleted vertices create exactly five disjoint paths.  Hence

```text
the ten inactive h-payers are paired by five vertex-disjoint
alternating h--e paths whose internal e-vertices lie in U.       (1433)
```

Cycles of the `h--e` factor which avoid `Z` remain disjoint from these
paths.  Equation (1433) is a normal form, not yet an impossibility: a path
may pair the two payers from one port or from different ports.  Its gain is
to replace the large-parameter common-layer branch by a fixed ten-terminal
path system coupled to the ten ordinary rooted `h`-edges and the companion
color-deletion law of (1399).

## 405. The saturated five-port boundary has an odd pairing component

The five paths in (1433) have a finite quotient which retains their port
incidence.  For each payer terminal, record the unique selected port in
`Z` which was deleted next to it.  Contract every one of the five
vertex-disjoint paths to an edge joining the recorded ports of its two
terminals.  If both terminals came from one port, retain the resulting
loop; if two paths join the same pair, retain parallel edges.  Call the
resulting multigraph `P_h` on the five selected ports.

Every selected port has exactly two `h`-payer terminals, and every terminal
is the endpoint of exactly one path.  With loops counted twice in degree,

```text
deg_(P_h)(p)=2 for every p in Z,
|E(P_h)|=|Z|=5.                                    (1434)
```

Thus `P_h` is a two-regular multigraph: its connected components are
cycles, allowing a one-vertex loop and a two-vertex parallel-edge cycle.
The component orders sum to five, so at least one component has odd order.
Equivalently,

```text
P_h has a cycle component on 1, 3, or 5 ports.     (1435)
```

This quotient has a literal interpretation before deletion.  The path
components obtained from one original cycle of the two-regular `h--e`
factor contract to one cycle component of `P_h`; conversely reinserting
the selected ports expands that quotient component back to the original
factor cycle.  Therefore (1435) says

```text
some cycle of the h--e factor meets Z in exactly 1, 3, or 5 vertices.
                                                        (1436)
```

The statement is deliberately parity-exact without excluding loops or
parallel pairings: those are real possibilities left open by (1433), and a
loop is precisely a factor cycle containing only one selected port.  At
`q>=128`, the common saturated layer therefore cannot pair its ten inactive
boundary labels by an entirely even port pattern.  Any terminal argument
may split into the three finite odd cases in (1436), while all other
boundary-free `h--e` cycles remain irrelevant to this five-port quotient.

## 406. The `q=16` density gap has two high-loss roots

Return to the finite branch left by (1423).  At `q=16`, failure of the
exact density comparison to force a residual unsheltered cycle means

```text
b_B+e_BB-S_sh<=6.
```

Using (1411), this is equivalently the high-slack condition

```text
Delta=sum_i delta_i>=14.                            (1437)
```

Each root slack lies between one and five by (1404).  If at most one root
had slack at least three, their total would be at most `5+4*2=13`, contrary
to (1437).  Hence there are distinct roots `i,j` with

```text
delta_i,delta_j>=3,
h_i+s_i^sh, h_j+s_j^sh>=5.                         (1438)
```

The boundary table (1402) makes (1438) completely local.  For either such
root `i`, exactly one of the following holds:

```text
v_i in O:
  E_i(O,B)>=4,
  or E_i(O,B)=2 and s_i^sh=1;

v_i in B:
  E_i(O,B)=5,
  or E_i(O,B)=3 and s_i^sh=1.                      (1439)
```

Indeed the omitted boundary values give `h_i<=3`, or give `h_i=4` without
the shelter needed to reach five in (1438).  Thus every high-slack root
either sends at least four residual-to-private ordinary edges (five when
its strict mate is private), or lies in one of the two explicitly sheltered
next-boundary cases.

There is an equivalent payer statement.  At `q=16` the inactive pool at
one offset port has size `q-7=9`, and (1394) is exact.  Therefore each of
the two roots in (1438) satisfies

```text
|E_i(G_sh)|=9-delta_i<=6.                           (1440)
```

Consequently the small density gap is not an unstructured failure of the
large-`q` estimate.  It forces two named root matchings into the finite
alternatives (1439), with at least three missing offset payers apiece and
at most six clean residual edges apiece.  All other `q=16` configurations
already fall into the simple all-`O` unsheltered cycle branch of (1422).
The remaining finite task is to couple the two high-loss private boundaries
through their pair graph or through the two possible shelter rows.

## 407. Two selected ports support a linear inactive theta system

The cross-port multiplicities of Section 403 concentrate on one pair of
ports.  Double-count the pairs of port families which reuse an outside
companion:

```text
sum_(i<j)|C_i intersect C_j|
 =sum_(o in U) binom(m(o),2).                       (1441)
```

For every integer `0<=m<=5`, one has
`binom(m,2)>=2m-3`.  Using (1425) and `|U|=2q-5`
therefore gives

```text
sum_(i<j)|C_i intersect C_j|
 >=2(5q-35-Delta)-3(2q-5)
 =4q-55-2Delta
 >=4q-105.                                         (1442)
```

There are only ten unordered pairs of selected ports.  Hence some pair
`p_(i+2),p_(j+2)` has a common companion set of size

```text
K_ij:=|C_i intersect C_j|
 >=ceil(max(4q-55-2Delta,0)/10)
 >=ceil(max(4q-105,0)/10).                         (1443)
```

For each `o in C_i intersect C_j`, let `z_i(o),z_j(o)` be the unique
inactive payer labels from the two port families.  They give the literal
ambient path

```text
p_(i+2)--z_i(o)--o--z_j(o)--p_(j+2).               (1444)
```

The paths (1444) are internally vertex-disjoint as `o` varies.  Their
middle vertices are distinct by definition, and portwise companion
injectivity makes the payer labels distinct in each family; labels from
the two different families are distinct because every non-`d` payer has
selected incidence one and the selected ports differ.

Thus the two selected ports are the branch vertices of a theta system with
`K_ij` internally disjoint paths of length four.  In particular every pair
of these paths is a simple eight-cycle, so the system contains
`binom(K_ij,2)` distinct eight-cycles.  Numerically,

```text
q>=64  -> K_ij>=16;
q>=128 -> K_ij>=41.                                (1445)
```

This does not contradict four-cycle-freeness--length eight is allowed--but
it converts the diffuse companion reuse into one explicit two-port
subgeometry of linear width.  A final obstruction can now couple the
source colors, payer layers, or SRP rows along many paths with the same two
selected endpoints rather than comparing unrelated collision vertices.

## 408. Odd saturated-layer pairing is locally factor-realizable

The odd port component in Section 405 is not by itself a contradiction.
There is an explicit layer-level model realizing the strongest `t=5`
boundary from Section 404.  On the `e` side take the five selected ports
`p_i`, five further vertices `u_i`, and ten further vertices `v_j`.  On the
`h` side take ten inactive payer labels `a_i,b_i` and ten rooted active
labels `y_j`, with indices modulo five and ten respectively.

Put the boundary incidences in the single cycle

```text
p_i -- a_i -- u_i -- b_(i+1) -- p_(i+1)
for i=0,...,4 cyclically.                           (1446)
```

Thus port `p_i` owns the two payer terminals `a_i,b_i`.  Their outside
companions are `u_i,u_(i-1)`, so they are distinct as required by
four-cycle-freeness.  At `u_i`, the payers `a_i,b_(i+1)` collide; they
exhaust the two `h`-neighbors and delete rooted color `h` there.  Contracting
the five paths in (1446) gives exactly the quotient five-cycle of Section
405.

Independently put the active incidences in the cycle

```text
v_j -- y_j -- v_(j+1)
for j=0,...,9 cyclically,                           (1447)
```

and assign `y_i,y_(i+5)` to root `x_i`.  Then every root has exactly two
active `h`-labels, each with target type `U--U`, while all ten payer labels
have target type `Z--U` and are core-inactive.  The two displayed components
are disjoint 20-cycles.  Hence their union is bipartite, two-regular, and
contains no four-cycle.  It realizes

```text
ten active rooted h-labels;
ten inactive selected h-payers;
five collision companions and the odd five-port pairing.        (1448)
```

Additional disjoint even cycles of length at least six may fill the unused
vertices of the `h--e` factor without changing (1446)--(1448).

This is deliberately a factor-level countermodel, not a model of all
simultaneous SRP equations: it does not specify the internal graph `A_h`
or the other cross factors.  Its role is to audit the terminal boundary.
Neither two-regularity, four-cycle-freeness, the exact twin population, nor
odd port-pairing parity excludes the saturated layer.  Any successful
continuation must use coupling to `A_h`, the source/payer-layer assignments,
the large cross-layer theta system of Section 407, or another simultaneous
SRP constraint absent from this local factor.

## 409. Deep `q=16` slack forces an adjacent high-loss pair

The two-root conclusion of Section 406 strengthens once the total slack
passes sixteen.  Call a root **high-loss** when `delta_i>=3`.  If at most
two roots were high-loss, then (1404) would give

```text
Delta<=2*5+3*2=16.                                 (1449)
```

Therefore

```text
Delta>=17 -> at least three roots are high-loss.   (1450)
```

The independence number of the five-cycle on the core roots is two, so
three high-loss roots contain an adjacent pair `x_i,x_j`.  Both members of
that pair satisfy the explicit private-boundary/shelter alternatives
(1439).  In addition, adjacency locates their common artificial fixed set:

```text
|B_(x_i) intersect B_(x_j)|=2                     (1451)
```

by (1331), and those two private tickets are isolates of the pair matching
graph `Gamma_ij`.  Thus the deep-slack branch supplies an adjacent
high-loss pair together with its two named common fixed tickets; it is not
merely an arbitrary pair among the five roots.

Using (1411), the complementary shallow band is finite at the scalar level:

```text
Delta in {14,15,16}
 iff b_B+e_BB-S_sh in {6,5,4}, respectively.       (1452)
```

Consequently the `q=16` density gap splits exactly into two targets:

```text
Delta>=17:
  an adjacent pair of roots obeys the high-loss alternatives (1439)
  and has the two fixed private tickets (1451);

Delta in {14,15,16}:
  the global private statistic b_B+e_BB-S_sh is exactly 6, 5, or 4.
                                                        (1453)
```

This is still a reduction, not an exclusion.  Its purpose is to expose the
next finite coupling: the adjacent branch can use the exact two-root path
decomposition of Sections 382--387 at the same time as the two high-loss
private boundaries, while the shallow band has only three possible global
boundary totals to realize.

## 410. The residual graph is five near-perfect matchings with constant defect

The exact port slack also gives a useful global normal form.  For each root
`i`, let `G_i` be the root-`i` matching class of `G_sh`.  It is a matching on
the common residual vertex set `O`, and (1394) together with the exact
edge/payer bijection gives

```text
|G_i| = q-7-delta_i.                              (1454)
```

Write `H_i := O \ V(G_i)` for its unmatched set.  Since `|O|=2q-15`,

```text
|H_i| = (2q-15)-2(q-7-delta_i)
      = 2 delta_i-1 in {1,3,5,7,9}.               (1455)
```

Thus every rooted matching is near-perfect on the same odd set, with an
odd defect of at most nine.  For `o in O`, put
`eta(o):=#{i:o in H_i}`.  The five matching colors are disjoint, so

```text
deg_G_sh(o)=5-eta(o),
sum_(o in O) eta(o)=sum_i(2 delta_i-1)=2 Delta-5,
5 <= 2 Delta-5 <= 45.                             (1456)
```

In particular at most `2 Delta-5` residual vertices miss even one root
matching.  The full-root sector

```text
O_5 := {o in O : eta(o)=0}
```

therefore satisfies

```text
|O_5| >= |O|-(2 Delta-5)
      = 2q-10-2 Delta >= 2q-60.                   (1457)
```

Every vertex of `O_5` has all five rooted actions represented by ordinary
`O`--`O`, unsheltered edges of `G_sh`, one in each root matching.  Finally,
summing the degrees in (1456) recovers the exact residual density:

```text
2|E(G_sh)| = 5|O|-(2 Delta-5),
|E(G_sh)|  = 5q-35-Delta.                         (1458)
```

Hence the entire residual graph is a union of five near-perfect matchings
whose departure from five-regularity is concentrated in at most forty-five
root incidences, independent of `q`.  This is a structural normal form, not
yet a contradiction; it isolates a large sector on which every root action
is simultaneously ordinary and unsheltered.

## 411. An adjacent high-loss pair either shares an exit or has one finite profile

The adjacent pair in the deep `q=16` branch has a direct private-boundary
coupling.  For root `i`, put

```text
A_i:=B setminus B_(x_i),
Q_i:={u in B:the ordinary root-i edge at u has its other endpoint in O}.
```

Thus `|A_i|=6`, `Q_i subset A_i`, and
`|Q_i|=E_i(O,B)`.  If roots `i,j` are adjacent on the core cycle, then
(1331) gives `|B_(x_i) intersect B_(x_j)|=2`; since both artificial blocks
have size four,

```text
|A_i intersect A_j|=4,
|A_i setminus A_j|=|A_j setminus A_i|=2.           (1459)
```

At most two members of `Q_i` lie outside the common active set, and the
same holds for `Q_j`.  Inclusion--exclusion inside the four common tickets
therefore gives

```text
|Q_i intersect Q_j|
 >=max(E_i(O,B)+E_j(O,B)-8,0).                     (1460)
```

Consequently an adjacent high-loss pair whose two boundary counts sum to
at least nine has a private ticket `u` at which both ordinary root edges
exit to `O`.  Writing their distinct indexing labels as `y_i,y_j`, one has

```text
u--y_i--o_i,       u--y_j--o_j,
o_i,o_j in O,      o_i!=o_j.                       (1461)
```

The last inequality is forced by four-cycle-freeness: equality would make
`u,o_i` have the two distinct common neighbors `y_i,y_j`.  Ticket
nonmonochromaticity also makes (1461) dynamically usable.  If `y_i,y_j`
have different exterior colors, they give the color-changing transition
through `u`; if their colors agree, the ticket's third rooted label has a
different color and gives such a transition with either one.

The contrapositive is a sharp finite alternative:

```text
Q_i intersect Q_j=emptyset
 -> E_i(O,B)+E_j(O,B)<=8.                           (1462)
```

If neither high-loss root is sheltered, the table (1439) then forces the
unique no-common-exit profile

```text
v_i,v_j in O,
E_i(O,B)=E_j(O,B)=4.
```

Indeed a private strict mate would force boundary count five, and a
residual mate with the next allowed unsheltered count has boundary at least
four (then six).  Thus the adjacent deep-slack branch reduces further:
either one named private ticket couples the two high roots to two distinct
residual endpoints and a legal color transition, or at least one shelter
is present, except for the single unsheltered `O/O,4+4` boundary profile.

## 412. At `q>=128` holonomy survives inside the full-root sector

The constant matching defect in Section 410 can be removed without losing
all properly colored cycles.  Let

```text
S:=O setminus O_5,       s:=|S|.
```

Every hole incidence counted by `eta` lies on `S`, so (1456) gives the
exact degree sum

```text
sum_(o in S)deg_G_sh(o)
 =5s-(2Delta-5).                                    (1463)
```

Deleting `S` removes at most this many edges; an edge internal to `S` is
counted twice and only improves the estimate.  Using (1458),

```text
|E(G_sh[O_5])|
 >=(5q-35-Delta)-(5s-(2Delta-5))
 =5q-40+Delta-5s.                                  (1464)
```

The induced full-root sector has `|O_5|=2q-15-s` vertices.  Subtract its
PC-cycle-free Yeo ceiling from (1464):

```text
|E(G_sh[O_5])|-(2|O_5|-3)
 >=q-7+Delta-3s
 >=q+8-5Delta,                                     (1465)
```

where the last inequality uses `s<=2Delta-5` from (1457).  Hence

```text
q>5Delta-8
 -> G_sh[O_5] contains a simple properly colored cycle.          (1466)
```

Since `Delta<=25`, the right side of (1465) is at least `q-117`.
Consequently

```text
every binary q>=128 has a simple all-O unsheltered holonomy
whose every physical vertex lies in O_5.            (1467)
```

At each vertex of this cycle all five root matchings are present as
ordinary unsheltered actions, not only the two cycle edges.  The rooted
component-color multiplicity cap is two, so those five actions occupy at
least three exterior colors.  Thus the very-large branch has a clean cycle
inside a sector with no missing root action and no private, strict, or
sheltered local exception.  Any remaining obstruction there must use the
simultaneous five-action/color geometry rather than the bounded hole set.

## 413. The full-root sector obeys a simultaneous five-color cut parity

The five matching classes carry more information than their total density.
For any `X subseteq O`, count the vertices of `X` matched by `G_i`.  Internal
matching edges contribute two vertices, crossing edges contribute one, and
the vertices in `H_i intersect X` contribute zero.  Therefore

```text
|X|-|H_i intersect X|
 =2|E(G_i[X])|+|partial_(G_i)X|,                  (1468)
```

and hence

```text
|partial_(G_i)X|
 =|X|-|H_i intersect X|                           (mod 2).       (1469)
```

In particular, if `X subseteq O_5`, then no root matching has a hole on
`X`, so all five rooted boundary counts have the same parity:

```text
|partial_(G_0)X| = ... = |partial_(G_4)X|
                   = |X|                         (mod 2).        (1470)
```

This applies especially to a connected component `C` of the induced graph
`G_sh[O_5]`.  No matching edge joins `C` to another vertex of `O_5`, so its
whole boundary lands in the bounded defect sector `S=O setminus O_5`.
Equation (1470) then gives the dichotomy

```text
|C| odd  -> every one of the five root matchings has an odd,
            hence nonzero, boundary from C to S;
|C| even -> every one of the five root-matching boundaries is even.
                                                               (1471)
```

Thus every odd full-root component sends at least five rooted matching
edges into the hole sector, one of each root type.  More generally, no cut
inside `O_5` can have an independently chosen pattern of rooted boundary
parities: the five coordinates are locked to the single bit `|X| mod 2`.
This simultaneous parity constraint is q-generic and survives even when
ordinary edge density or properly colored-cycle existence alone gives no
further information.

## 414. A shortest full-root holonomy has linear boundary

Choose a shortest simple properly colored cycle in `G_sh[O_5]`, and write

```text
Q=(v_0,v_1,...,v_(ell-1),v_0),
c_j:=the exterior color of v_j v_(j+1),
```

with subscripts read modulo `ell`.  Consider a chord `v_a v_b` of color
`h`.  The chord together with either of the two `v_a`--`v_b` arcs of `Q`
forms a simple cycle shorter than `Q`.  Each shortcut cycle is properly
colored away from the chord endpoints, and hence must fail proper coloring
at one of those endpoints by the choice of `Q`.  Applied to the two arcs,
this says

```text
h in {c_a,c_(b-1)} intersect {c_b,c_(a-1)}.        (1472)
```

Proper coloring of `Q` gives `c_(a-1)!=c_a` and
`c_(b-1)!=c_b`.  The two same-endpoint intersections in (1472) are
therefore impossible, leaving exactly the two chord types

```text
h=c_a=c_b,       or       h=c_(a-1)=c_(b-1).       (1473)
```

Thus every chord incident with `v_j` has one of the two colors already
used by the cycle edges at `v_j`.  For either such color, the exterior
component-color degree cap two has already spent one incidence on the
corresponding cycle edge, so it permits at most one additional chord.
Consequently

```text
deg_(G_sh[V(Q)])(v_j)<=2+2=4.                      (1474)
```

Every `v_j` lies in `O_5`, so its degree in the whole shadow graph is
exactly five.  Subtracting (1474), every cycle vertex sends at least one
edge out of the cycle, and summing these distinct boundary incidences gives

```text
|partial_(G_sh)V(Q)|
 =sum_(v in V(Q))(5-deg_(G_sh[V(Q)])(v))
 >=ell=|V(Q)|.                                    (1475)
```

Hence the clean holonomy supplied by Section 412 can be chosen with a
linear edge boundary: no shortest properly colored cycle in the full-root
sector can absorb all five ordinary root actions locally.  Its chords are
rigidly typed by (1473), and at least one action at every cycle vertex must
leave the cycle.  This is a genuine expansion constraint, not merely the
existence of a color-changing circuit.

## 415. The defect sector gives an exact odd-component budget

The component parity of Section 413 can be quantified root by root.  Put

```text
b_i:=|partial_(G_i)O_5|,       e_i(S):=|E(G_i[S])|,
S:=O setminus O_5,             s:=|S|.
```

Exactly `s-|H_i|` vertices of `S` are matched by `G_i`.  Its internal
edges use two such vertices and its boundary edges use one, so (1455)
gives

```text
s-(2delta_i-1)=2e_i(S)+b_i,
b_i=s-2delta_i+1-2e_i(S).                         (1476)
```

Let `r` be the number of odd connected components of `G_sh[O_5]`.
By (1471), each odd component contributes a positive odd number to every
`b_i`, whereas each even component contributes an even number.  Therefore

```text
b_i>=r,       b_i=r                              (mod 2),
r<=min_i b_i<=s-2delta_max+1.                     (1477)
```

Summing (1476) over the five disjoint root matching classes gives the
aggregate boundary identity

```text
sum_i b_i
 =5s-(2Delta-5)-2|E(G_sh[S])|,
5r<=5s-(2Delta-5)-2|E(G_sh[S])|.                  (1478)
```

There is a useful equality endpoint.  Since every `H_i` is contained in
`S`, one always has `s>=2delta_max-1`.  If equality holds, then for a root
with `delta_i=delta_max` one has `S=H_i`, hence `b_i=0` in (1476), and

```text
s=2delta_max-1 -> r=0:
every connected component of G_sh[O_5] is even.   (1479)
```

Thus the bounded hole sector controls not only how many full-root vertices
are lost, but also the parity census of the components that remain.  Odd
components consume one boundary edge of every root type, and internal
matching edges inside `S` reduce their available budget two at a time.

## 416. A shortest clean holonomy has an exact five-root boundary spectrum

The cut parity and the shortest-cycle expansion admit a common exact form.
Let `Q` be the shortest properly colored cycle chosen in Section 414, put
`ell:=|V(Q)|`, and for each root matching write

```text
a_i:=|E(G_i[V(Q)])|,       b_i:=|partial_(G_i)V(Q)|.
```

Every vertex of `Q subseteq O_5` is matched exactly once by `G_i`.
Counting its root-`i` incidences therefore gives, coordinate by coordinate,

```text
ell=2a_i+b_i,
b_i=ell-2a_i in {0,...,ell},
b_i=ell (mod 2).                                  (1480)
```

Thus (1470) is not only a parity constraint here: the five rooted boundary
coordinates record exactly how many internal edges of each matching the
cycle and its chords consume.  Let `c` be the number of chords of `Q` in
`G_sh`.  The five matching classes partition the internal shadow edges, so

```text
sum_i a_i=ell+c.
```

Summing (1480) consequently yields the exact total boundary

```text
B:=|partial_(G_sh)V(Q)|
  =sum_i b_i
  =5ell-2(ell+c)
  =3ell-2c.                                       (1481)
```

Section 414 bounds the chord degree of every cycle vertex by two.  Hence
`2c<=2ell`, or `c<=ell`, and (1481) sharpens (1475) to the spectrum

```text
ell<=B<=3ell,
B=ell (mod 2),
B-ell=2(ell-c).                                   (1482)
```

In particular, if `ell` is odd, then every `b_i` is a positive odd integer:
the shortest clean holonomy sends at least one boundary edge of every root
type, regardless of how many of its other root actions are absorbed by
chords.  If `ell` is even, a root coordinate may vanish, but only by using
exactly `ell/2` internal edges of that matching.  Thus the remaining
large-`q` obstruction has a rigid five-coordinate cut vector, not merely a
scalar lower bound.  The equality case in (1482) is analyzed next via the
signed chord graph.

## 417. The signed chord graph is bipartite and measures boundary surplus

Let `D_Q` be the graph on `V(Q)` whose edges are precisely the chords of
the shortest cycle `Q`.  At `v_j`, call a chord outgoing if its color is
`c_j` and incoming if its color is `c_(j-1)`.  These types are distinct
because `Q` is properly colored.  The chord law (1473) says more than
local color reuse:

```text
every chord has the same type at both endpoints.                  (1483)
```

Moreover the component-color degree cap permits at most one outgoing and
at most one incoming chord at each vertex.  Thus `D_Q` has maximum degree
two, and whenever a vertex has chord degree two its two incident chords
have opposite types.

Now traverse a cycle component of `D_Q`.  Across an edge its type is
unchanged by (1483), while at the next vertex the other edge has the
opposite type.  The edge types therefore alternate around the component,
so the component has even length.  All other components are paths
(including isolated vertices).  Consequently

```text
D_Q is bipartite and is a disjoint union of even cycles and paths.       (1484)
```

This decomposition exactly measures the surplus in (1482).  Let `p` be
the number of path components of `D_Q`, counting an isolated vertex as a
path.  Every cycle component has equally many vertices and edges, whereas
every path component has one more vertex than edge.  Since
`|V(D_Q)|=ell` and `|E(D_Q)|=c`,

```text
ell-c=p,
|partial_(G_sh)V(Q)|-ell=2p.                     (1485)
```

In particular the linear boundary bound is tight exactly when `p=0`, or
equivalently when every cycle vertex has two chords.  At that endpoint

```text
|partial_(G_sh)V(Q)|=ell
 <-> D_Q is a disjoint union of even cycles.       (1486)
```

Otherwise the boundary is at least `ell+2`, with exactly two additional
exit incidences for every path component of the chord graph.  Hence the
only way a shortest clean holonomy can attain minimal expansion is through
a spanning two-regular bipartite chord system; any break in that system
pays a quantified boundary surplus.

## 418. Every shortest-cycle vertex has a root-new and color-new exit

The chord law also couples the two distinct edge labels: exterior color
and core root.  Write `rho(e)` for the root matching containing a shadow
edge `e`.  At every vertex of `O_5`, the five incident shadow edges consist
of exactly one edge from each `G_i`.  In particular the two cycle edges at
`v_j` have distinct roots:

```text
rho(v_(j-1)v_j) != rho(v_jv_(j+1)).                (1487)
```

If a chord at `v_j` is outgoing, (1473) says that it repeats exterior
color `c_j`; if it is incoming, it repeats `c_(j-1)`.  But it cannot repeat
the root of the corresponding cycle edge, because a matching has degree at
most one at `v_j`.  Thus every chord is simultaneously

```text
same exterior color as one incident cycle edge,
different core root from both incident cycle edges.              (1488)
```

This already forces an escape at every cycle vertex, without assuming
tightness.  If `d_j in {0,1,2}` is the chord degree at `v_j`, then its
`2+d_j` internal incidences use distinct roots and its `3-d_j` boundary
incidences use precisely the complementary roots.  Among the two incident
cycle colors, the unused degree capacity is only `2-d_j`: each chord
saturates the cycle color whose type it has.  Since there are `3-d_j`
boundary edges, at least one boundary edge `f_j` must satisfy

```text
rho(f_j) is not used by any internal edge at v_j,
color(f_j) notin {c_(j-1),c_j}.                    (1489)
```

Now assume the tight endpoint `|partial V(Q)|=ell`.  By (1486), every
cycle vertex has exactly two chords, one outgoing and one incoming.  The
four internal incidences at `v_j` lie in four distinct root matchings, so
the unique boundary edge `f_j` lies in the fifth:

```text
{rho(e): e incident with v_j, e internal to V(Q)} has size 4;
rho(f_j) is its unique complementary root.                        (1490)
```

There is an equally rigid exterior-color conclusion.  The two cycle
colors are distinct, the outgoing chord repeats `c_j`, and the incoming
chord repeats `c_(j-1)`.  Hence the four internal color incidences are

```text
{c_(j-1),c_(j-1),c_j,c_j}.
```

The component-color degree cap two has saturated both colors.  Therefore
the unique exit has a third color:

```text
color(f_j) notin {c_(j-1),c_j}.                    (1491)
```

Consequently no shortest clean holonomy is locally closed.  Every one of
its vertices has an action new in both coordinates; at minimal boundary
this action is canonical, with the missing fifth root and a third exterior
color.  This crossed root/color escape is the simultaneous-routing
information absent from the uncolored chord graph, and is the interface
through which the cycle can restart the tagged propagation machinery of
Sections 357--363.

## 419. Full-root holonomy avoids bounded source colors and payer layers

The avoidance principle of Section 401 can be imposed without leaving the
full-root sector.  Retain `S=O setminus O_5`, `s=|S|`, and put

```text
R_5:=q-7+Delta-3s.
```

By (1465), the edge surplus of `G_sh[O_5]` over its properly-colored-cycle-
free ceiling is at least `R_5`, and

```text
R_5>=q+8-5Delta>=q-117.                           (1492)
```

Let `A` be a set of exterior source colors.  If every properly colored
cycle in `G_sh[O_5]` uses a color in `A`, delete all such edges.  The
remaining graph is PC-cycle-free, so the number deleted is at least its
original surplus, hence at least `R_5`.  On the other hand (1405) bounds
the total number of available edges of color `h` by `10-k_h`.  Therefore

```text
every PC cycle in G_sh[O_5] meets A
 -> sum_(h in A)(10-k_h)>=R_5.                    (1493)
```

The same argument applies to canonical payer layers.  Injectivity of the
offset-payer map and the five two-slot offset ports bound the edges paid
from any one layer by ten, exactly as in (1415).  Thus for every payer-layer
set `P`,

```text
every PC cycle in G_sh[O_5] has a payer layer in P
 -> 10|P|>=R_5.                                   (1494)
```

Equivalently, a source-color set of total weight below `R_5`, or a payer-
layer set with `10|P|<R_5`, can be avoided by a simple properly colored
cycle wholly inside `O_5`.  Two uniform consequences sharpen (1416)--
(1417).  The distinguished color `d` has weight ten by (1408), while the
strict-export support `Gamma={h:k_h>0}` has total weight at most forty-five
by (1406).  Since `Delta<=25`, (1492) gives

```text
binary q>=128
 -> G_sh[O_5] has a simple PC cycle avoiding source color d;

binary q>=256
 -> G_sh[O_5] has a simple PC cycle avoiding every source color
    in Gamma.                                      (1495)
```

These cycles retain all of Section 412's cleanliness: every vertex has all
five ordinary unsheltered root actions, while every cycle edge has its
distinct core-inactive payer.  Thus neither the distinguished double-payer
component, the five strict-export colors, nor any fixed bounded set of
payer layers can control full-root holonomy in the large binary branch.

## 420. Color-new exits give external vertex expansion

The uniform escape in Section 418 converts the edge boundary of a shortest
clean holonomy into a vertex boundary.  Let `Q` have length `ell>=5`.  At
each `v in V(Q)`, choose one boundary edge

```text
f_v=v w_v
```

whose root is unused by the internal edges at `v` and whose exterior color
is different from both incident cycle colors, as guaranteed by (1489).
Suppose two chosen exits `f_u,f_v` have the same outside endpoint `w` but
different exterior colors.  Join `u` to `v` along the shorter of the two
arcs of `Q`.  The resulting two-edge ear cycle has length at most

```text
floor(ell/2)+2<ell.                               (1496)
```

All transitions internal to the arc are proper.  At `u` and `v` they are
proper because the chosen exit color is new against both incident cycle
colors; at `w` they are proper by the assumed difference of the two exit
colors.  This contradicts the minimality of `Q`.  Therefore

```text
w_u=w_v -> color(f_u)=color(f_v).                 (1497)
```

The exterior component-color degree cap is two.  Hence no outside vertex
can receive three chosen exits: (1497) would give all three the same color,
violating that cap.  Consequently the chosen root-new/color-new exits obey

```text
#{w_v:v in V(Q)} >= ceil(ell/2).                  (1498)
```

Moreover, whenever equality is lost locally through a collision, the two
colliding exits form a monochromatic pair at their outside endpoint.  They
still have different root types, since each root class is a matching.
Thus every shortest clean holonomy of length at least five has linear
external **vertex** expansion, with the only permitted two-to-one merging
explicitly typed:

```text
same outside endpoint and same exterior color,
but two distinct complementary roots.             (1499)
```

Cycles of length three or four remain a bounded local alternative because
the ear in (1496) need not be strictly shorter there.  Beyond that finite
case, the simultaneous five-action escape cannot be absorbed by a bounded
set of outside companions.

## 421. A clean triangle has an exact root-boundary spectrum

The triangular alternative in Section 420 is rigid at the root level.  Let

```text
Q=(v_0,v_1,v_2,v_0).                              (1500)
```

Its three edge colors are pairwise distinct.  Its three root types are
also pairwise distinct: at each triangle vertex the two incident edges
belong to different root matchings.  There are no chords, so (1480) gives,
up to permuting the five roots,

```text
(a_0,...,a_4)=(1,1,1,0,0),
(b_0,...,b_4)=(1,1,1,3,3).                        (1501)
```

Thus each triangle vertex has exactly three boundary edges, one in every
root matching complementary to its two incident cycle roots, and the
triangle has nine boundary edges in total:

```text
|partial_(G_sh)V(Q)|=9.                            (1502)
```

This does **not** imply nine distinct outside endpoints.  A shadow edge
records the two target endpoints of an intermediate rooted label, so a
four-cycle in `G_sh` generally lifts to an eight-cycle in the original
target factor and is allowed.  Original four-cycle-freeness guarantees
simplicity of the shadow matching edges, but does not make `G_sh`
four-cycle-free.  Therefore

```text
ell=3: exact root cut vector (1,1,1,3,3), but exit collisions remain;
ell=4: a finite shadow alternative, not excluded by target C4-freeness;
ell>=5: the ear law (1497)--(1499) applies.                         (1503)
```

Thus the triangle has a fully determined five-root boundary spectrum, but
the small-length endpoint-collision problem remains genuinely open.  Any
exclusion of lengths three or four must use exterior colors, payer tags,
or another simultaneous-SRP constraint rather than incorrectly importing
four-cycle-freeness into the shadow graph.

## 422. The hole sector can absorb only a bounded part of vertex expansion

Let `Q` be a shortest clean holonomy of length `ell>=5`, and let

```text
W:={w_v:v in V(Q)}
```

be the chosen-exit endpoint set from Section 420.  Every member of `W`
lies in `O setminus V(Q)`, and (1498) gives

```text
|W|>=ceil(ell/2).                                  (1504)
```

Only `s=|S|` of these distinct endpoints can lie in the hole sector
`S=O setminus O_5`.  All remaining endpoints lie in `O_5 setminus V(Q)`
and are joined to `Q` by edges of the induced full-root graph.  If `C_Q`
is the connected component of `G_sh[O_5]` containing `Q`, then

```text
|W intersect O_5|>=max(ceil(ell/2)-s,0),
|C_Q|>=ell+max(ceil(ell/2)-s,0).                   (1505)
```

Thus a full-root component whose vertex set is exactly the shortest cycle
can exist only in the constant range

```text
V(C_Q)=V(Q)
 -> ceil(ell/2)<=s
 -> ell<=2s<=4Delta-10<=90.                       (1506)
```

More generally (1505) quantifies how many additional full-root vertices
the component must contain once the clean cycle is longer than the defect
sector can absorb.  The bound deliberately retains the length-three and
length-four alternatives of (1503); their endpoint collisions need the
separate finite simultaneous-color analysis identified there.  For every
longer shortest holonomy, however, a bounded hole set cannot hide linear
vertex expansion inside the shadow graph.

## 423. The four-cycle exception still has two-point exit expansion

Although target four-cycle-freeness does not exclude a four-cycle in the
shadow graph, shortestness still controls its adjacent exit collisions.
Let

```text
Q=(v_0,v_1,v_2,v_3,v_0)
```

be a shortest properly colored cycle, and choose at each `v_j` one
root-new/color-new boundary edge `f_j=v_jw_j` using (1489).  Suppose two
adjacent vertices have the same chosen outside endpoint, say
`w_j=w_(j+1)=w`.  If the two exit colors were different, then

```text
v_j -- v_(j+1) -- w -- v_j                       (1507)
```

would be a properly colored triangle.  The transition at each cycle
vertex is proper because its chosen exit color differs from both incident
cycle colors, and the transition at `w` is proper by the assumed color
difference.  This contradicts the choice of the four-cycle as shortest.
Therefore

```text
w_j=w_(j+1) -> color(f_j)=color(f_(j+1)).         (1508)
```

No outside endpoint can receive three of the four chosen exits.  Indeed,
any three vertices of a four-cycle induce a path of length two.  Applying
(1508) along that path makes all three exit colors equal at the common
endpoint, contrary to the exterior component-color degree cap two.  Hence

```text
#{w_0,w_1,w_2,w_3}>=2.                            (1509)
```

When an adjacent pair collides, its two exits have the same exterior color
but different roots, the latter because every root class is a matching.
An opposite pair may collide with different colors: its two-edge ear has
length four rather than being shorter, so minimality alone gives no
constraint.  Thus the complete valid small-length split is now

```text
ell=3: exact root cut (1,1,1,3,3), endpoint merging open;
ell=4: at least two chosen-exit endpoints, with adjacent merging typed;
ell>=5: at least ceil(ell/2) chosen-exit endpoints, all merging typed.
                                                               (1510)
```

This uses only shortest-cycle coloring and the genuine root/color degree
caps.  It does not assume that the target-pair shadow graph is itself
four-cycle-free.

## 424. Root capacity gives the triangle genuine three-point expansion

The exact triangle cut vector (1501) still forces vertex expansion, but
through matching capacity rather than shadow four-cycle-freeness.  Let
`W_partial` be the set of outside endpoints of all nine boundary edges of
the triangle.  Each of the two roots absent from the cycle has boundary
coordinate three.  Its three boundary edges belong to one matching and
therefore have three distinct outside endpoints.  Hence

```text
|W_partial|>=3.                                    (1511)
```

More precisely, every collision bundle at an outside endpoint contains
distinct roots, because each `G_i` has degree at most one there, and each
exterior color occurs at most twice in that bundle.  Thus the valid local
capacity statement is

```text
same outside endpoint -> all incident boundary roots are distinct;
same outside endpoint and same exterior color -> multiplicity at most 2.
                                                               (1512)
```

There is also a defect-sector consequence when the triangle is an entire
component of `G_sh[O_5]`.  Then every one of its boundary endpoints lies
in `S`.  For either root `i` absent from the triangle, those three matched
endpoints are distinct from the hole set `H_i subseteq S`.  Consequently

```text
V(C_Q)=V(Q), ell=3
 -> s>=3,
 -> s>=|H_i|+3=2delta_i+2
    for each of the two roots absent from Q.       (1513)
```

So the triangular exception cannot collapse to fewer than three outside
companions, and an isolated full-root triangle consumes three nonhole
vertices of the defect sector in each unused root matching.  This is
weaker than the retracted nine-neighbor claim but is exact under the true
shadow model and interfaces directly with the bounded hole budgets.

## 425. Properly-colored-cycle-free full-root components have bounded mass

The defect cut bounds not just odd components but every component that
contains no holonomy.  Let `C` be a connected component of
`G_sh[O_5]`, put `n_C:=|C|`, `e_C:=|E(C)|`, and let `b_C` be its edge
boundary into `S`.  Every vertex of `C` has shadow degree five, so

```text
b_C=5n_C-2e_C.                                    (1514)
```

If `n_C>=2` and `C` has no properly colored cycle, the sharpened Yeo bound
gives `e_C<=2n_C-3`.  A singleton has `e_C=0`.  Consequently

```text
C PC-cycle-free, n_C>=2 -> b_C>=n_C+6;
C a singleton                 -> b_C=5=n_C+4.      (1515)
```

Let `T` be the union of all PC-cycle-free components, with `k_1` singleton
components and `k_2` nontrivial components.  Their boundaries are disjoint
subsets of the full `O_5`--`S` cut.  Summing (1515), then using the exact
cut identity (1478), gives

```text
|T|+4k_1+6k_2
 <=sum_(C subset T)b_C
 <=5s-(2Delta-5)-2|E(G_sh[S])|,

|T|<=8Delta-20<=180.                              (1516)
```

For the last inequality, use `s<=2Delta-5` from (1457) and `Delta<=25`.
Thus the complementary union of full-root components which do contain a
properly colored cycle has vertex mass at least

```text
|O_5|-|T|
 >=2q+10-10Delta
 >=2q-240.                                        (1517)
```

Hence the large binary branch does not merely contain one clean holonomy:
all but at most 180 full-root vertices lie in holonomy-containing
components, uniformly in `q`.  Any remaining contradiction may therefore
work componentwise on an almost-spanning sector; PC-cycle-free debris is
entirely chargeable to the constant hole boundary.

## 426. A closed full-root component is five-one-factor holonomy

There is an exact description of components which spend none of the defect
cut.  Let `C` be a connected component of `G_sh[O_5]` with no edge to
`S`.  Then its rootwise boundary coordinates all vanish:

```text
b_i(C)=|partial_(G_i)C|=0       for i=0,...,4.     (1518)
```

Every vertex of `C` has exactly one incident edge from each root matching.
Since none leaves `C`, each restriction `G_i[C]` is a perfect matching.
In particular

```text
|C| is even,
G_sh[C]=G_0[C] disjoint_union ... disjoint_union G_4[C]
is a connected 5-regular graph with five named one-factors.       (1519)
```

The shadow graph is simple, so such a component has `|C|>=6`.  Its edge
count is

```text
|E(C)|=5|C|/2>2|C|-3.                            (1520)
```

The sharpened properly-colored-cycle theorem therefore forces a simple PC
cycle in `C`.  Equivalently,

```text
C has no PC holonomy -> C has a nonempty boundary to S;
C has zero boundary  -> C is an even five-one-factor holonomy reservoir.
                                                               (1521)
```

Thus closed full-root components are not part of the bounded debris in
Section 425.  They retain all five root actions internally and necessarily
carry holonomy; only components that pay into the constant defect sector
can be properly-colored-cycle-free.

## 427. Full-root holonomy has linear disjoint packing mass

The induced-core surplus also survives passage from one cycle to a maximal
packing.  Put

```text
H:=G_sh[O_5],       n:=|O_5|,
R_5:=q-7+Delta-3s.
```

By (1465), `|E(H)|-(2n-3)>=R_5`.  Let `X subseteq O_5` meet every properly
colored cycle of `H`.  If at least two vertices remain, then `H-X` is
PC-cycle-free, and deleting `X` removes at most `5|X|` edges.  The
sharpened Yeo bound therefore gives

```text
|E(H)|-5|X| <= 2(n-|X|)-3,
3|X| >= |E(H)|-(2n-3) >= R_5.                    (1522)
```

If fewer than two vertices remain, the same cardinality conclusion is
automatic in the binary range `q>=128`: then `|X|>=n-1`, while the
five-regular degree ceiling gives
`R_5<=|E(H)|-(2n-3)<=n/2+3`.  Thus every vertex transversal of the clean
holonomies satisfies

```text
|X|>=ceil(R_5/3)>=ceil((q-117)/3).                (1523)
```

Now take a maximal family of pairwise vertex-disjoint properly colored
cycles in `H`.  The union of their vertex sets meets every properly colored
cycle, since a disjoint one could otherwise be added.  Applying (1523)
shows that

```text
some vertex-disjoint family of clean holonomies covers at least
ceil(R_5/3) full-root vertices.                   (1524)
```

There is a parallel edge statement.  The union `F` of a maximal family of
pairwise edge-disjoint properly colored cycles is an edge transversal.
Deleting it leaves a PC-cycle-free graph, so directly comparing with the
same ceiling yields

```text
|F|>=R_5.
```

Because the chosen cycles are edge-disjoint, `|F|` is their total cycle
length.  Hence

```text
some edge-disjoint family of clean holonomies has total length
at least R_5>=q-117.                              (1525)
```

Consequently the `q>=128` branch cannot concentrate holonomy in one
exceptional circuit or a bounded vertex set.  It carries linear disjoint
cycle mass entirely inside the no-hole, all-five-root sector, in addition
to the almost-spanning component mass of Section 425.

## 428. Only boundedly many full-root components meet the hole sector

The simultaneous cut parity also bounds the number of open components,
independently of their orders.  Call a connected component `C` of
`G_sh[O_5]` open when it has a nonempty boundary to `S`, and write
`b(C):=sum_i b_i(C)`.  By (1470), all five root-boundary coordinates have
parity `|C|`.  Hence

```text
C open and |C| even -> b(C)>=2;
|C| odd             -> b_i(C)>=1 for every i,
                       so b(C)>=5.                 (1526)
```

Indeed in the even case at least one coordinate is nonzero and every
coordinate is even.  Let `n_even^+` count the open even components and
let `n_odd` count the odd components.  Component boundaries partition the
full `O_5`--`S` cut, so (1478) and (1526) give

```text
2n_even^+ + 5n_odd
 <=5s-(2Delta-5)-2|E(G_sh[S])|
 <=8Delta-20
 <=180.                                             (1527)
```

Consequently

```text
n_even^+ + n_odd<=90,       n_odd<=36.             (1528)
```

Every other full-root component is closed and therefore has the even
five-one-factor structure and forced holonomy of Section 426.  Thus the
entire induced full-root graph splits into at most ninety components that
interact with the bounded hole sector, together with any number of closed
even holonomy reservoirs.  In particular all componentwise irregularity
visible from `S` is confined to a constant-size component census, not just
to a constant number of missing vertices.

## 429. The full-root cycle space has a linear tag-even kernel

The abundance results can be reconnected to the literal selected tags.
Put `H:=G_sh[O_5]`.  Every edge `y` of `H` has two residual endpoints, so
if its root is `i`, its selected tag set is exactly `D(y)=T_i` by (1245).
Define the edgewise linear map

```text
tau:F_2^{E(H)} -> F_2^Z,
tau(1_y):=[T_i] when y lies in G_i.                (1529)
```

The five vectors `[T_i]` are a basis by (1324).  Therefore, for every
binary edge chain `F`,

```text
tau(F)=0
 iff |F intersect E(G_i)| is even for every root i
 iff every selected tag column occurs evenly across F.           (1530)
```

Now restrict `tau` to the binary cycle space `Z_1(H)`.  Its kernel consists
of Eulerian shadow chains with complete rootwise and selected-column tag
cancellation.  The dimension of the ambient cycle space is already linear.
Using (1464), `|O_5|=2q-15-s`, and at least one component,

```text
dim Z_1(H)
 =|E(H)|-|O_5|+components(H)
 >=3q-24+Delta-4s
 >=3q-4-7Delta
 >=3q-179.                                        (1531)
```

The map has rank at most five, so

```text
dim ker(tau|Z_1(H))>=3q-184,
and in particular is at least 200 when q=128.      (1532)
```

Thus the clean full-root sector contains not only linearly many holonomy
edges and vertices, but a linear-dimensional reservoir of Eulerian chains
whose literal three-tags-per-edge cancel in every selected column and
whose five root frequencies are all even.  This does not yet ensure that
one kernel element is itself a properly colored simple cycle; it isolates
that precise remaining selection problem instead of treating tag
cancellation as scarce.

## 430. Avoidance and disjoint holonomy abundance hold simultaneously

The avoidance weights of Section 419 can be subtracted before applying the
packing argument of Section 427.  Let `A` be a set of exterior source
colors and put

```text
w(A):=sum_(h in A)(10-k_h),
H_A:=H minus {edges whose source color lies in A}.
```

By (1493), deleting these colors removes at most `w(A)` edges.  Hence the
surplus of `H_A` over the PC-cycle-free ceiling is at least

```text
R_A:=R_5-w(A).                                    (1533)
```

Assume `R_A>0`.  If a vertex set `X` meets every properly colored cycle of
`H_A`, then deleting `X` costs at most `5|X|` edges while the Yeo ceiling
drops by `2|X|`.  Exactly as in (1522)--(1523),

```text
|X|>=ceil(R_A/3).                                 (1534)
```

The union of a maximal vertex-disjoint PC-cycle family in `H_A` is such a
transversal, while the union of a maximal edge-disjoint family is an edge
transversal.  Therefore there are source-`A`-avoiding clean holonomies with

```text
vertex-disjoint covered mass >=ceil(R_A/3),
edge-disjoint total length   >=R_A.                (1535)
```

There is an identical payer-layer statement.  If `P` is a set of payer
layers, at most `10|P|` edges of `H` have their canonical payer in `P`, by
(1494).  Replacing `R_A` in (1534)--(1535) by

```text
R_P:=R_5-10|P|                                    (1536)
```

gives disjoint clean holonomy families avoiding every payer layer in `P`
whenever `R_P>0`.

The two distinguished source-color consequences are explicit.  The color
`d` has weight ten, and the strict-export support `Gamma` has weight at
most forty-five.  Since `R_5>=q-117`,

```text
binary q>=128:
  d-free vertex-disjoint clean holonomies cover at least
  ceil((q-127)/3) vertices,
  and a d-free edge-disjoint family has total length at least q-127;

binary q>=256:
  Gamma-free vertex-disjoint clean holonomies cover at least
  ceil((q-162)/3) vertices,
  and a Gamma-free edge-disjoint family has total length at least q-162.
                                                               (1537)
```

Thus avoidance is not paid for by collapsing back to one exceptional
cycle.  Even after every distinguished source color, or any fixed set of
payer layers, is removed, the no-hole five-root sector retains linear
disjoint properly colored holonomy mass.
