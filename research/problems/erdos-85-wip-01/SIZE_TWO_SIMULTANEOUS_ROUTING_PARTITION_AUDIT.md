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

Hence

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
