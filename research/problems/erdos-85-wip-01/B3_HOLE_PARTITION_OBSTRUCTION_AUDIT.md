# B.3 exceptional-hole partition obstruction audit

## Scope

This note records the current boundary of the `q = 9` three-high second-profile
residual/core obstruction.  It is not a nonexistence proof.  The SAT results
below are external exploratory evidence; no UNSAT certificate is claimed.

Let `Q` be the `47 x 24` incidence matrix of the ordinary `B0` centers with
the unmarked `B1` core, let `K` be the cubic core adjacency matrix, and let
`A` be the residual adjacency matrix on the 47 centers.  An exceptional
triple center `h` has residual degree six and exactly three triple-center
neighbors.  The already-proved trace-zero law and the `B0` Gram law imply
that the six `Q`-blocks at those neighbors are pairwise disjoint and avoid
`supp(Q_h K)`.  Their sizes are three triples and three pairs, so equality in
the 24-point capacity bound requires

```text
U1 \ supp(Q_h K)
  = (three disjoint rainbow triples) disjoint-union
    (three disjoint marked-support pairs).
```

Colorwise, the pairs must consist of one of each missing-color type, using
two points of each color.  The triples must then give a three-edge matching
on the remaining `3 x 3 x 3` points.

## Exact computational frontier

`q9_b0_residual_defect_sat.py --audit-hole-partitions-seeds N` counts these
local partitions in fixed outer witnesses.  In ten sampled witnesses per
branch, every witness had at least one exceptional hole with count zero.
Branch 4 also produced a valid outer witness with a count-one hole, so a
theorem excluding every hole separately is false.

The seed-free mode keeps the unrestricted outer `Q,K` design and only the
residual edges incident to exceptional holes.  It omits all other residual
rows and defect semantics:

```text
python3 q9_b0_residual_defect_sat.py \
  --branch 3 --hole-partition-only --kissat --timeout-seconds 180
```

This produced `p cnf 138975 837650` and `UNKNOWN`.  Requiring only one of the
two branch-3 holes via `--hole-partition-at-least 1` produced
`p cnf 138976 837618` and was also `UNKNOWN` after 180 seconds.  Thus neither
the coupled conjecture nor a branch-3 per-hole strengthening is established.

## Reductions that do not close

1. **Capacity alone.**  For a row `t`, disjointness gives
   `3 n3(t) + 2 n2(t) <= 24 - |supp(Q_t K)|`.  This is just the degree bound
   on ordinary rows.  At a hole it is equality and yields the partition
   above, but no contradiction.
2. **Parallel-class role counts.**  They admit an abstract partition: take
   three diagonal triples on indices `3,4,5` and the pairs
   `(c0:6,c1:6)`, `(c0:7,c2:6)`, `(c1:7,c2:7)` outside a `3+3+3` support.
   Hence the Latin/parallel-class layer alone is insufficient.
3. **Binary row space.**  Exact partition implies
   `(A Q)_h = 1 + (Q K)_h` over `F2`.  The aggregate hole targets lie in the
   eligible block-row span in sampled witnesses, so parity gives no terminal.
4. **Scalar pair-cover contractions.**  The exact outer cover is
   `K^2 + Q^T Q + M + D = C + 8 I`, where `M` is the marked-pair graph,
   `D` the core defect graph, and `C` the complete tripartite color graph.
   Substituting the partition equation and taking row sums or inner products
   recovers existing column laws or tautologies.
5. **Per-hole Hall or determinant vanishing.**  False in branch 4: one valid
   outer witness has a full local transversal.  Its partition parity is one,
   so even the coupled sum of the corresponding determinants need not vanish.
6. **Forced puncture-type transport.**  False in sampled compatible holes.
   Triple-neighbor role patterns vary, and a compatible partition need not
   contain another exceptional hole.

## Remaining conjecture

The only surviving statement from this mechanism is location-sensitive:

> In every branch-3 or branch-4 outer design satisfying the exact zero-slack
> pair cover, not all exceptional holes admit the complement partition above.

Equivalently, the high-degree product of the local `3 x 3` matching-existence
indicators is zero.  None of the capacity, parity, determinant-sum, role-count,
or scalar matrix identities above implies this.  Progress requires a new
entrywise coupling among different holes or a certified solution of the
seed-free query; repeating fixed-outer residual SAT does not address the
uniform statement.

## Rectangular collision parity

There is a parameter-free parity invariant which survives the failed scalar
contractions above.  It was identified by transferring the collision-table
argument from the regular component lane.  Let `Q` be any zero-one matrix,
let `K` be any symmetric loopless zero-one matrix, and put

```text
R = Q K Q^T.
```

If `S_x` is the support of row `x` of `Q`, then

```text
R_xx = 2 |E_K(S_x)|.                                           (1)
```

Since `R` is symmetric, every off-diagonal summand in the ordered collision
count occurs twice.  On the diagonal,
`binom(2e,2) = e(2e-1) = e (mod 2)`.  Therefore

```text
sum_(x,y) binom(R_xy,2)
  = sum_x |E_K(S_x)|                         (mod 2).           (2)
```

No entry bound on `R` is needed for (2).  If the application separately
forces `R_xy <= 2`, its left side is exactly the parity of the ordered cells
with two routes.

For disjoint vertex blocks `T,U` in a C4-free graph, take `Q` to be the
`T x U` adjacency block and `K` the adjacency matrix on `U`.  Then the right
side of (2) counts triangles having one vertex in `T` and two in `U`.
Moreover, if `x,y in T` are adjacent, the two cross fibers are anticomplete
by `c4Free_internalEdge_crossBlock_fibers_anticomplete`, so

```text
A_T(x,y)=1  implies  R_xy=0.                                  (3)
```

Thus (2)--(3) give a joint parity invariant of precisely the residual
adjacency and the zero-support graph of `Q K Q^T`; unlike the earlier trace
zero, it sees double routes.  In the B.3 specialization, its right side is
the parity of the `B0-B1-B1` triangles with the B1 vertices in the unmarked
core.

This does not yet close the hole-partition conjecture.  The remaining
consumer must determine that triangle parity (or force the parity of the
double-route cells) from the colored row ledger.  Connectivity of `D0-x`
does not by itself enter (2); its prospective role is to prevent the
collision support from splitting into independently parity-balanced pieces.

### Core-edge contraction

The exact pair-cover identity makes the missing parity more concrete.  In
the B.3 notation,

```text
K^2 + Q^T Q + M + D = C + 8 I,
```

The graph `K` has twelve same-color root-triangle matching edges and 24
cross-color edges;
only the latter are edges of the complete tripartite color graph `C`.
Contracting this identity over those 24 unordered cross-color `K`-edges gives

```text
sum_{uv in E(K)} (Q^T Q)_uv
  = 24 - 3 t(K) - |E(K) intersect E(M)| - |E(K) intersect E(D)|,  (4)
```

where every edge set in (4) is implicitly restricted to the cross-color
sector.  Indeed, the `K^2` contraction is `3 t(K)`: a K-triangle is rainbow
(two same-color vertices would share both their high root and the third
triangle vertex), and contributes one common neighbor on each of its three
edges.  The left side of (4) is exactly the number of `B0-B1-B1` triangles
counted on the right side of (2).  Thus its parity is

```text
t(K) + |E(K) intersect E(M)| + |E(K) intersect E(D)|  (mod 2). (5)
```

This is also the four-way common-neighbor partition of the cubic-core edges:
completion inside the unmarked core, completion through an ordinary `B0`
row, completion in the marked-pair layer, or no completion (a defect edge).
Consequently the first missing input can be stated sharply: the existing
colored ledger must determine the parity of the three terms in (5), jointly
or separately.  Their uncolored sum merely recovers the 24-edge partition
and supplies no contradiction by itself.

### Pointwise sharpening and parity probe

There is one exact pointwise sharpening.  The graph induced on the
neighborhood of any vertex in a C4-free graph has maximum degree at most
one: two incident local edges would make their two outer endpoints share
both the root and the middle vertex.  Every B.3 row support has size two or
three, so

```text
|E_K(S_x)| is either zero or one.                               (6)
```

Consequently the right side of (2) is literally the parity of the number of
ordinary B0 rows carrying a B0--U1--U1 triangle, not merely a weighted edge
count.

The mandatory abstract-satisfiability probe rules out an outer-ledger-only
parity theorem.  Using `make_outer_seed` from
`q9_b0_residual_defect_sat.py`, three independently seeded valid outer
designs in each branch gave total internal-row K-edge counts

```text
branch 3: 11, 14, 18  (parities 1,0,0),
branch 4: 12, 15, 17  (parities 0,1,1).
```

Thus both parities occur in both branches before the residual graph and
defect semantics are imposed.  This is a failure certificate for the claim
that the colored `Q,K` row ledger alone fixes (2); it is not evidence that an
actual graph can realize either parity.  Any terminal consumer must use the
residual adjacency, defect connectivity, or an equally strong coupling.

### The unmasked local label sum is tautological

The most direct attempt to bring the residual graph into (6) still loses its
adjacency information.  Over `F2`, let

```text
q(s) = |E_K(supp(s))|,
b(s,t) = s K t^T.
```

Then `q(s+t)=q(s)+q(t)+b(s,t)`.  At an exact exceptional hole `h`, the
partition equation is

```text
sum_{u in N_A(h)} Q_u = 1 + Q_h K.
```

Polarizing therefore expresses the sum of the row labels `q(Q_u)`, plus all
cross-block terms `b(Q_u,Q_v)`, as `q(1+Q_hK)`.  But the neighbor blocks
partition `W = U1 \ supp(Q_hK)`, so the entire left side is simply
`|E_K(W)|`.  Cubic handshaking gives

```text
|E_K(W)| = q(supp(Q_hK)) + |supp(Q_hK)|  (mod 2),
```

which is exactly the polarized right side.  Hence the unmasked neighbor-label
sum is another form of cubic handshaking.  A non-tautological consumer must
retain a mask on the cross-block terms, for example one supplied by residual
adjacency or defect reciprocity.

### Incidence-masked three-way partition

There is a pointwise identity that retains both masks.  For an ordinary B0
row `t`, put `S_t = N_G(t) intersect U1` and `l_t=|E_K(S_t)|`.  Restrict the
mixed three-way resolution to the incidence cells `b in S_t`.  Such a cell
is resolved in exactly one of three ways:

1. by a core common neighbor in `U1`;
2. by a residual B0 common neighbor;
3. by the defect relation, equivalently the original edge `tb` is
   triangle-free.

Because the graph induced on `S_t` is a matching, the first class has size
exactly `2 l_t`.  If `r_t` and `d_t` denote the sizes of the second and third
classes, respectively, then

```text
|S_t| = 2 l_t + r_t + d_t.                                  (7)
```

Every unmarked B1 column has five B0 neighbors, so
`sum_t |S_t| = 24*5 = 120`.  Writing `L=sum_t l_t`, `R=sum_t r_t`, and
`Z=sum_t d_t`, summing (7) gives

```text
2 L = 120 - R - Z.                                           (8)
```

Thus the collision parity is the half-parity of the combined
residual-resolved and triangle-free incidence mass.  Unlike the unmasked
polarization, (7)--(8) preserve exactly the residual/defect distinction
needed by a prospective connectivity consumer.  They do not yet determine
that half-parity; a mod-four constraint on `R+Z` is still required.
