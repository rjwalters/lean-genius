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
