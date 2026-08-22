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
