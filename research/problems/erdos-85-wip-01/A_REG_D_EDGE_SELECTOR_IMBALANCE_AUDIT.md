# A-REG defect-edge selector-pair imbalance audit

Status: falsified first lemma from divergence round 3, 22 August 2026.

## Proposed placement invariant

For an oriented defect edge `uv`, and every vertex `z` that is nondefect to
both endpoints and lies outside `N(u) union N(v)`, let

```text
a = the unique point in N(z) intersect N(u),
b = the unique point in N(z) intersect N(v).
```

The pairs `(a,b)` form a bipartite multigraph `M_uv` on `N(u) x N(v)`.
Because the selectors are reciprocal, a plausible first lemma was that the
row/column imbalance of `M_uv` is determined by the signed boundary of
`T=A intersect D`.  Summing such imbalances around a defect cycle would then
give a nonlinear placement holonomy unavailable to scalar owner budgets.

## Exact q=4 control falsification

`q4_defect_edge_selector_pair_audit.py` evaluates every oriented defect edge
in the banked fixed-point-free q=4 control.  There are four exact local
pattern classes (reported by endpoint `T` status, sorted `(M-degree,
T-neighbor-status)` rows/columns, and total edge count):

```text
16 x (uv not in T; rows 1,1,1,1; columns 1,1,1,1; |M|=4)
 8 x (uv not in T; rows 1,1,2,2; columns 1,1,2,2; |M|=6)
16 x (uv in T;     rows 0_T,1,2,3_T; same columns; |M|=6)
 8 x (uv not in T; rows 1,1,2_T,2_T; same columns; |M|=6)
```

The proposed boundary determination fails more strongly than these four
classes suggest.  Condition simultaneously on

- whether `uv` lies in `T`;
- whether the row point `a` equals `v`;
- whether `ua` lies in `T`;
- whether `av` lies in `A` or `D`; and
- the number of common neighbors of `a,v`.

There are row points with identical values of all these data but different
`M_uv` degrees (1 versus 2).  When `uv` itself lies in `T`, the two
`T`-neighbors of `u` have degrees 0 and 3: the zero row is the endpoint `v`,
while the other broken-incidence neighbor has degree three.  Thus neither
`T` membership nor its signed local boundary determines imbalance.

The script also checks that the sorted row- and column-degree profiles agree
in this control.  That equality is compatible with reversing the oriented
edge, but it supplies only a multiset balance and no canonical pointwise
transport.

## Disposition

The divergence-round first lemma is false.  The correction term must retain
higher-order placement information: which outside vertices reuse which
unique common-neighbor centers, not merely the `A/D/T` status around `uv`.
Any viable holonomy must couple those placements globally across several
defect edges.  A signed `T`-boundary or local degree formula is insufficient.

