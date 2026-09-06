# A triangle-free internal control satisfying the new parity obstruction

Node: A.5.3 / A-REG-NONBIP / NONBIP-MIXED / weight three.

Status: explicit q16 countermodel to an exclusion using only the internal
conditions listed below. This is not an ambient graph, a full small-shore
Gram realization, or a Lean theorem. It demonstrates that the odd-code
exclusion of the interval defect cannot be extended to all triangle-free
defects merely by adding commutation, cubic degree, and the internal cap.

## Construction

Write the points as `(x,i)` with `x` in F2^4, encoded by integers0 through15,
and `i` in `{0,1,2}`. Addition of base coordinates is bitwise XOR.
Let the base graph have connection set

```text
S={1,2,4,8,15}.
```

This is the 5-regular folded5-cube, also called the Clebsch graph; see the
[DistanceRegular.org entry](https://www.math.mun.ca/distanceregular/graphs/clebsch.html).
The explicit definition fixes which of the two complementary graphs
sometimes carrying that name is meant. No classification theorem is used.
Define D by replacing each base vertex by three independent points and
joining all nine pairs between adjacent base vertices:

```text
D((x,i),(y,j)) iff x XOR y belongs to S.
```

Define H with generators3,5,9 and the three different transpositions of
`{0,1,2}`:

```text
sigma_3=(0 1), sigma_5=(0 2), sigma_9=(1 2),
N_H(x,i)={(x XOR s, sigma_s(i)): s in {3,5,9}}.
```

## Exact internal properties

D is simple and15-regular on48=3q points. The four unit vectors in S give
connectivity. No sum of two distinct elements of S lies in S, so D is
triangle-free. Base vertices `0,1,3,7,15` give an induced5-cycle, and taking
fiber coordinate0 gives one in D. Thus D is nonbipartite.

H is simple, symmetric, and cubic: each generator and each corresponding
fiber permutation is an involution, and the three base neighbors differ.
Each generator translation commutes with the base adjacency of D; each
fiber permutation commutes with the all-ones3-by-3 matrix. Therefore HD=DH.
None of3,5,9 belongs to S, so H and D have disjoint edge sets. In particular
`diag(HD)=0`, satisfying the even-overlap condition that excluded the entire
interval-defect family.

For two different H generators s,t, their sum is respectively6,10,12.
These three sums are distinct and outside S. At a fixed starting fiber
coordinate i, the two orders of the generators end at
`sigma_s sigma_t(i)` and `sigma_t sigma_s(i)`. Products of distinct
transpositions are opposite3-cycles, which take i to different points.
Consequently every off-diagonal entry of H^2 is at most1, and every entry
on a D-edge is0. Thus H is C4-free and its neighborhoods across D-edges
are disjoint.

Exact binary elimination gives `rank_F2(D+I)=38`, which is even. Hence the
new closed-neighborhood rank condition is also satisfied. All these
properties hold simultaneously for these same H,D matrices.

## What is missing

The required incidence matrix B would have48 rows,208 columns, row sum13,
column sum3, and

```text
H^2+BB^T=15I+J-D.
```

Its off-diagonal support is the26-regular graph
`L=J-I-D-(H^2-3I)`. A triangle decomposition of L would provide such a B;
this document does not assert one. In fiber blocks, L has K3 within each
base fiber, matching I3 blocks at base differences6,10,12, and full K3,3
blocks at the other seven nonzero differences outside S.

Neither the shared cross equation `HB+BT=J` nor the exterior Gram has been
solved. No connected exterior defect, regular ambient graph, or full branch
counterexample follows. The point of the control is to stop an internal-only
extension of the successful interval-defect argument; subsequent work must
use constraints beyond those verified here.

Run the standard-library checker:

```sh
python3 research/problems/erdos-85-wip-01/check_weight_three_clebsch_internal.py
```
