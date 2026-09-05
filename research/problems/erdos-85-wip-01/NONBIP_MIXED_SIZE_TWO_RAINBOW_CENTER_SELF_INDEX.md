# Size-two carrier: rainbow-center self-index

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact q-generic incidence consequence; no terminal claimed.

## Setup

Use the size-two defect triangle `Q={c_0,c_1,c_2}`, exterior carrier fibers
`S_i`, and rainbow-star count `w` from
`NONBIP_MIXED_SIZE_TWO_DIAGONAL_GRAM_PACKING.md`.  The component weights are

```text
m=2,       n=q-2,
```

so `H_C` has degree two and the cross block `B` has row degree `n` and
column degree two.  A rainbow center is a label `v in F` with exactly one
`H_F`-neighbor in every `S_i`.

## The six forbidden internal labels

Put

```text
W = union_i N_H_C(c_i),       X=C\\W.
```

The three `H_C`-neighborhoods are pairwise disjoint.  A common point of
`N_H_C(c_i)` and `N_H_C(c_j)` would be a common ambient neighbor of the
defect pair `c_i,c_j`, contradicting its zero common-neighbor count.  Since
each neighborhood has size two,

```text
|W|=6,       |X|=2q-6=2(n-1).                            (1)
```

Now let `v` be a rainbow center.  Evaluate

```text
H_C B+B H_F=J
```

at `(c_i,v)`.  The second term is `deg_H_F(v,S_i)=1`, so the first term is
zero.  It counts the `B`-neighbors of `v` which lie in `N_H_C(c_i)`.
Therefore this count vanishes for every `i`, and

```text
N_B(v) subset X.                                         (2)
```

Thus the center of every partial-Latin entry is not an arbitrary exterior
label: its self-indexed two-point selector is an edge entirely inside the
fixed `2(n-1)`-set `X`.

## Exact capacity ledger

Every point of `X` has cross degree `n`, so the total `B`-incidence capacity
from `X` is

```text
|X|n=2n(n-1).
```

The `w` rainbow centers use exactly two of these incidences each by (2).
Consequently the non-rainbow labels use exactly

```text
2n(n-1)-2w                                                 (3)
```

incidences from `X`.  Writing

```text
gamma_ij=|U_i intersect U_j|,
u=|U_0 intersect U_1 intersect U_2|,
```

the banked formula

```text
w=n(n-4)+gamma_01+gamma_02+gamma_12-u
```

turns (3) into

```text
6n-2(gamma_01+gamma_02+gamma_12)+2u <= 6n.              (4)
```

All `6n` incidences from the six rows in `W` go to non-rainbow labels,
because (2) excludes every rainbow center.  Hence the exterior labels split
their two-point selectors as follows:

```text
rainbow centers:      exactly 2w incidences, all from X;
non-rainbow labels:   exactly 6n incidences from W,
                      and the quantity (4) from X.       (5)
```

In particular, only `O(n)` of the `X`-incidence capacity remains outside
the quadratically large rainbow-center family.

## The selector graph leaves only twelve internal exceptions

Distinct columns of `B` give distinct two-subsets of `C`: equal columns
would make their two exterior labels common neighbors of the same pair in
`C`, producing a C4.  Thus all exterior labels are the edges of a simple
`n`-regular selector graph `L` on `C`, with

```text
|E(L)|=|F|=qn=n(n+2).                                    (6)
```

Rainbow labels are edges of `L[X]`.  From the exact formula for `w`, the
total number of non-rainbow selector edges is

```text
|E(L)|-w=6n-(gamma_01+gamma_02+gamma_12)+u.              (7)
```

Let `e_W=|E(L[W])|`.  The degree sum on the six vertices of `W` is `6n`, so
the number of selector edges with at least one endpoint in `W` is

```text
6n-e_W.
```

All these edges are non-rainbow by (2).  Subtracting them from (7) shows
that the non-rainbow selector edges lying entirely in `X` number exactly

```text
e_W-(gamma_01+gamma_02+gamma_12)+u.                      (8)
```

Write `W_i=N_H_C(c_i)`, so `W` is the disjoint union of three two-sets.
Each `W_i` is independent in `L`: its two vertices already share `c_i` as
an ambient neighbor in `C`, and an exterior selector edge between them would
supply a second common neighbor.  Hence `L[W]` has edges only across the
three `2 x 2` blocks and

```text
e_W <= 12,
0 <= |E(L[X]) \\ {rainbow edges}| <= 12.                 (9)
```

The non-rainbow part inside the large set `X` is therefore bounded by an
absolute constant, independent of `q`.  All remaining non-rainbow selector
edges touch the fixed six-vertex set `W`.

## Disposition

This is the first constraint which uses the rainbow centers as the actual
self-indexed exterior labels rather than merely as entries of a partial
Latin square.  It concentrates all their selector edges inside `X` and
nearly saturates the `B`-capacity there.

It is not yet a contradiction.  But the unresolved selector freedom has
collapsed to the finite graph `L[W]` and at most twelve exceptional edges in
`L[X]`.  A terminal must show that none of these constant-sized exception
patterns is compatible with the companion/owner labels and the three
near-saturated partial-Latin projections.  The raw incidence capacity alone
still has nonnegative slack.
