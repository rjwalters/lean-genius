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

There is a pointwise converse, which gives the cleanest form of the
selector restriction. For every exterior label `v` and every `i`, the
same block equation gives

```text
deg_H_F(v,S_i)=1-|N_B(v) intersect W_i|.                  (2a)
```

Its nonnegative left side forces the intersection on the right to have
size at most one. Thus `U_i` is exactly the set of selector edges touching
`W_i`, and `T_i` is the set avoiding `W_i`. A two-endpoint edge cannot
touch all three disjoint `W_i`, so `u=0`; the intersection `U_i intersect
U_j` consists exactly of the selector edges across `W_i x W_j`.
Consequently `e_W=sum gamma_ij` and the rainbow edges are exactly `L[X]`.
The longer matrix derivation (10d)--(10h) below independently recovers
these identities. The pointwise observation is due to Sol3's selector-star
synthesis.

## Every center edge avoids its companion triple

Let a rainbow center `v` have leaf `f_i in S_i`, and write the leaf selector
as

```text
N_B(f_i)={c_i,r_i}.
```

The three companions `r_0,r_1,r_2` are pairwise distinct.  If `r_i=r_j`,
then the two distinct leaves `f_i,f_j` would share both `r_i` and their
rainbow center `v` as ambient common neighbors, producing a C4.  No `r_i`
lies in `Q`, since that would put `f_i` in a second, disjoint carrier fiber.
Thus the six labels

```text
c_0,c_1,c_2,r_0,r_1,r_2
```

are distinct.

Write the center selector as `N_B(v)={a,b}`.  Evaluate
`H_C B+B H_F=J` at `(a,f_i)`.  The `B H_F` term already contains the witness
`v`, because `B(a,v)=H_F(v,f_i)=1`; the full entry is one, so this witness is
unique and the `H_C B` term vanishes.  Since the two `B`-neighbors of `f_i`
are `c_i,r_i`,

```text
not H_C(a,c_i),       not H_C(a,r_i).
```

The same argument applies to `b` and to all three leaves.  Consequently the
selector edge of every rainbow center is `H_C`-anticomplete to its entire
six-label triangle/companion set:

```text
{a,b} x {c_0,c_1,c_2,r_0,r_1,r_2} contains no H_C edge. (3)
```

The avoidance of the triangle labels recovers (2); avoidance of the three
center-dependent companions is new owner-labelled information.

## Exact capacity ledger

Every point of `X` has cross degree `n`, so the total `B`-incidence capacity
from `X` is

```text
|X|n=2n(n-1).
```

The `w` rainbow centers use exactly two of these incidences each by (2).
Consequently the non-rainbow labels use exactly

```text
2n(n-1)-2w                                                 (4)
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

turns (4) into

```text
6n-2(gamma_01+gamma_02+gamma_12)+2u <= 6n.              (5)
```

All `6n` incidences from the six rows in `W` go to non-rainbow labels,
because (2) excludes every rainbow center.  Hence the exterior labels split
their two-point selectors as follows:

```text
rainbow centers:      exactly 2w incidences, all from X;
non-rainbow labels:   exactly 6n incidences from W,
                      and the quantity (5) from X.       (6)
```

In particular, only `O(n)` of the `X`-incidence capacity remains outside
the quadratically large rainbow-center family.

## The selector graph: from twelve possible exceptions to none

Distinct columns of `B` give distinct two-subsets of `C`: equal columns
would make their two exterior labels common neighbors of the same pair in
`C`, producing a C4.  Thus all exterior labels are the edges of a simple
`n`-regular selector graph `L` on `C`, with

```text
|E(L)|=|F|=qn=n(n+2).                                    (7)
```

Rainbow labels are edges of `L[X]`.  From the exact formula for `w`, the
total number of non-rainbow selector edges is

```text
|E(L)|-w=6n-(gamma_01+gamma_02+gamma_12)+u.              (8)
```

Let `e_W=|E(L[W])|`.  The degree sum on the six vertices of `W` is `6n`, so
the number of selector edges with at least one endpoint in `W` is

```text
6n-e_W.
```

All these edges are non-rainbow by (2).  Subtracting them from (8) shows
that the non-rainbow selector edges lying entirely in `X` number exactly

```text
e_W-(gamma_01+gamma_02+gamma_12)+u.                      (9)
```

Write `W_i=N_H_C(c_i)`, so `W` is the disjoint union of three two-sets.
Each `W_i` is independent in `L`: its two vertices already share `c_i` as
an ambient neighbor in `C`, and an exterior selector edge between them would
supply a second common neighbor.  Hence `L[W]` has edges only across the
three `2 x 2` blocks and

```text
e_W <= 12,
0 <= |E(L[X]) \\ {rainbow edges}| <= 12.                (10)
```

The non-rainbow part inside the large set `X` is therefore bounded by an
absolute constant, independent of `q`.  All remaining non-rainbow selector
edges touch the fixed six-vertex set `W`.

The first diagonal Gram block makes this finite freedom more explicit.  For
distinct `x,y in C`, its off-diagonal entry is

```text
1_{L(x,y)}+(H_C^2)_(x,y)=1-1_{D_C(x,y)}.               (10a)
```

Thus exactly one of the following holds: `xy` is a defect edge, `x,y` have
an internal ambient common neighbor, or `xy` is a selector edge.  In
particular, the endpoints of every rainbow selector edge are nonadjacent in
`D_C` and have no common `H_C`-neighbor, in addition to the six-label
anticompleteness in (3).

There are twelve unordered pairs across the three `2 x 2` blocks
`W_i x W_j`.  Let `d_W` count the `D_C`-edges among those pairs and let
`h_W` count the pairs having an internal ambient common neighbor.  Summing
(10a) on precisely those twelve pairs gives

```text
e_W=12-d_W-h_W.                                        (10b)
```

Consequently the exact exceptional count (9) is

```text
|E(L[X]) \\ {rainbow edges}|
  =12-d_W-h_W-(gamma_01+gamma_02+gamma_12)+u.           (10c)
```

So the apparent twelve-edge freedom is not arbitrary: every missing
exception is paid for by a defect edge, an internal distance-two pair, or
one of the already bounded hole intersections on the same fixed
six-vertex configuration.

In fact both remaining terms collapse.  First, the triple hole intersection
is empty.  If `v in U_0 intersect U_1 intersect U_2`, then
`deg_H_F(v,S_i)=0` for every `i`.  Evaluating `H_C B+B H_F=J` at `(c_i,v)`
would therefore give

```text
|N_B(v) intersect W_i|=1                 for i=0,1,2.
```

The sets `W_i` are pairwise disjoint, while the selector `N_B(v)` has only
two points.  This is impossible, so

```text
u=0.                                                       (10d)
```

For the finite `W` ledger, let `K=H_C^2-2I`; off the diagonal it is the
zero-one relation of having an internal ambient common neighbor.  It is
two-regular, and the diagonal Gram partition (10a) is the matrix identity

```text
L+D_C+K=J-I.
```

All three relations commute: `H_C` commutes with `D_C`, hence with `K`, and
the displayed partition then gives commutation with `L`.  For `i<j`, let
`d_ij` and `h_ij` count respectively the `D_C`- and `K`-edges across
`W_i x W_j`.  Since `c_i c_j` is a `D_C`-edge and hence not a `K`-edge,

```text
d_ij=(H_C D_C H_C)_(c_i,c_j)=2+(D_C K)_(c_i,c_j),
h_ij=(H_C K H_C)_(c_i,c_j)=(K^2)_(c_i,c_j).             (10e)
```

The companion-location identity also has an exact relation-algebra form.
Because `R_i=N_L(c_i)`, its three classes relative to `c_j` show that
`delta_ij=(L D_C)_(c_i,c_j)` and `p_ij=(L^2)_(c_i,c_j)`.
Equivalently, multiplying the partition by `L` or `K` gives

```text
gamma_ij=(L K)_(c_i,c_j)
        =2-(D_C K)_(c_i,c_j)-(K^2)_(c_i,c_j).           (10f)
```

Thus `d_ij+h_ij+gamma_ij=4`.  The four pairs in
`W_i x W_j` partition among `D_C,K,L`, so the number of `L`-edges in that
block is exactly `gamma_ij`.  Summing the three blocks yields

```text
e_W=gamma_01+gamma_02+gamma_12.                         (10g)
```

Substitution of (10d)--(10g) into (9) removes every internal exception:

```text
E(L[X]) = {rainbow selector edges}.                     (10h)
```

Every selector edge wholly inside `X` is therefore the center of a unique
rainbow triple; all non-rainbow selector edges touch `W`.

## Exact endpoint--companion routing

The selector restriction also has a pointwise form.  Fix `f in S_i`, with
companion `r_f`, and `a in X`.  Evaluating
`H_C B+B H_F=J` at `(a,f)` gives

```text
(B H_F)_(a,f)=1-1_{H_C(a,r_f)}.                         (11)
```

Indeed, the two `B`-neighbors of `f` are `c_i,r_f`, and membership
`a in X` excludes `H_C(a,c_i)`.  The remaining term counts exterior
labels `v` for which `a` is a selector endpoint and `f` is an
`H_F`-neighbor.  Its value is at most one, also directly by C4-freeness.
Consequently the non-`H_C` ordered pairs

```text
(a,r_f),       a in X, f in S_i
```

are in exact bijection with such endpoint--leaf routings through exterior
centers.

Let `R_i={r_f:f in S_i}`, and let `e_H(X,R_i)` denote the oriented
`H_C` incidence count from the labels in `R_i` into `X`.  There are
therefore exactly

```text
2n(n-1)-e_H(X,R_i)                                      (12)
```

endpoint--leaf routings for fiber `i`.  Every rainbow center contributes
both selector endpoints, hence exactly `2w` of them.  The non-rainbow
remainder is

```text
6n-2 sum_{a<b} gamma_ab+2u-e_H(X,R_i).                  (13)
```

Since every companion has `H_C`-degree two,
`e_H(X,R_i)=2n-e_H(W,R_i)`; equivalently (13) is

```text
4n-2 sum_{a<b} gamma_ab+2u+e_H(W,R_i).                  (14)
```

For a rainbow center with leaves `f_i` and selector endpoints `a,b`,
(11) in particular forces `a,b` to avoid the `H_C`-neighborhood of
each of its three companions.  Thus the remaining exceptional selector
patterns must also realize the exact finite `W x R_i` incidence ledgers
(14), rather than merely the edge counts (9)--(10).

## Three almost-coincident matching unions

The banked selector-star perfect-matching theorem packages the same
structure globally.  For `f in S_i`, let `M_f` be the perfect matching
of `C` formed by the two-point `C`-selectors of all ambient neighbors of
`f`.  Its two neighbors in `C` are `c_i,r_f`, so `M_f` contains the
two selector pairs

```text
W_i=N_H_C(c_i),       N_H_C(r_f).
```

For distinct `f,f' in S_i`, the matchings intersect exactly in `W_i`.
Indeed, equality of two target-`C` selector edges identifies their ambient
centers by selector injectivity; that center must then be the unique common
neighbor `c_i` of `f,f'`.  After deleting `W_i`, the `n` matchings
in this family are therefore pairwise edge-disjoint one-factors of
`C\W_i`.  Let `A_i` be their union.  Then

```text
deg_A_i(x)=n for x outside W_i,       deg_A_i(x)=0 for x in W_i,
|E(A_i)|=n(n+1).                                         (15)
```

The intersections of these three dense factors retain the two possible
shores of their unique ambient center.  Selector injectivity and the
one-neighbor caps give

```text
|E(A_i intersect A_j)|
  = |T_i intersect T_j| + p_ij
  = n^2-2n+gamma_ij+p_ij.                               (16)
```

The first term consists of selector edges of common centers in `F`; the
second consists of the distinct neighborhood pairs `N_H_C(r)` for
`r in R_i intersect R_j`.

Using `gamma_ij=n-delta_ij-p_ij`, equation (16) simplifies to

```text
|E(A_i intersect A_j)|=n^2-n-delta_ij,
|E(A_i) \ E(A_j)|=2n+delta_ij.                         (16a)
```

Moreover, `A_i` contains no edge wholly inside `W_j`.  Such an edge
would equal the target selector of `c_j`; selector injectivity would force
`c_j` to be an ambient neighbor of some `f in S_i`, contrary to the
disjointness of the carrier fibers.  The two vertices of `W_j` both have
`A_i`-degree `n`, whereas they are isolated in `A_j`.  Thus exactly
`2n` edges of `A_i\A_j` touch `W_j`, and the remaining

```text
delta_ij
```

lie wholly in `C\(W_i union W_j)`.  Pairwise disagreement away from the
four forced hole vertices is exactly the companion-defect count, not merely
an `O(n)` error.

Put

```text
t=|R_0 intersect R_1 intersect R_2|.
```

The same center split at the triple intersection is exact:

```text
|E(A_0 intersect A_1 intersect A_2)|=w+t.               (17)
```

Here the `w` edges are rainbow selectors with centers in `F`, while the
`t` edges are the `H_C`-neighborhood pairs of common companions in
`C`; the two classes cannot collide by target-selector injectivity.

Each `R_i` is exactly the `L`-neighborhood of `c_i`: the companion
map supplies `n` distinct such neighbors and both sets have cardinality
`n`.  Hence `p_ij=(L^2)_(c_i,c_j)`, and `t` is the common
`L`-neighborhood size of the defect triangle.  Also every `R_i` avoids
the three triangle labels, so the three `n`-sets lie in the common
`2n+1` point universe `C\Q`.  Inclusion-exclusion gives

```text
3n-(p_01+p_02+p_12)+t
  = |R_0 union R_1 union R_2| <= 2n+1,
t <= p_01+p_02+p_12+1-n,                               (17a)
p_01+p_02+p_12 >= n-1.                                 (17b)
```

The slack in (17a) is exactly the number of nontriangle labels unused by
all three companion systems.

Consequently, for every `i`,

```text
|E(A_i) \ E(A_0 intersect A_1 intersect A_2)|
  =5n-(gamma_01+gamma_02+gamma_12)+u-t.                 (18)
```

Thus three explicitly factorized `n`-regular graphs with different
two-vertex holes agree outside only `O(n)` edges.  The new scalar `t`
records precisely the common-companion part that is invisible in the
rainbow-star count.

## Disposition

This is the first constraint which uses the rainbow centers as the actual
self-indexed exterior labels rather than merely as entries of a partial
Latin square.  It concentrates all their selector edges inside `X` and
nearly saturates the `B`-capacity there.

It is not yet a contradiction.  But the unresolved selector freedom has
been localized: `L[X]` is exactly the rainbow selector graph, and the
cross-block counts on `W` are fixed by the hole intersections. A terminal
must show that this exact
self-indexed rainbow realization is incompatible with the companion/owner
labels and the three near-saturated partial-Latin projections.  The raw
incidence capacity alone still has nonnegative slack.

`NONBIP_MIXED_SIZE_TWO_TRIPLE_COMPANION_AUDIT.md` makes the limitation
concrete: a cyclic C-shore construction satisfies the diagonal Gram
partition, commutation, all companion scalar counts, and these W-edge
counts for every even `q>=8`. It does not construct the exterior graph.
The remaining force must come from simultaneous exterior compatibility,
not those C-shore counts alone.
