# B.3 near-regular defect cut variance

## Exact identity

Let `A` be a loopless `C4`-free graph on `q^2` vertices whose degrees are
`q`, except for a three-point set `H` of degree `q+1`.  Let `D` be the
off-diagonal zero-common-neighbor graph.  For `S` of size `s`, put

```text
b_v = deg_A(v,S),
h   = |S intersect H|,
B_H = sum_{v in H} b_v.
```

Counting length-two paths across the cut gives

```text
delta_D(S)
  = s(q^2-s) - sum_v b_v(deg_A(v)-b_v)
  = sum_v b_v^2 - s^2 - qh - B_H.             (1)
```

Also

```text
sum_v b_v = q s + h.                           (2)
```

This is the near-regular analogue of the regular cut-variance identity.

## The high vertices disappear from the defect graph

Apply (1) to a singleton high vertex.  Its `b`-vector is its adjacency row,
so `sum b_v^2=q+1`.  Equation (1) says

```text
deg_D(h) = - |N_A(h) intersect H|.
```

Both sides have opposite signs unless the intersection is empty.  Therefore
the three high vertices are `A`-independent and isolated in `D`.  This
recovers the known high-independence fact directly from the cut identity.

It is consequently enough to take `S` disjoint from `H`.  Writing
`beta_h=deg_A(h,S)`, (1) becomes

```text
delta_D(S)
  = sum_{v notin H} b_v^2 - s^2
    + sum_{h in H} beta_h(beta_h-1),            (3)

sum_{v notin H} b_v = q s - sum_h beta_h.       (4)
```

The final term is an exact colored collision mass: it counts ordered pairs
of points of `S` that share each high root.

For an ordinary singleton with `i` high neighbors, (3) gives
`deg_D(v)=q-1-i`, exactly the existing `B_i` degree stratification.

## Integer-minimum consequences at q=9

For fixed `s` and the three values `beta_h`, minimize the first sum in (3)
among the 78 ordinary integer degrees with total (4).  If `M=9s-sum beta`
and `M=78a+r`, the unconstrained convex minimum is

```text
(78-r)a^2 + r(a+1)^2.
```

The second three-high profile has ordinary bin sizes

```text
|B0|=50, |B1|=27, |B3|=1.
```

For `B0`, all `beta_h` vanish, and (3) gives

```text
delta_D(B0) >= 60*6^2 + 18*5^2 - 50^2 = 110.
```

For `B1`, each high root has nine bin-one neighbors, so
`beta=(9,9,9)`.  The ordinary degree total is 216, minimized by sixty 3s and
eighteen 2s.  Thus

```text
delta_D(B1) >= 60*3^2 + 18*2^2 - 27^2
               + 3*(9*8)
             = 99.
```

For the unique `B3` point, `beta=(1,1,1)` and (3) returns its exact defect
degree `5`.

There is also a root-neighborhood bound.  If `S=N_A(h)` for a high root,
then `s=10`, `beta_h=0`, and each of the other two beta values is at most one
by C4-freeness.  Convex minimization in the three cases gives respectively
`14`, `11`, and `8`; hence

```text
delta_D(N_A(h)) >= 8.                           (5)
```

## Necessary component orders in the ordinary defect graph

Let `D0` be the defect graph induced on the 78 ordinary vertices.  If `S` is
a union of `D0`-components, then its defect boundary is zero.  For
`beta=(beta_1,beta_2,beta_3)`, put

```text
M = 9|S| - (beta_1+beta_2+beta_3).
```

Writing `M=78a+r`, equations (3)--(4) give the necessary inequality

```text
0 >= (78-r)a^2 + r(a+1)^2 - |S|^2
       + sum_i beta_i(beta_i-1).                 (6)
```

Apply (6) to both `S` and its complement, whose color vector is
`(10,10,10)-beta`.  Handshake adds `sum beta_i` even, since

```text
2 e_D(S) = 8|S| - sum beta_i.
```

If `D0` is disconnected, choose a smallest component, so `|S| <= 39`.
Evaluating the elementary convex inequalities leaves only the following
orders and color vectors, up to permutation:

```text
 9 : (0,1,1), (0,2,2), (1,1,2), (2,2,2)
18 : (2,2,2), (2,2,4), (2,3,3), (3,3,4)
19 : (2,3,3), (3,3,4)
26 : (3,3,4)
27 : (4,4,4)
35 : (4,5,5).
```

Every other order from 1 through 39 is impossible at this layer.  In the
order-nine cases,

```text
e_D(S) = (8|S| - sum beta_i)/2,
```

so `D[S]` is `K9` with respectively one, two, two, or three edges removed.
This turns the smallest surviving component into a near-clique placement
problem rather than an unrestricted finite census.

The same test on all orders from 1 through 77 leaves the symmetric order set

```text
{9,18,19,26,27,35,43,51,52,59,60,69}.
```

Partitioning 78 by these orders gives exactly eleven possible disconnected
component-order multisets:

```text
[9,69], [18,60], [19,59], [26,52], [27,51], [35,43],
[9,9,60], [9,18,51], [9,26,43], [26,26,26], [9,9,9,51].
```

In particular, `D0` has at most four components.  Requiring every component
vector to lie in its own order's admissible list above, and requiring those
vectors to sum to `(10,10,10)`, eliminates none of these eleven rows;
the respective numbers of ordered color-vector assignments in the displayed
order are

```text
10, 10, 6, 3, 1, 3, 39, 10, 9, 6, 39.
```

Thus the cut identity turns disconnectedness into a finite eleven-row
structural classification, while also proving that color totals alone are
not the missing terminal.  The exact integer enumeration is independently
reproducible with `q9_near_regular_cut_components.py`; it checks both the
order list and all eleven assignment counts, without enumerating graphs.

## Localization of the bin-one two-factor

The Lean theorem
`squareOrderNine_threeHigh_secondProfile_binOne_defect_twoRegular` says that
the 27 bin-one vertices induce a two-regular graph in `D`.  Its three
nine-point high-root color classes are independent by
`squareOrderNine_threeHigh_secondProfile_binOne_color_edge_ledger`.  Hence the
bin-one vertices lying in any `D0`-component induce a disjoint union of whole
cycles.

This localizes the color vector.  Let `x` be the unique bin-three vertex.  If
a component `S` does not contain `x`, its three bin-one color counts equal
`beta(S)`.  If `x` belongs to `S`, then `x` is adjacent in `A` to all three
high roots, and those counts equal

```text
beta(S) - (1,1,1).                              (7)
```

For bin-one color counts `(a,b,c)`, two-regularity and color independence
force the numbers of edges between the three color pairs to be

```text
e_ab = a+b-c,   e_ac = a+c-b,   e_bc = b+c-a.  (8)
```

They must be nonnegative and cannot exceed the simple-graph capacities
`ab`, `ac`, and `bc`; a nonempty bin-one portion also contains at least three
vertices.  Applying only these necessary conditions gives the
following refinement.  In the eleven-row display above, the numbers of
surviving color-vector assignments are respectively

```text
7, 10, 6, 3, 1, 3, 27, 7, 9, 6, 21.
```

Counting also the choice of which component contains `x` gives respectively

```text
8, 17, 12, 6, 2, 6, 33, 12, 18, 18, 21.
```

There are two useful location conclusions.  In `[9,9,9,51]`, the bin-three
vertex must lie in the order-51 component.  In `[9,26,43]`, it cannot lie in
the order-nine component.  More locally, the order-nine color type
`(0,1,1)` is impossible altogether: without `x` it would require a simple
two-regular graph on two vertices, while with `x` equation (7) is negative.

If `x` does lie in an order-nine component, still more is forced.  Its color
vector is necessarily `(2,2,2)`, so its bin-one portion has color counts
`(1,1,1)` and is a triangle.  The order-nine calculation above says that the
whole component is `K9` minus three edges.  Since bin-one vertices have no
defect edge to `x`, the three missing edges are exactly the star from `x` to
that triangle.  Equivalently, the other five vertices are bin-zero, form a
defect `K5`, and are all five defect neighbors of `x`.  This is an exact
forced component geometry, although the present packing laws do not exclude
it.  The cycle conditions still leave all eleven order rows, so the result is
a strict profile and location refinement rather than a disconnectedness
contradiction.

## Componentwise bin-degree capacity

There is one further exact aggregate constraint.  Write `epsilon=1` for the
component containing `x` and `epsilon=0` otherwise.  Equations (7) and the
pointwise bin-degree theorems give

```text
n1 = sum beta_i - 3 epsilon,
n0 = |S| - n1 - epsilon,
e_D(B1,B1;S) = n1,
e_D(B1,B0;S) = 5 n1,
e_D(B3,B0;S) = 5 epsilon.
```

Indeed every bin-one vertex has exactly two bin-one and five bin-zero defect
neighbors, while the unique bin-three vertex has all five defect neighbors
in bin zero.  Summing degree eight over the bin-zero vertices therefore
determines

```text
e_D(B0,B0;S) = (8 n0 - 5 n1 - 5 epsilon)/2.     (9)
```

The right side must be an integer between zero and `C(n0,2)`, and a nonempty
`B1`--`B0` or `B3`--`B0` incidence requires `n0 >= 5`.  This removes the
non-owner order-nine type `(2,2,2)`: it would have `n1=6`, `n0=3`, and a
negative value in (9).  Consequently every order-nine component not
containing `x` has color type `(0,2,2)` or `(1,1,2)`, up to permutation; in
either case its five bin-zero vertices form a defect `K5` and its four
bin-one vertices form a colored `C4`, with every cross edge present.

At the eleven-row level, (9) leaves the same numbers of color assignments as
the two-factor test, but reduces the numbers of possible placements of `x`
to

```text
7, 17, 12, 6, 2, 6, 27, 10, 18, 18, 21
```

in the displayed order.  Thus it removes six placements in `[9,9,60]`, two
in `[9,18,51]`, and one in `[9,69]`, without yet eliminating an order row.

## Pointwise bin types force connectivity

The aggregate capacity calculation is superseded by the existing Lean
pointwise theorem
`squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy`.
Every bin-zero vertex has defect-neighbor counts

```text
(B0,B1,B3) = (5,3,0) or (7,0,1),               (10)
```

and the five vertices of the second type are exactly the defect neighbors
of the unique bin-three vertex.  Now suppose that `D0` is disconnected and
choose any component `S` not containing that vertex.  Such a component
exists because only one component can contain it.  All `n0` bin-zero
vertices of `S` have the first type in (10), so counting the `B0`--`B1`
defect edges from the bin-zero side gives `3 n0`.  Every bin-one vertex has
exactly five bin-zero defect neighbors, all in its own component, so the same
edge count from the `n1` bin-one vertices is `5 n1`.  Therefore

```text
3 n0 = 5 n1,
n0 = 5k,  n1 = 3k,
|S| = n0+n1 = 8k.                               (11)
```

But the complete proper-component order list obtained from (6) is

```text
{9,18,19,26,27,35,43,51,52,59,60,69},
```

which contains no multiple of eight.  This contradiction proves:

```text
The ordinary defect graph D0 on 78 vertices is connected.              (12)
```

In particular, all eleven disconnected order rows are impossible.  The
earlier order-nine localization calculations are retained only as checks of
the weaker aggregate layers; (10)--(12) are the decisive consumer.

## If the bin-three vertex is an articulation

Connectivity makes deletion of the unique bin-three vertex `x` the next
natural separator test.  Suppose a component `S` of `D0-x` contains `e` of
the five exceptional bin-zero vertices, `r` regular bin-zero vertices, and
`n1` bin-one vertices.  Its only boundary edges in `D0` are the `e` edges to
`x`.  Counting `B0`--`B1` edges again gives `3r=5n1`, so for some `k`

```text
r=5k,  n1=3k,  n0=e+5k,
|S|=e+8k,  delta_D(S)=e.                        (13)
```

The internal bin-zero degree sum is also exact.  Each exceptional vertex has
seven bin-zero defect neighbors and each regular vertex has five, all in
`S`; hence

```text
2 e_D(B0,B0;S) = 7e+25k.                        (14)
```

Thus `7e+25k` is even, `n0>=8`, and the right side of (14) is at most
`n0(n0-1)`.  Apply (6) to `S` and its complement with boundary `e`, then
assemble components using

```text
sum e=5,  sum k=9,  sum beta=(9,9,9).
```

The exact checker leaves nine color assignments.  Every one has exactly two
components, with the exceptional vertices split `2+3`; their order pairs
are

```text
(18,59) : seven assignments,
(27,50) : one assignment,
(34,43) : one assignment.                       (15)
```

Consequently `x` can be an articulation only in these three sharply
specified branches.  This is not yet a proof that `D0-x` is connected; a
location-sensitive consumer of (15) is still required.

### Equality shores

Eight of the nine assignments in (15) attain equality in the convex square
bound on at least one shore.  Equality forces every ordinary center degree
`b_v=|N_A(v) intersect S|` to take one of two consecutive values.  Up to
permuting colors, the exact profiles are:

```text
order 60, beta=(7,8,9), boundary 2:
  thirty centers of degree 6 and forty-eight of degree 7  (six assignments);

order 34, beta=(4,4,4), boundary 2:
  eighteen centers of degree 3 and sixty of degree 4;

order 50, beta=(6,6,6), boundary 2:
  thirty-six centers of degree 5 and forty-two of degree 6;

order 51, beta=(7,7,7), boundary 3:
  thirty centers of degree 5 and forty-eight of degree 6.
```

The order-60 shore is `x` together with the order-59 component.  Since `x`
has exactly six ordinary `A`-neighbors, equality forces all six into that
shore and none into the order-18 component.  In the `(27,50)` branch the
order-50 equality instead forces five or six of those neighbors into the
order-50 component.  In the `(34,43)` branch, three or four lie in the
order-34 component.  The sole articulation assignment with no equality
shore is the symmetric `(18,59)` color split `(2,2,2)/(7,7,7)`.

The first equality profile actually gives a contradiction.  Let `S` be the
order-18 component with `beta(S)=(1,2,3)` after naming the high roots
`h_a,h_b,h_c`, and let `T` be its ordinary complement.  If `Z` is the set of
30 ordinary centers having six neighbors in `T`, then, on all 81 vertices,

```text
A 1_S = 2 1 + 1_Z - A 1_H - e_(h_a) + e_(h_c). (16)
```

Here `A 1_H` is the high-incidence vector.  Use

```text
D = 8I + J + diag(1_H) - A^2,
A^2 1_H = 3 1 + 9 1_H,
```

where the second identity uses high independence and the fact that every
high vertex is isolated in `D`.  Substituting (16) gives

```text
D 1_S = 8 1_S + 3 1 + 7 1_H - A 1_Z
          + 1_(N_A(h_a)) - 1_(N_A(h_c)).        (17)
```

At a high root, the left side is zero and the last two terms vanish, so
every high root has all ten `A`-neighbors in `Z`.  At `x`, the left side is
two (the two exceptional vertices of `S`), while `x` is adjacent to both
`h_a` and `h_c`; hence (17) gives

```text
|N_A(x) intersect Z| = 1.                       (18)
```

But `x` has one bin-one original partner at each of the three high roots.
Those three distinct partners are neighbors of their high roots, hence all
belong to `Z`, and all are adjacent to `x`.  This contradicts (18).

Therefore all six nonsymmetric `(18,59)` assignments are impossible.  The
B3-articulation frontier shrinks from nine assignments to exactly three:

```text
(18,59) with beta=(2,2,2)/(7,7,7),
(27,50) with beta=(3,3,3)/(6,6,6),
(34,43) with beta=(4,4,4)/(5,5,5).              (19)
```

The equality low sets in the last two branches are also rigid.  In the
`(27,50)` branch, let `S` be the order-50 component and let `Z` be the 36
ordinary centers having five neighbors in `S`.  Equality says

```text
A 1_S = 6 1 - 1_Z,
D 1_S = 8 1_S - 4 1 - 6 1_H + A 1_Z.           (20)
```

Evaluation at each high root gives `|N_A(h) intersect Z|=10`, so `Z`
contains `x` and all 27 bin-one vertices; its other eight vertices are bin
zero.  Since `x in Z`, the first equation in (20) gives

```text
|N_A(x) intersect S| = 5.
```

Thus the six ordinary neighbors of `x` split exactly `5+1` between the
order-50 and order-27 components.

This branch is in fact impossible.  Write

```text
Z = {x} union B1 union W,   |W|=8,
```

so all three original bin-zero neighbors of `x` lie in `W`.  For a bin-zero
vertex `y`, the pointwise original-neighbor theorem says that `y` has no
bin-one original neighbor when `y~x`, and exactly three otherwise.  Hence

```text
deg_A(y,W) = deg_A(y,Z)-1  if y~x,
deg_A(y,W) = deg_A(y,Z)-3  otherwise.            (21)
```

On the order-50 side, (20) gives `deg_A(y,Z)=3` for its two exceptional
vertices and four for its regular bin-zero vertices.  Every bin-zero vertex
on the order-27 side has `Z`-degree four.

If `x` has three local edges, its three bin-zero neighbors are all
exceptional and span no edge.  The order-27 side contains exactly one
ordinary neighbor of `x`; because it contains three exceptional vertices
while the other side contains only two, this unique neighbor must be one of
the three original exceptional vertices.  Thus the three bin-zero neighbors
of `x` have `W`-degrees `3,2,2`.  Being independent, they send seven edges to
the other five points of `W`, but (21) gives those other points total degree
only five.  Contradiction.

If `x` has four local edges, its bin-zero neighbors are one exceptional and
two regular vertices, and the two regular vertices span the unique extra
local edge.  Their total `W`-degree is at least eight, so after subtracting
twice their one internal edge they send at least six edges to the other five
points.  Equation (21) gives those five points total degree at most five,
again a contradiction.  Therefore

```text
the (27,50) B3-articulation branch is impossible.                 (22)
```

In the `(34,43)` branch, take the order-34 component `S` and the 18-center
low set `Z`.  Here

```text
A 1_S = 4 1 - 1_Z,
D 1_S = 8 1_S - 2 1 - 4 1_H + A 1_Z.           (23)
```

Every high root has six neighbors in `Z`, for total high incidence 18, and
evaluation at `x` gives `|N_A(x) intersect Z|=4`.  If `x` were not in `Z`,
all 18 points of `Z` would be bin one, so only the three bin-one partners of
`x` could be its neighbors in `Z`, a contradiction.  Hence

```text
Z = {x} union (fifteen B1 points, five of each color) union (two B0 points),
```

and the first equation in (23) forces exactly three ordinary neighbors of
`x` on each articulation side.

This two-point low set has a further local consequence.  Let `P` be its
fifteen bin-one points, let `W` be its two bin-zero points, and put

```text
p = |P intersect N_A(x) intersect B1|,
q = |W intersect N_A(x) intersect B0|.
```

The three bin-one neighbors of `x` are its high-root partners and its three
bin-zero neighbors will be denoted by `U`.  Since `|N_A(x) intersect Z|=4`,

```text
p+q=4,  so (p,q) is either (2,2) or (3,1).       (24)
```

For a high-root partner `z`, the pointwise bin-one profile gives no bin-one
neighbors.  Thus, because `x in Z`, equation (23) gives

```text
deg_A(z,W)=0 if z is on the order-34 side,
deg_A(z,W)=1 if z is on the order-43 side.       (25)
```

The already proved local-triangle profile at `x` says more than just the
types of the three points in `U`: the three forced high--partner edges use
all local edges in the three-edge branch, while in the four-edge branch the
unique additional local edge joins the two regular points of `U`.

**Retraction of the order-34 placement kill.**  The argument below treated
every bin-zero owner-neighbor as having all eight defect neighbors in its
deleted-owner shore and hence `Z`-degree two.  This is false for the
exceptional points `E = N_D(x) ∩ B0`: each has the deleted owner `x` as its
eighth defect neighbor.  Relative closure therefore gives seven in-shore
neighbors when `e ∈ S`, not eight.  Equation (23) gives

```text
deg_A(e,Z)=1 for e in the order-34 shore S,
deg_A(e,Z)=2 for e in the complementary shore.
```

Here two defect sets must be distinguished.  The full-type ledger has
`|F ∩ S|=2` for the total five-point set
`F = N_D(x) ∩ B0`, whereas the local profile counts only the original
exceptional set `E = N_A(x) ∩ F`: `|E|=3` in the three-local-edge branch and
`|E|=1` in the four-edge branch.  Thus the full-type count does not by itself
discard the four-edge branch.  In the three-edge `(2,2)` branch, however,
every point of `E` off `S` would have `Z`-degree two but only the owner as a
`Z`-neighbor; hence `E ⊆ F ∩ S`, contradicting `3 ≤ 2`.  This corrected
subcase is now formalized.  The subsequent prose eliminations still invoke
uniform exceptional `Z`-degree two and do not establish the remaining
four-edge placements or all of `(3,1)`.  Their regular/nondefect degree-two
inputs remain valid; until those placements are rebuilt, the `(34,43)`
branch is open.

Suppose first that `(p,q)=(2,2)`.  In the three-edge branch the two points
of `U` lying in `W` are independent.  Their `Z`-degrees force both to be the
two exceptional points on the order-34 side.  Hence exactly one partner is
on that side (the ordinary-neighbor split is `3+3`), but (25) would force
the other two partners to meet `W`, impossible because there are no further
edges inside `N_A(x)`.  Thus this subcase is dead.  In the four-edge branch,
symmetry of the two-point graph `A[W]` forces the two points of `W` to be
the adjacent regular pair: choosing the exceptional point and one regular
point is impossible because they are nonadjacent while the regular point
requires `W`-degree one.  Equation (25) then forces all three partners onto
the order-34 side.  Consequently all
three points of `U` lie on the order-43 side.  The whole `(2,2)` alternative
therefore has the single surviving placement

```text
four local edges; W is the regular U-pair; all partners are on order 34;
all three points of U are on order 43.                         (26)
```

But the third point of `U` is the exceptional one.  It is not in `W`, has
no bin-one neighbors, and the local-edge classification says it is adjacent
to neither point of the regular pair `W`.  Its only neighbor in `Z` is
therefore `x`, whereas every bin-zero point on the order-43 side has
`Z`-degree two by (23).  This contradiction eliminates `(p,q)=(2,2)`.

Now suppose `(p,q)=(3,1)`, so all three partners belong to `P`.  If `b` is
the number of points of `U` on the order-34 side, the `3+3` split puts
exactly `b` partners on the order-43 side.  By (25), each of those partners
must meet the unique point of `W\U`.  Two such partners would share both
`x` and that point, creating a four-cycle, so

```text
b <= 1.                                                       (27)
```

If `b=1` and the selected point of `U intersect W` lies on the order-43
side, both it and the unique order-43 partner must meet `W\U`, again making
a four-cycle with `x`.  Hence in the three-edge branch that selected point
must be the unique order-34 point of `U`.  In the four-edge branch it must
additionally be the exceptional point: a selected regular point has
`W`-degree one on either side and produces the same forbidden four-cycle.
If `b=1`, the selected point is the exceptional order-34 point, so the other
two points of `U` are outside `W`, have no neighbor in `P`, and have no edge
to the selected point.  Their required `Z`-degree two forces both through
the sole point of `W\U`; they share that point and `x`, a forbidden
four-cycle.

If `b=0`, the selected point of `U intersect W` is on the order-43 side and
its required `W`-degree one forces it to meet `W\U`.  In the three-edge
branch both other points of `U` also require that neighbor.  In the
four-edge branch, if the selected point is exceptional then both regular
points require it; if it is regular, the remaining exceptional point does.
In every case the selected point and at least one other point of `U` share
both `x` and `W\U`, again a four-cycle.  This kills `(p,q)=(3,1)` as well.
Consequently, in the original argument (retracted above),

```text
the (34,43) B3-articulation branch is impossible.              (28, RETRACTED)
```

The symmetric `(18,59)` branch has cut excess two rather than equality.  The
integer square-sum refinement leaves exactly two profiles on the order-60
shore:

```text
(L) one degree-5 center c, 28 degree-6, 49 degree-7;
(H) one degree-8 center c, 31 degree-6, 46 degree-7.                 (29)
```

In case (L), let `Z` contain the degree-5 center and the 28 degree-6
centers.  In case (H), let `Z` be the 31 degree-6 centers.  For the order-18
component `S`, respectively,

```text
(L) A 1_S = 2 1 + 1_Z + e_c - A 1_H,
(H) A 1_S = 2 1 + 1_Z - e_c - A 1_H.             (30)
```

The same square-identity calculation gives

```text
(L) D 1_S = 8 1_S + 3 1 + 7 1_H - A 1_Z - 1_(N_A(c)),
(H) D 1_S = 8 1_S + 3 1 + 7 1_H - A 1_Z + 1_(N_A(c)). (31)
```

In case (H), evaluation at a high root forces `c` to be high-free; otherwise
that high would have more than all ten neighbors in `Z`.  Thus all three
high neighborhoods lie in `Z`.  Evaluation at `x` then gives at most two
neighbors of `x` in `Z`, contradicting its three bin-one high-root partners.
So (H) is impossible.

In case (L), evaluation at `x` gives

```text
|N_A(x) intersect Z| = 1 - 1_[x adjacent c].     (32)
```

At the high roots, (31) says that at most the `k(c)` high-root incidences of
`c` can account for missing points of `Z`.  Hence at least `3-k(c)` of the
three distinct bin-one partners of `x` lie in `Z`.  If `c` is bin zero this
lower bound is three, and if `c` is bin one it is two; both contradict (32).
The only remaining possibility is `c=x` (the spike center is ordinary, so
there is no high-vertex case).

Therefore the symmetric articulation survivor has `x` as the unique
degree-5 center into the order-60 shore.  Equivalently, exactly one of the
six ordinary neighbors of `x` lies in the order-18 component.

The four bin-zero points in the low set now eliminate this last branch.
Write

```text
Z = {x} union P union W,  |P|=24 in B1,  |W|=4 in B0,
p = |P intersect N_A(x) intersect B1|,
q = |W intersect N_A(x) intersect B0|.
```

Equation (32) and the preceding conclusion give `p+q=1`, so either
`(p,q)=(0,1)` or `(1,0)`.  Let `U` again be the three bin-zero neighbors of
`x`, let `a` and `b` be respectively the numbers of partners and points of
`U` on the order-18 side.  The one-neighbor shore split gives

```text
a+b=1.                                                        (33)
```

Every partner has no bin-one neighbor.  Evaluating (31) at a partner shows
that it has two neighbors in `W` on the order-18 side and one on the other
side.  Thus the three partners send exactly

```text
3+a = 4-b                                                     (34)
```

edges into `W`.  Distinct partners cannot meet the same point of `W`, since
they would then have two common neighbors, that point and `x`.

Likewise, a point of `U` has no bin-one neighbor.  Its required `W`-degree
is one, except that an exceptional point on the order-18 side has degree
two.  No point of `W` can meet two points of `U`, nor can it meet both a
partner and a point of `U`, for the same common-neighbor reason.

First take `(p,q)=(0,1)`.  All three partners lie outside `P`, but (34) is
unchanged.  Their neighbors cannot be the selected point of `U intersect W`
because the exact local-edge profile at `x` has only the three high--partner
edges and, in the four-edge branch, the regular `U`-pair edge.  Hence their
`4-b` distinct neighbors lie in the three-point set `W\U`, forcing `b=1`;
all three partners are then on the order-59 side and saturate `W\U`.  But
the points of `U` require at least one further incidence with `W\U`.  In the
three-edge branch there is no `U`--`U` edge at all.  In the four-edge branch
the selected point can account for at most one required incidence of the
other regular point via their unique edge; the selected point itself still
requires a neighbor in `W\U`.  Either way a point already occupied by a
partner must also meet a point of `U`, producing a four-cycle.  Thus
`(0,1)` is impossible.

Finally take `(p,q)=(1,0)`.  All four points of `W` lie outside `U`.
The partners require `4-b` distinct points of `W`.  In the three-edge
branch the points of `U` require `3+b` further distinct points of `W`; in
the four-edge branch they require at least three.  These two sets of points
must be disjoint, yet their total required cardinality is at least six,
larger than `|W|=4`.  This contradiction kills `(1,0)`.  Therefore

```text
deleting the unique bin-three vertex does not disconnect D0.         (35)
```

## Scope

Equations (1)--(4) are exact and global.  They couple cut size to the three
colored high-root collision masses, which the earlier local B0 type ledger
does not do.  The first canonical shores above have substantial slack, so
they do not by themselves exclude the second profile.  The useful next
consumer must choose a location-sensitive shore whose defect boundary is
already controlled by the row-cover/transversal structure; applying only
whole-bin totals reproduces known quotient mass rather than a contradiction.

The component-order list and the pointwise bin dichotomy together prove that
`D0` is connected.  This is a structural conclusion for the q=9 second
three-high profile, not a graph census and not a proof that the full defect
graph cannot be connected.

The pointwise bin inputs are Lean-checked; the short component-order and
articulation consumers are recorded here and in the exact arithmetic
checker, but are not yet packaged as new Lean theorems.  No full
nonexistence conclusion is claimed.
