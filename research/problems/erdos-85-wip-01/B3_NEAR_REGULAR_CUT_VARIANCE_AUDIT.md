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

The pointwise bin inputs are Lean-checked; the short component-order consumer
is recorded here and in the exact arithmetic checker, but is not yet
packaged as a new Lean theorem.  No nonexistence conclusion is claimed.
