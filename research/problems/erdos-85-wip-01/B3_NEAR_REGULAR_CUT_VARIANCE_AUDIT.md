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

## Scope

Equations (1)--(4) are exact and global.  They couple cut size to the three
colored high-root collision masses, which the earlier local B0 type ledger
does not do.  The first canonical shores above have substantial slack, so
they do not by themselves exclude the second profile.  The useful next
consumer must choose a location-sensitive shore whose defect boundary is
already controlled by the row-cover/transversal structure; applying only
whole-bin totals reproduces known quotient mass rather than a contradiction.

The component-order list is stronger: it is a finite necessary classification
derived symbolically from the exact identity.  It is not yet sufficient to
prove that `D0` is connected or to eliminate any listed component type.

No Lean theorem or nonexistence conclusion is claimed in this audit.
