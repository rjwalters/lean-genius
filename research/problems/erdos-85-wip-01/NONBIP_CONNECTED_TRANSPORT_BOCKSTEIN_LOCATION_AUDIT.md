# NONBIP-CONNECTED transport Bockstein location audit

Date: 2026-08-27. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **exact second-bit location identity; terminal still open**.

## Convergence

Divergence round 92 independently nominated the same next object twice: do
not reduce the canonical integer transport

```text
B = A^2(A+I) = A^3+A^2
```

only modulo two.  Lift its action on a binary adjacency-kernel shore through
division by two.  The competing raw statement, that the D-label on K is a
vertex coboundary, is already false in the q=4 control: K has a triangle
with exactly one D-edge (`fbd96e249e`).

## Exact lift

Let `s=1_S` be the zero-one vector of a binary kernel shore and write

```text
A s = 2c,                 beta = c mod 2.              (1)
```

Over the integers,

```text
B s = A^2(A+I)s
    = A^2(2c+s)
    = 2(A^2c+Ac).                                      (2)
```

Therefore `Bs` is entrywise even and its canonical half satisfies

```text
(B s / 2) mod 2 = (A^2+A) beta.                       (3)
```

This is the coefficient Bockstein that the earlier triangle-incidence audit
did not have: it comes from an actual divisible integer matrix-vector
product, so there is no choice of lift and no homological ambiguity.

## The whole dyadic tower

The calculation is not confined to the first half-occupancy digit.  Suppose
at any level `j>=1` that every line occupancy is divisible by `2^j`, and
define its integer quotient and next binary digit by

```text
A s = 2^j c_j,             gamma_j = c_j mod 2.        (3a)
```

The same integer calculation gives

```text
B s = 2^j (A^2+A)c_j,
(B s / 2^j) mod 2 = (A^2+A) gamma_j.                  (3b)
```

The support of `gamma_j` is exactly
`dyadicOccupancySupport G S j`.  The existing stopping package proves that
at the first nonzero level `1<=j<k` this support is nonempty and even, and
is unchanged when S is replaced by its complement.  At the final level
`j=k-1`, the connected-defect theorem
`c4Free_binarySquare_finalDyadicSupport_ne_univ` additionally makes it
proper, so `gamma_j` is genuinely nonconstant there.  This is the precise
way the lift can see structure absent in the q=4 calibration: not through
beta alone, but through the first surviving higher digit, or through the
proper final digit in the final-layer subtree.

The carry can be written exactly.  For fixed `x,S`, define the entrywise
`j`-th digit and lower-digit carry

```text
delta_j(x,y) = floor(B_xy/2^j) mod 2,
kappa_j(x,S) = (sum_(y in S) (B_xy mod 2^j))/2^j mod 2. (3c)
```

The numerator defining `kappa_j` is divisible by `2^j`: subtracting the
sum of the entrywise quotients from the divisible row sum in (3b) proves
this directly.  Euclidean division entry by entry then turns (3b) into

```text
kappa_j(x,S) + sum_(y in S) delta_j(x,y)
  = ((A^2+A) gamma_j)_x                         (mod 2). (3d)
```

Thus the higher location problem has two named pieces, not an unspecified
error term: the carry of the lower transport digits and the located `j`-th
digit.  At `j=1`, `B_xy mod 2` is the H-edge indicator, so `kappa_1` is
exactly half the H-incidence into S; equation (5) below is this instance.

## Graph-facing decomposition

Let `H` be the odd support of B.  The completed direct-transport package
proves

```text
H = K disjoint-union T,
```

where K is disjoint from A and T consists of the ambient edges lying in no
triangle.  For every entry put

```text
r_xy = floor(B_xy/2) mod 2.
```

Since `B_xy = 1[xy in H] + 2 r_xy (mod 4)`, equation (2) first recovers
the known parity law

```text
deg_K(x,S) = deg_T(x,S) (mod 2),                       (4)
```

and then supplies its next digit:

```text
(deg_K(x,S)+deg_T(x,S))/2
  + sum_(y in S) r_xy
  = ((A^2+A) beta)_x                         (mod 2).  (5)
```

The division in (5) is legitimate by (4).  Off A, `B_xy` is exactly the
common-neighbor atom plus the cross-neighborhood matching size from audit
equation (21); on A it is the corresponding triangle/triangle-free count.
Thus `r_xy` is a located mod-four incidence digit, not an auxiliary edge
color.

## Exact q=4 calibration

The fixed-free q=4 control has two kernel shores, the two D-components.
For either component S, every line occupancy is two, so `c=1` and
`beta=1`; the right side of (5) is zero.  Direct evaluation gives exactly
two row types:

```text
x in S:
  (deg_K(x,S), deg_T(x,S), sum_S r_xy) = (2,0,1)
                                              or (0,2,1),
x outside S:
  (deg_K(x,S), deg_T(x,S), sum_S r_xy) = (4,0,0).
```

Hence the residual digit is precisely `1_S` in this control, and it cancels
the half-degree term pointwise.  This is a positive calibration of (5), but
also a warning: the second bit need not vanish, be component-blind, or be
determined by beta alone.

## Bounded verdict

Equations (3b) and (5) are strictly finer than the completed F2 transport
package and give the first exact self-indexed dyadic location law for K.  The
q=4 probe `889616792d` decisively falsifies the **beta-only** location
terminal: complementary component shores have the same beta but
complementary half-cut and residual vectors.  It does not falsify the tower
identity (3b), whose useful input is the stopping digit `gamma_j`.

It is not yet a terminal.  The q=4 calibration shows that the residual
matching digit can pay the entire half-degree demand.  A successful consumer
must constrain the carry/digit pair (3c), beginning with the located row sums

```text
sum_(y in S) floor((A^3+A^2)_xy/2) mod 2              (6)
```

using the first nonzero stopping digit (or the proper nonconstant final
digit in the final-layer subtree), and then couple that constraint to
connectedness of D.  Until such a consumer is named, (3)--(5) should remain
an audited interface rather than a standalone Lean wrapper.
