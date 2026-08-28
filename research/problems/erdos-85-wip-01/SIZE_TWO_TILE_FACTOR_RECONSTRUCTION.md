# Size-two tile factor reconstruction

Node: `A-REG-NONBIP / all size-two`; divergence round 104.

Status: exact branch-wide interface.  The complete family of individual
intermediate-color tiles recovers the left and right kernels of every reused
two-regular factor over characteristic zero.

## Setup

Let the defect components be `C_1,...,C_r`, all of order `2q`, and put

```text
X_cd=A[C_c,C_d],
Y_e^(c,d)=X_ce X_ed.
```

Every `X_cd` is a zero--one matrix with row and column sum two, and
`X_dc=X_cd^T`.  For fixed intermediate color `e`, the same left factor
`X_ce` is reused in every tile whose source is `c`, while the same right
factor `X_ed` is reused in every tile whose target is `d`.

The within-component Gram matrix is

```text
Q_e=sum_d X_ed X_de=(q-1)I+J-D_e,                    (1)
```

where `D_e` is the connected `(q-1)`-regular defect graph induced on `C_e`.

## Positivity of the within Gram

Over the reals, `Q_e` is positive definite.  On the constant vector its
eigenvalue is `2q`.  On the perpendicular complement, an eigenvalue `mu` of
`D_e` gives eigenvalue `q-1-mu`.  Connectedness of the regular graph makes
every nonprincipal `mu` strictly smaller than `q-1`, so all these values are
positive.

Equivalently, the vertically stacked matrix with block rows `X_de` has full
column rank.  This conclusion uses connectedness of the actual defect
component, not a circulant, affine, or eigenline normalization.

## Common-kernel reconstruction

Fix colors `c,e`.  Then

```text
intersection_d ker((Y_e^(c,d))^T)=ker(X_ce^T).        (2)
```

Indeed, the right side is contained in every kernel because

```text
(Y_e^(c,d))^T=X_de X_ec.
```

Conversely, suppose `v` is killed by every displayed tile transpose and put
`u=X_ec v`.  Then `X_de u=0` for every `d`.  Multiplying by the transpose
blocks and summing gives `Q_e u=0`; positivity of `Q_e` forces `u=0`, hence
`X_ec v=0`, which is exactly `v in ker(X_ce^T)`.

Dually, fixing `e,d` and varying the source gives

```text
intersection_c ker(Y_e^(c,d))=ker(X_ed).              (3)
```

Thus the individual tiles remember the singular flags of their common
factors even though the factors themselves have been eliminated from the
bare four-regular support partition.

## Cycle interpretation and scope

Over `F_2`, a two-regular bipartite factor has one kernel direction for each
cycle component: its two permutation sheets sum to an unsigned cycle
incidence matrix.  Equations (2)--(3) are proved above only in characteristic
zero; reduction modulo two can acquire additional kernel and cannot be
claimed from the same positivity argument.  A useful arithmetic lift must
therefore compare the reconstructed rational kernel with the binary or
`Z/4` kernel and retain the corresponding Bockstein/Smith defect.

There is a sharp warning at `Z/4`: the naive common-kernel equality is false.
Every tile has row and column sum four, so

```text
1 in intersection_d ker((Y_e^(c,d))^T mod 4).
```

But every factor has row and column sum two, hence

```text
X_ce^T 1 = 2 1 != 0 mod 4.
```

Thus the constant vector is an explicit element of the left side which is
not in the proposed factor kernel.  In the characteristic-zero converse,
positivity turned `Q_e u=0` into `u=0`; modulo four this step fails already
on constants because `Q_e 1=2q 1=0 mod 4`.  Conceptually, a product of two
degree-two factors erases the constant Bockstein (`2*2=4`).  Any `Z/4`
consumer must retain divided images or marked integral lifts; it cannot
obtain the factor Bockstein from common tile kernels alone.

The result is an interface, not a contradiction.  It is empty when a factor
is invertible, which can happen for a disconnected two-regular bipartite
factor whose cycle half-lengths are all odd.  When a cross factor is one
connected cycle on shores of even order, its one-dimensional alternating
kernel is recovered canonically from all its tiles.  The remaining terminal
would have to show that the reciprocal family of these reconstructed flags,
together with the symmetric self-indexed diagonal cycle factors, is
incompatible for binary `q>=8`.

## Why this is finer than owner annihilation

Summing compositions over an endpoint color recovers the already-proved
rank-one owner product and centered-owner annihilation.  Those sums forget
which endpoint tiles share a factor.  Equations (2)--(3) instead take an
intersection across the **individual** summands and recover precisely that
common factor's kernel.  They should not be collapsed back to a summed owner
identity in a future consumer.
