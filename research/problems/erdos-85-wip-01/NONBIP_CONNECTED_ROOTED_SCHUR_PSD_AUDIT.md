# NONBIP-CONNECTED rooted Schur/PSD equality audit

Date: 2026-08-26.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **mechanism cut at the first exact Schur block**.

## Proposed force

Divergence round 79 proposed splitting at a root `x`, removing the primary
direction, and looking for a positive-semidefinite equality case whose Schur
complement is a sum of squares of

```text
t_y - t_x  (for Dxy),       and       (A t)_x - 2  (mod 4).
```

The square-order two-ball slack `2t_x-1` makes this plausible only if the
fixed first/second-layer Gram block has a forced null direction.  The exact
calculation below shows that it instead has strict positive slack in every
first-layer direction.

## Exact rooted Gram decomposition

Fix `x` and put `Y=N_A(x)`.  For `y in Y`, let `r_y` be the zero-one
indicator of `N_A(y)`.  Regularity and C4-freeness give

```text
<r_y,r_z> = q  if y=z,
<r_y,r_z> = 1  if y!=z.                               (1)
```

Indeed distinct `y,z in N(x)` have the common neighbor `x`, and a second
common neighbor would make a four-cycle.  Hence the row Gram matrix is

```text
R R^T = (q-1) I + J.                                  (2)
```

Every row has value one at coordinate `x`.  Delete that coordinate and write
`s_y=r_y-e_x`.  Equation (2) becomes

```text
<s_y,s_z> = (q-1) delta_yz.                           (3)
```

Thus the root-deleted rows are already pairwise orthogonal.

The graph induced by `A` on `Y` is a matching plus isolated vertices.  Let
`epsilon_y=1` when `y` belongs to a matched pair (equivalently, to a triangle
through `x`) and zero otherwise.  Split `s_y` into its coordinate in `Y` and
its coordinates outside `{x} union Y`:

```text
s_y = ell_y + b_y.
```

Here `ell_y` is the unit vector at the matched partner when `epsilon_y=1`,
and zero otherwise.  Distinct `ell_y` have distinct supports, so

```text
<ell_y,ell_z> = epsilon_y delta_yz.
```

The coordinate sets of `ell` and `b` are disjoint.  Subtracting this identity
from (3) gives the exact external-branch Gram matrix

```text
B B^T = diag(q-1-epsilon_y).                          (4)
```

Equivalently, the external branch sets

```text
B_y = N(y) \ ({x} union N(x))
```

are pairwise disjoint and have size `q-2` on the `2t_x` matched coordinates
and `q-1` on the other `q-2t_x` coordinates.

For the intended `q>=8`, every eigenvalue in (4) is at least `q-2>0`.
Therefore the first rooted Schur block has full row rank and no equality
direction at all.  Its determinant is explicitly

```text
(q-2)^(2t_x) (q-1)^(q-2t_x),                          (5)
```

which is positive for every allowed value of `t_x`; positivity and
integrality impose no residue condition on `t_x`.

## Where further compression stops being forced

The union of the external branches has size

```text
q(q-1)-2t_x.
```

Since the graph has `q^2` vertices, the vertices outside the rooted two-ball
form a residual set of size `2t_x-1`.  Any deeper Schur complement must use
the adjacency among the external branches and this residual set (or the
adjacency within the residual set).  Those entries are not determined by
(1)--(4).  They are precisely the root-dependent second-layer incidence
that the endpoint-2 Terwilliger audit identified as uncontrolled.

Schur complement positivity remains a valid inequality after those entries
are introduced, but there is no rank or dimension equality forcing the
complement to vanish: (4) is invertible with large positive slack.  Turning
the resulting inequality into a sum-of-squares **equality** would require a
new evaluation of the residual incidence block.  Merely naming that block by
the deviations `t_y-t_x` or `(At)_x-2` inserts the desired terminal rather
than deriving it.

## Verdict

The q-generic rooted PSD route is cut in its proposed equality-case form.
The complete forced Gram block diagonalizes as (4), with eigenvalues `q-2`
and `q-1`, not zero.  All information capable of coupling different roots
lies in the unrestricted deeper incidence block.  A viable PSD successor
would need an independently proved sharp evaluation of that block; ordinary
positivity or the square-order dimension count supplies no such evaluation.
