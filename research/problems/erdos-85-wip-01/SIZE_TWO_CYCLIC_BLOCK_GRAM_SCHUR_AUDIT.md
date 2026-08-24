# Block Gram / Schur-complement audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Candidate

Let `T` be an empty difference fibre and let `A` be the incidence matrix
from its `q` cells to all cells outside `T`.  Every row has weight `q-2`.
Under the full same-fibre cap, two distinct rows have scalar product zero or
one.  Hence

```text
A A^T = (q-2) I + B,
```

where `B` is the simple owner-pair agreement graph.  The banked empty-fibre
support theorem gives `|E(B)| >= q`.  The proposed analytic route was to use
positive semidefiniteness, together with global block transpose, to prove the
opposite inequality.

## The local Gram inequality permits the extremal cycle

Positive semidefiniteness alone cannot distinguish the desired contradiction.
Take `B` to be the cycle `C_q`.  Its eigenvalues are
`2 cos(2 pi j/q)`, so

```text
(q-2) I + B >= (q-4) I.
```

It is positive semidefinite for every `q >= 4` (positive definite for the
live binary orders `q >= 8`), while `|E(B)|=q` exactly meets the forced lower
bound.  This is the spectral version of the chordless-cycle obstruction
already found in the Levi audit.

There is also a direct set-system realization with exactly the available
number of outside columns.  Use one column for each edge of `C_q`, incident
with its two endpoint rows, and give every row `q-4` additional private
columns.  There are

```text
q + q(q-4) = q(q-3)
```

columns, the number of cells outside one fibre.  Each row has weight `q-2`,
adjacent cycle rows have intersection one, and all other row intersections
are zero.  Thus even the integral Gram factorization, not merely an abstract
PSD matrix, realizes the bad endpoint.

This realization deliberately omits the second affine projection and route
reciprocity.  Sol3's directed q=8 all-cap control (`5ca21a32da`) supplies the
stronger computational version: exact row and column hits, looplessness,
the empty fibre, and all same-fibre caps remain SAT when only reciprocity is
removed.

## Global symmetry does not make the adjacency matrix PSD

Writing the full reciprocal adjacency matrix in the empty-fibre partition
gives

```text
K = [ 0   A  ]
    [ A^T D  ].
```

The equality of the off-diagonal blocks is exactly reciprocity, but `K` is an
adjacency matrix and is generally indefinite.  Therefore one cannot take a
Schur complement of `K` as a positive matrix.  Squaring does produce a PSD
matrix, but its `T,T` principal block is simply `AA^T`; this returns to the
cycle-compatible identity above and loses the signs/block labels through
which reciprocity could matter.

One may instead use the graph Laplacian `(q-2)I-K`, which is PSD because the
code is `(q-2)`-regular.  Any Schur-complement inequality obtained this way
is a generic effective-resistance inequality for a regular graph.  It uses
no consecutive-hole or cyclic-coordinate data.  In particular, the owner
cycle set system above already satisfies its necessary principal-block PSD
condition.  Such an inequality cannot by itself force `|E(B)| <= q-1`.

Shifting by a larger scalar has the same problem: for
`lambda >= ||K||`, positivity of `lambda I-K` is generic spectral
bookkeeping, and its Schur complement depends on the unresolved outside
block `D`.  Replacing `D` by a norm bound discards precisely the blockwise
transpose correlations identified by the directed/reciprocal SAT separator.

## Cut and surviving analytic target

The scalar block-Gram / uncolored Schur route is **cut**.  The facts

```text
AA^T = (q-2)I+B,  |E(B)| >= q,  K=K^T
```

do not contradict one another by positivity.  The cycle endpoint is allowed
with room to spare.

Any spectral revival must keep more than `AA^T`.  A viable matrix must be
block- or group-ring-valued so that the `t,u` entry remembers the target
difference and the affine base displacement, and transpose must act before
those colors are summed.  Equivalently, it must use the exact relations
between `A_tu` and `A_ut^T`, not merely symmetry of their concatenation.
This is the same surviving information demanded by the fully colored
integer `Sym^2` candidate.
