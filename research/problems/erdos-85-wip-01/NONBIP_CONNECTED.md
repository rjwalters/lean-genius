# NONBIP-CONNECTED `[q]`

This is the one-component child of `GAP A-REG-NONBIP`: a hypothetical
`q`-regular C4-free graph `G` on `q²` vertices whose second-order defect
graph `D` is connected and nonbipartite, for `q = 2^k`, `k >= 3`.

## Banked inputs

`Erdos85BinarySquareConnectedOwnerComplement.lean` proves:

- the unique owner graph is the complement of `D`;
- its centered Gram is `q L_D`;
- the adjacency matrix `A` is nonsingular;
- `L_D = A² - J`; and
- `det(L_D + J) = det(A)²`.

The q-generic spectral pairing in `559c798c6b` additionally says that every
nonprincipal adjacency eigenvalue `theta` pairs with defect eigenvalue
`q - 1 - theta²`.  In the connected case this is the same operator identity
viewed on the zero-sum subspace, not an extra numerical restriction.

## Spectral-only route is insufficient

For every even `q >= 4`, define a circulant graph `D_q` on `Z/(q²)` with
generator set

```text
{q²/2, +/-1, +/-2, +/-4, ..., +/-(q-4)}.
```

It has degree `q-1`, is connected because `1` is a generator, and is
nonbipartite because it also has even generators.  Its Fourier modes pair as
`j` and `q²-j`.  The corrected principal eigenvalue of `L_D + J` is `q²`;
the half-frequency eigenvalue is `4`, because exactly one paired generator
is odd.  Every other eigenvalue occurs in a paired mode.  Consequently

```text
charpoly(L(D_q) + J) = (x - q²)(x - 4) P_q(x)²
```

for an integral polynomial `P_q`.  Hence `det(L_D+J)` is a square.  By the
Matrix-Tree theorem it equals `q⁴ tau(D_q)`, so `tau(D_q)` is a rational
square; since it is an integer, it is an integer square.  Thus all of the
following necessary conditions admit connected nonbipartite countermodels
uniformly in binary `q`:

- `(q-1)`-regularity on `q²` vertices;
- positivity and connected one-dimensional Laplacian kernel;
- square corrected-Laplacian determinant;
- square spanning-tree count; and
- the even-multiplicity characteristic-polynomial pattern required by a
  formal square root, including square exceptional eigenvalues.

`q_generic_connected_defect_spectral_countermodel.py` checks the exact
integer matrices and factorization at `q=4,8` by default (`q=16` is also
supported but slower).

This does **not** construct an ambient graph `G`, so it is not a countermodel
to A-REG or to the connected stratum.  It is a loss certificate for arguments
using only the spectrum or determinant of `D`.  A viable next child must use
the entrywise/integral square-root structure of

```text
A² = L_D + J,
```

such as zero-one adjacency, diagonal zero, or eigenvector-coordinate
constraints.  Merely strengthening determinant bookkeeping cannot close
`NONBIP-CONNECTED`.
