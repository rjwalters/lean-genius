# NONBIP-CONNECTED flat-projector countermodel

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **the specified low-moment flat-projector rank argument is cut**.

The single-sector leverage audit asks whether coupling spectral sectors
through `diag(A)=0` and `diag(A^2)=q` can supply the missing dimension bound.
This construction exhibits a flat sector of dimension `q` and trace `2-q`
under those low-moment conditions. It does not instantiate a single
designated primary factor carrying the full trace `-q`.

For binary `q>=8`, the order `n=q^2` admits a Sylvester Hadamard matrix.  Normalize
its columns to an orthonormal basis, with the first column equal to
`1/sqrt(n)`.  Assign the uniform round-66 adjacency-root ledger to those
columns: principal root `q`; `q` roots `+1,-1` with imbalance `2-q`; one root
`-2`; and sign-paired roots over the two residual defect values.  That ledger
has

```text
sum lambda_i = 0,             sum lambda_i^2 = nq.
```

Every squared basis coordinate is `1/n`.  Consequently the resulting real
symmetric matrix `B=H diag(lambda) H^T` satisfies pointwise

```text
diag(B)=0,       diag(B^2)=q,       B 1=q 1.
```

Moreover the selected `q`-dimensional projector has constant leverage
`1/q` at every vertex. Its dimension `m=q` exceeds the numerical target

```text
2(q-1)m^2 <= q^2
```

The last scalar inequality holds for every `q>=2`; the spectral construction
and verifier here use binary `q>=8`.  The executable check is

```text
python3 research/problems/erdos-85-wip-01/
  verify_nonbip_connected_flat_projector_countermodel.py
```

This is deliberately not a graph: its off-diagonal entries are not zero-one,
and it does not impose the off-diagonal common-neighbor mask in the square
identity.  That distinction is the result.  Even an actual orthogonal
projector system satisfying regularity and both forced diagonal moments
pointwise permits a selected sector with `m=q`. These conditions do not
bound every such sector at the target scale. This is neither a counterexample
to a bound with the additional exact designated-trace hypothesis nor to
every additional constraint on diagonal entries of powers.

An off-diagonal identity coupling spectral sectors through the same zero-one
incidence entries is one possible successor. The construction makes every
`diag(B^r)` equal to the corresponding normalized global power sum, but this
does not make those values valid local graph-walk counts.

## Scope correction: higher local integrality is not imposed (2026-09-09)

The selected sector has one root `+1` and `q-1` roots `-1`, hence trace
`2-q`. Adding the separate `-2` root gives trace `-q` on a sector of dimension
`q+1`, but that combines two distinct defect eigenvalues. It does not supply
one primary factor with that trace. The original designated-factor language
therefore overstated the interface matched by this control.

At `q=8`, the displayed real spectral ledger gives exactly

```text
diag(B^6) = 26572127/5832 - 1675*sqrt(871)/18954.
```

Indeed, in the verifier's notation the two residual defect roots are
`left = -29/27 + 4*sqrt(871)/27` and
`right = -29/27 - 2*sqrt(871)/351`, with multiplicities 2 and 52.
Substituting these into
`(8^6 + 8 + 64 + 2*(7-left)^3 + 52*(7-right)^3)/64`
gives the value above. Since `29^2 < 871 < 30^2`, this is irrational and
cannot be a diagonal entry of a power of an integer adjacency matrix.
Thus this control does not rule out using higher local integrality.

The separate `Q1024_LOCAL_WALK_CONTROL.md` addresses all-length local
integrality for a different formal spectrum at `q=1024`; its scope and
remaining projector/entrywise-realization gaps must be assessed separately.
Neither construction establishes A-REG or a graph realization.
