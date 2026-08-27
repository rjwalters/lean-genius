# NONBIP-CONNECTED flat-projector countermodel

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **all diagonal spectral-moment routes cut**.

The single-sector leverage audit leaves open the possibility that coupling
all spectral sectors through `diag(A)=0` and `diag(A^2)=q` might force the
designated dimension down to the terminal `O(sqrt(q))` scale.  It does not.

For binary `q`, the order `n=q^2` admits a Sylvester Hadamard matrix.  Normalize
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

Moreover the designated `q`-dimensional projector has constant leverage
`1/q` at every vertex.  Its dimension `m=q` violates the required terminal

```text
2(q-1)m^2 <= q^2
```

for every `q>=2`.  The executable check is

```text
python3 research/problems/erdos-85-wip-01/
  verify_nonbip_connected_flat_projector_countermodel.py
```

This is deliberately not a graph: its off-diagonal entries are not zero-one,
and it does not impose the off-diagonal common-neighbor mask in the square
identity.  That distinction is the result.  Even an actual orthogonal
projector system satisfying regularity and both forced diagonal moments
pointwise permits `m=q`; leverage-score, Schur--Horn, or any argument using
only diagonal entries of powers cannot prove the desired bound.

A viable designated-dimension successor must use an off-diagonal identity
that couples spectral sectors through the same zero-one incidence entries.
Adding more diagonal moments is not a successor: the construction makes
every `diag(B^r)` equal to the corresponding normalized global power sum.
